/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.Algorithms.Lean.Matrix.Multiply
public import Mathlib.Data.ZMod.Basic
import Batteries.Data.Vector.Lemmas
import Mathlib.Tactic

/-!
# Freivalds' charged matrix-product trial

MIT 6.046J Spring 2015 Lecture 6, printed page 2, supplies the trial shape
and acceptance exactly when `A (B r) = C r`.

This implementation is an intentional strict GF(2) specialization: the cited lecture chooses a
random binary vector for matrices over a general coefficient domain and does not restrict `A`,
`B`, `C` or their arithmetic to `ZMod 2`, whereas here the matrices and all arithmetic are over
`ZMod 2`. The specialization loses scope (for example, integer `[1] * [1]` and `[3]` are unequal
in the source setting but become equal after reduction modulo 2).

The three products reuse the existing rectangular accumulator with one
column. Its saved `B r` is passed to the second product. Each scalar
multiplication and addition contributes one to the corresponding existing
cost component. Conversion, zero initialization, column comparison, indexing,
allocation, and random-bit acquisition are outside this arithmetic model.

Retained Lean was authored by Codex at Adam Kiezun's explicit selection.
-/

set_option autoImplicit false

namespace Cslib.Algorithms.Lean.Matrix

open Cslib.Algorithms.Lean

@[no_expose] private def seedColumn {n : Nat} (r : Fin n → ZMod 2) :
    _root_.Vector (_root_.Vector (ZMod 2) 1) n :=
  _root_.Vector.ofFn fun i => _root_.Vector.replicate 1 (r i)

@[no_expose] private def zeroColumn (n : Nat) :
    _root_.Vector (_root_.Vector (ZMod 2) 1) n :=
  _root_.Vector.replicate n (_root_.Vector.replicate 1 0)

/-- **Freivalds trial.** Given $n \times n$ matrices $A$, $B$, $C$ over
$\mathbb{F}_2 = \mathbb{Z}/2$, stored as arrays of rows, and a seed $r \in \mathbb{F}_2^n$, the
trial computes the column vectors $Br$, $A(Br)$ and $Cr$, each by accumulating matrix products
into a zero column, and returns true exactly when $A(Br) = Cr$. Its cost is the pair (number of
scalar multiplications, number of scalar additions), each multiply-add step counting one of each.

The coefficient domain is $\mathbb{F}_2$ by intentional specialization, not by a restriction in
the cited source. -/
public def freivaldsTrial {n : Nat}
    (A B C : _root_.Vector (_root_.Vector (ZMod 2) n) n)
    (r : Fin n → ZMod 2) : TimeM (Nat × Nat) Bool := do
  let column := seedColumn r
  let initial := zeroColumn n
  let br ← rectangularMatrixAccumulate B column initial
  let abr ← rectangularMatrixAccumulate A br initial
  let cr ← rectangularMatrixAccumulate C column initial
  pure (decide (abr = cr))

@[expose] public section

/-- **Cost of the Freivalds trial.** For $n \times n$ matrices $A$, $B$, $C$ over
$\mathbb{F}_2$ and every seed $r \in \mathbb{F}_2^n$, the Freivalds trial performs exactly
$3n^2$ scalar multiplications and exactly $3n^2$ scalar additions.

These counts belong to the same run that returns the acceptance bit and include the additions
into the zero-initialized accumulators. -/
theorem freivaldsTrial_time {n : Nat}
    (A B C : _root_.Vector (_root_.Vector (ZMod 2) n) n)
    (r : Fin n → ZMod 2) :
    (freivaldsTrial A B C r).time = (3 * n ^ 2, 3 * n ^ 2) := by
  apply Prod.ext <;>
    simp [freivaldsTrial, rectangularMatrixAccumulate_time, pow_two] <;> ring

/-- **Matrix of a Freivalds input.** An $n \times n$ array $A$ of rows over
$\mathbb{F}_2 = \mathbb{Z}/2$ determines the $n \times n$ matrix over $\mathbb{F}_2$ whose
$(i, j)$ entry is entry $j$ of row $i$ of $A$. -/
public def freivaldsMatrix {n : Nat}
    (A : _root_.Vector (_root_.Vector (ZMod 2) n) n) :
    _root_.Matrix (Fin n) (Fin n) (ZMod 2) :=
  _root_.Matrix.of fun i j => (A.get i).get j

private def columnEntries {n : Nat}
    (column : _root_.Vector (_root_.Vector (ZMod 2) 1) n) : Fin n → ZMod 2 :=
  fun i => (column.get i).get 0

private theorem seedColumn_entries {n : Nat} (r : Fin n → ZMod 2) :
    columnEntries (seedColumn r) = r := by
  funext i
  simp [columnEntries, seedColumn]


private theorem columnEntries_product {n : Nat}
    (A : _root_.Vector (_root_.Vector (ZMod 2) n) n)
    (column : _root_.Vector (_root_.Vector (ZMod 2) 1) n) :
    columnEntries (rectangularMatrixAccumulate A column (zeroColumn n)).ret =
      (freivaldsMatrix A).mulVec (columnEntries column) := by
  funext i
  simpa [columnEntries, zeroColumn, freivaldsMatrix,
    _root_.Matrix.mulVec_apply_eq_sum] using
    rectangularMatrixAccumulate_apply A column (zeroColumn n) i 0


private theorem column_eq_iff_entries_eq {n : Nat}
    (a b : _root_.Vector (_root_.Vector (ZMod 2) 1) n) :
    a = b ↔ columnEntries a = columnEntries b := by
  constructor
  · exact congrArg columnEntries
  · intro h
    ext i hi j hj
    have hj0 : j = 0 := by omega
    subst j
    change (a.get ⟨i, hi⟩).get 0 = (b.get ⟨i, hi⟩).get 0
    exact congrFun h ⟨i, hi⟩

/-- **Acceptance criterion of the Freivalds trial.** For $n \times n$ matrices $A$, $B$, $C$ over
$\mathbb{F}_2$ and every seed $r \in \mathbb{F}_2^n$, the Freivalds trial on $A$, $B$, $C$, $r$
returns true if and only if $A(Br) = Cr$. -/
theorem freivaldsTrial_accept_iff {n : Nat}
    (A B C : _root_.Vector (_root_.Vector (ZMod 2) n) n)
    (r : Fin n → ZMod 2) :
    (freivaldsTrial A B C r).ret = true ↔
      (freivaldsMatrix A).mulVec ((freivaldsMatrix B).mulVec r) =
        (freivaldsMatrix C).mulVec r := by
  simp only [freivaldsTrial, TimeM.ret_bind, TimeM.ret_pure]
  simp only [decide_eq_true_eq]
  rw [column_eq_iff_entries_eq]
  simp only [columnEntries_product, seedColumn_entries]


/-- **Acceptance via the product discrepancy.** For $n \times n$ matrices $A$, $B$, $C$ over
$\mathbb{F}_2$ and every seed $r \in \mathbb{F}_2^n$, the Freivalds trial on $A$, $B$, $C$, $r$
returns true if and only if $(AB - C)r = 0$. -/
theorem freivaldsTrial_accept_discrepancy_iff {n : Nat}
    (A B C : _root_.Vector (_root_.Vector (ZMod 2) n) n)
    (r : Fin n → ZMod 2) :
    (freivaldsTrial A B C r).ret = true ↔
      (freivaldsMatrix A * freivaldsMatrix B - freivaldsMatrix C).mulVec r = 0 := by
  rw [freivaldsTrial_accept_iff, _root_.Matrix.sub_mulVec,
    ← _root_.Matrix.mulVec_mulVec, sub_eq_zero]

/-- **Completeness of the Freivalds trial.** Let $A$, $B$, $C$ be $n \times n$ matrices over
$\mathbb{F}_2$ with $AB = C$. Then for every seed $r \in \mathbb{F}_2^n$ the Freivalds trial on
$A$, $B$, $C$, $r$ returns true. This includes the case $n = 0$. -/
theorem freivaldsTrial_complete {n : Nat}
    (A B C : _root_.Vector (_root_.Vector (ZMod 2) n) n)
    (h : freivaldsMatrix A * freivaldsMatrix B = freivaldsMatrix C)
    (r : Fin n → ZMod 2) :
    (freivaldsTrial A B C r).ret = true := by
  apply (freivaldsTrial_accept_discrepancy_iff A B C r).mpr
  simp [h]

/-- **Freivalds trial on empty matrices.** For $0 \times 0$ matrices $A$, $B$, $C$ over
$\mathbb{F}_2$ and the empty seed $r$, the Freivalds trial returns true at zero cost: it performs
no scalar multiplications and no scalar additions. -/
theorem freivaldsTrial_empty
    (A B C : _root_.Vector (_root_.Vector (ZMod 2) 0) 0)
    (r : Fin 0 → ZMod 2) :
    freivaldsTrial A B C r = pure true := by
  apply TimeM.ext
  · apply freivaldsTrial_complete A B C
    ext i j
    exact Fin.elim0 i
  · change (freivaldsTrial A B C r).time = (0, 0)
    simpa using freivaldsTrial_time A B C r

end

end Cslib.Algorithms.Lean.Matrix
