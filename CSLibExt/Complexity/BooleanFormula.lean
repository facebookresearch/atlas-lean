/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Data.Fin.Basic
import Mathlib.Tactic.Ring

/-!
# Boolean formulas: substitution, depth and size

`BooleanFormula n` is the formula (tree) model of Boolean computation over `n` inputs: leaves are
inputs or constants, internal nodes are AND, OR and NOT gates. Subformulas are never shared, so
`BooleanFormula.subst` copies the formula substituted for an input at every occurrence of that
input. This is formula substitution, not composition of circuits with shared gates; for the
latter, see `Cslib.Circuits.Circuit.comp` in `Cslib.Computability.Circuit.Composition`.

## Main results

* `Cslib.Complexity.BooleanFormula.eval_subst`: a substituted formula evaluates as the outer
  formula on the values of the substituted formulas.
* `Cslib.Complexity.BooleanFormula.depth_subst_le`: if every substituted formula has depth at
  most `D`, substitution adds at most `D` to the depth.
* `Cslib.Complexity.BooleanFormula.size_subst_le_tight`: if every substituted formula has size at
  most `D`, then `(g.subst wiring).size ≤ g.size * (D + 1) + D`, that is,
  `g.size + (g.size + 1) * D`: the gates of `g`, plus at most `g.size + 1` leaves, each replaced
  by at most `D` gates.
* `Cslib.Complexity.BooleanFormula.size_subst_le`: the weaker bound
  `g.size * (D + 1) + (D + 1)`.
-/

@[expose] public section

namespace Cslib.Complexity

/-- Boolean formulas over `n` inputs, as trees: leaves are inputs or constants, internal nodes
are gates. Subformulas are not shared. -/
inductive BooleanFormula (n : ℕ)
  | input (i : Fin n) : BooleanFormula n
  | const (b : Bool) : BooleanFormula n
  | and (g h : BooleanFormula n) : BooleanFormula n
  | or (g h : BooleanFormula n) : BooleanFormula n
  | not (g : BooleanFormula n) : BooleanFormula n

/-- Evaluation of a formula on an input assignment. -/
def BooleanFormula.eval {n : ℕ} (σ : Fin n → Bool) : BooleanFormula n → Bool
  | .input i => σ i
  | .const b => b
  | .and g h => g.eval σ && h.eval σ
  | .or g h => g.eval σ || h.eval σ
  | .not g => !g.eval σ

/-- Size: number of gates (internal nodes). -/
def BooleanFormula.size {n : ℕ} : BooleanFormula n → ℕ
  | .input _ => 0
  | .const _ => 0
  | .and g h => g.size + h.size + 1
  | .or g h => g.size + h.size + 1
  | .not g => g.size + 1

/-- Depth: longest path from a leaf to the root. -/
def BooleanFormula.depth {n : ℕ} : BooleanFormula n → ℕ
  | .input _ => 0
  | .const _ => 0
  | .and g h => max g.depth h.depth + 1
  | .or g h => max g.depth h.depth + 1
  | .not g => g.depth + 1

/-- Substitution: replace each input `i` of the outer formula by a formula `wiring i` over `m`
inputs. Every occurrence of input `i` gets its own copy of `wiring i`. -/
def BooleanFormula.subst {n m : ℕ} (wiring : Fin n → BooleanFormula m) :
    BooleanFormula n → BooleanFormula m
  | .input i => wiring i
  | .const b => .const b
  | .and g h => .and (g.subst wiring) (h.subst wiring)
  | .or g h => .or (g.subst wiring) (h.subst wiring)
  | .not g => .not (g.subst wiring)

/-- Substitution evaluates pointwise: evaluating `g.subst wiring` is evaluating `g` on the values
of the substituted formulas. -/
theorem BooleanFormula.eval_subst {n m : ℕ} (wiring : Fin n → BooleanFormula m)
    (g : BooleanFormula n) (τ : Fin m → Bool) :
    (g.subst wiring).eval τ = g.eval (fun i => (wiring i).eval τ) := by
  induction g with
  | input i => rfl
  | const b => rfl
  | and g h ihg ihh => simp [BooleanFormula.subst, BooleanFormula.eval, ihg, ihh]
  | or g h ihg ihh => simp [BooleanFormula.subst, BooleanFormula.eval, ihg, ihh]
  | not g ih => simp [BooleanFormula.subst, BooleanFormula.eval, ih]

/-- Depth of a substitution is at most the depth of the outer formula plus the maximal depth `D`
of the substituted formulas: substitution adds depth, it does not multiply it. -/
theorem BooleanFormula.depth_subst_le {n m : ℕ} (wiring : Fin n → BooleanFormula m)
    (g : BooleanFormula n) (D : ℕ) (hD : ∀ i, (wiring i).depth ≤ D) :
    (g.subst wiring).depth ≤ g.depth + D := by
  induction g with
  | input i =>
    simp only [BooleanFormula.subst, BooleanFormula.depth, Nat.zero_add]
    exact hD i
  | const b =>
    simp only [BooleanFormula.subst, BooleanFormula.depth, Nat.zero_add]
    exact Nat.zero_le D
  | and g h ihg ihh =>
    simp only [BooleanFormula.subst, BooleanFormula.depth]
    omega
  | or g h ihg ihh =>
    simp only [BooleanFormula.subst, BooleanFormula.depth]
    omega
  | not g ih =>
    simp only [BooleanFormula.subst, BooleanFormula.depth]
    omega

/-- Size of a substitution, tight form: if every substituted formula has at most `D` gates, then
`(g.subst wiring).size ≤ g.size * (D + 1) + D = g.size + (g.size + 1) * D`. The gates of `g`
remain, and `g` has at most `g.size + 1` leaves, each replaced by at most `D` gates. -/
theorem BooleanFormula.size_subst_le_tight {n m : ℕ} (wiring : Fin n → BooleanFormula m)
    (g : BooleanFormula n) (D : ℕ) (hD : ∀ i, (wiring i).size ≤ D) :
    (g.subst wiring).size ≤ g.size * (D + 1) + D := by
  induction g with
  | input i =>
    simp only [BooleanFormula.subst, BooleanFormula.size, Nat.zero_mul, Nat.zero_add]
    exact hD i
  | const b =>
    simp only [BooleanFormula.subst, BooleanFormula.size, Nat.zero_mul, Nat.zero_add]
    exact Nat.zero_le D
  | and g h ihg ihh =>
    simp only [BooleanFormula.subst, BooleanFormula.size]
    have h1 : (g.subst wiring).size + (h.subst wiring).size + 1
        ≤ (g.size * (D + 1) + D) + (h.size * (D + 1) + D) + 1 :=
      Nat.add_le_add_right (Nat.add_le_add ihg ihh) 1
    have e : (g.size * (D + 1) + D) + (h.size * (D + 1) + D) + 1
        = (g.size + h.size + 1) * (D + 1) + D := by ring
    rw [e] at h1
    exact h1
  | or g h ihg ihh =>
    simp only [BooleanFormula.subst, BooleanFormula.size]
    have h1 : (g.subst wiring).size + (h.subst wiring).size + 1
        ≤ (g.size * (D + 1) + D) + (h.size * (D + 1) + D) + 1 :=
      Nat.add_le_add_right (Nat.add_le_add ihg ihh) 1
    have e : (g.size * (D + 1) + D) + (h.size * (D + 1) + D) + 1
        = (g.size + h.size + 1) * (D + 1) + D := by ring
    rw [e] at h1
    exact h1
  | not g ih =>
    simp only [BooleanFormula.subst, BooleanFormula.size]
    have h1 : (g.subst wiring).size + 1 ≤ (g.size * (D + 1) + D) + 1 :=
      Nat.add_le_add_right ih 1
    have hdist : (g.size + 1) * (D + 1) = g.size * (D + 1) + (D + 1) := by ring
    have e : (g.size * (D + 1) + D) + 1 ≤ (g.size + 1) * (D + 1) + D := by
      omega
    exact h1.trans e

/-- Size of a substitution, weaker form: if every substituted formula has at most `D` gates,
then `(g.subst wiring).size ≤ g.size * (D + 1) + (D + 1)`, one more than
`BooleanFormula.size_subst_le_tight`. -/
theorem BooleanFormula.size_subst_le {n m : ℕ} (wiring : Fin n → BooleanFormula m)
    (g : BooleanFormula n) (D : ℕ) (hD : ∀ i, (wiring i).size ≤ D) :
    (g.subst wiring).size ≤ g.size * (D + 1) + (D + 1) := by
  have h := BooleanFormula.size_subst_le_tight wiring g D hD
  have hle : g.size * (D + 1) + D ≤ g.size * (D + 1) + (D + 1) :=
    Nat.add_le_add_left (Nat.le_succ D) _
  exact h.trans hle

end Cslib.Complexity
