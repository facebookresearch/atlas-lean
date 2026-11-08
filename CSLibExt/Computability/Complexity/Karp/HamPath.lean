/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.Computability.Complexity.Path
public import CSLibExt.Computability.SatTimeM
public import Mathlib.Data.List.Dedup

/-!
# Karp reductions on the canonical classes: HAMPATH

Specification module for SAT ≤ HAMPATH (Sipser, Theorem 7.46, for CNF formulas of any clause
width) on `MetaMathlibExt.ComplexityTheory`. It fixes the language and the pure reduction; the
correctness proofs (forward: assignment to path; backward: the normal-path argument), the emitter
machine and NP membership are separate components.

* Instances are PATH instances (`Path.encodeP s t n es`): a digraph on `0, …, n - 1` with `s`, `t`.
* `IsHamPath n es s t p`: `p` lists every vertex exactly once, starts at `s`, ends at `t`, and
  consecutive vertices are joined by arcs (`Path.arc`). `hamPathDec`: some Hamiltonian path exists.
* The construction `toHam φ`, with `m = φ.length` clauses and the distinct variables
  `hamVars φ = (varsOf φ).dedup` (`k` of them):
  - clause `j` is vertex `j`;
  - variable `i` has a diamond: top `hpT m i`, a row `hpR m i l` for `l ≤ 3 m` (separators at
    `l = 3 j`, the pair of clause `j` at `3 j + 1`, `3 j + 2`), and bottom `hpT m (i + 1)`, the
    next top;
  - `hpT m i` points to both row ends, both row ends point to `hpT m (i + 1)`, and row
    neighbours point to each other;
  - if variable `i` occurs positively in clause `j`: `hpR m i (3 j + 1) → j → hpR m i (3 j + 2)`;
    negatively: `hpR m i (3 j + 2) → j → hpR m i (3 j + 1)`;
  - `s = hpT m 0`, `t = hpT m k`, `n = hpT m k + 1`.

  A left-to-right row means "true". `reduceHam` is the reduction on bit strings; undecodable
  inputs go to `noHam` (two vertices, no arcs, `s = t = 0`), a no-instance.
* `DetoursNormal φ p`: every clause vertex `j` of `p` sits between the two vertices of its pair in
  one diamond row. The backward direction splits at this predicate: every Hamiltonian path of
  `toHam φ` has normal detours (Sipser's separator argument), and a Hamiltonian path with normal
  detours traverses each row in one direction and yields a satisfying assignment.
-/

@[expose] public section

namespace Cslib.Complexity.Karp

open Cslib.CookLevin Cslib.Logic.PL

/-- A Hamiltonian path from `s` to `t` in the digraph on `0, …, n - 1` with edge list `es`. -/
def IsHamPath (n : ℕ) (es : List (ℕ × ℕ)) (s t : ℕ) (p : List ℕ) : Prop :=
  p.Nodup ∧ p.length = n ∧ (∀ v ∈ p, v < n) ∧ p.head? = some s ∧ p.getLast? = some t ∧
    p.IsChain (Path.arc n es)

open Classical in
/-- HAMPATH: the digraph has a Hamiltonian path from `s` to `t`. -/
noncomputable def hamPathDec : MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  decide (∃ s t n es, Path.encodeP s t n es = x ∧ ∃ p, IsHamPath n es s t p)

/-- The distinct variables of a formula (each kept at its last occurrence). -/
def hamVars (φ : CNF) : List ℕ := (varsOf φ).dedup

/-- The top of diamond `i` (the bottom of diamond `i - 1`), for `m` clauses. -/
def hpT (m i : ℕ) : ℕ := m + i * (3 * m + 2)

/-- Row vertex `l ≤ 3 m` of diamond `i`. -/
def hpR (m i l : ℕ) : ℕ := hpT m i + 1 + l

/-- The arcs of diamond `i` for variable `x`: its frame, its row, and its clause detours. -/
def diamondEdges (φ : CNF) (i x : ℕ) : List (ℕ × ℕ) :=
  let m := φ.length
  [(hpT m i, hpR m i 0), (hpT m i, hpR m i (3 * m)), (hpR m i 0, hpT m (i + 1)),
    (hpR m i (3 * m), hpT m (i + 1))] ++
  (List.range (3 * m)).flatMap (fun l => [(hpR m i l, hpR m i (l + 1)),
    (hpR m i (l + 1), hpR m i l)]) ++
  (List.range m).flatMap fun j =>
    (if (x, true) ∈ φ.getD j [] then [(hpR m i (3 * j + 1), j), (j, hpR m i (3 * j + 2))]
      else []) ++
    (if (x, false) ∈ φ.getD j [] then [(hpR m i (3 * j + 2), j), (j, hpR m i (3 * j + 1))]
      else [])

/-- All arcs of the construction, diamond by diamond. -/
def hamEdges (φ : CNF) : List (ℕ × ℕ) :=
  (List.range (hamVars φ).length).flatMap fun i => diamondEdges φ i ((hamVars φ).getD i 0)

/-- Sipser's HAMPATH instance for `φ`. -/
def toHam (φ : CNF) : List Bool :=
  Path.encodeP (hpT φ.length 0) (hpT φ.length (hamVars φ).length)
    (hpT φ.length (hamVars φ).length + 1) (hamEdges φ)

/-- A fixed no-instance: two vertices, no arcs, `s = t = 0`. -/
def noHam : List Bool := Path.encodeP 0 0 2 []

/-- SAT ≤ HAMPATH on bit strings. -/
def reduceHam (x : List Bool) : List Bool :=
  match decodeCNF x with
  | some φ => toHam φ
  | none => noHam

/-- Every clause vertex `j` of `p` is a detour inside one diamond row: `p` contains
`a, j, b` where `{a, b}` is the pair `hpR m i (3 j + 1)`, `hpR m i (3 j + 2)` of some
diamond `i`. -/
def DetoursNormal (φ : CNF) (p : List ℕ) : Prop :=
  ∀ j < φ.length, ∃ i < (hamVars φ).length,
    [hpR φ.length i (3 * j + 1), j, hpR φ.length i (3 * j + 2)] <:+: p ∨
      [hpR φ.length i (3 * j + 2), j, hpR φ.length i (3 * j + 1)] <:+: p

/-! ### Diamond arithmetic -/

/-- Tops increase with the diamond index. -/
theorem hpT_mono {m i i' : ℕ} (h : i ≤ i') : hpT m i ≤ hpT m i' :=
  Nat.add_le_add_left (Nat.mul_le_mul_right _ h) _

/-- Row vertices of diamond `i` lie below the next top. -/
theorem hpR_lt_hpT_succ {m i l : ℕ} (hl : l ≤ 3 * m) : hpR m i l < hpT m (i + 1) := by
  unfold hpR hpT
  rw [Nat.add_one_mul i]
  omega

end Cslib.Complexity.Karp
