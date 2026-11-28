/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# KURODOKO (KUROMASU): definitions

Source:
J. Kölker, "Kurodoko is NP-complete", Journal of Information Processing 20(3) (2012),
694-706, doi:10.2197/ipsjjip.20.694 (Section 1, Theorems 2 and 3).
-/
module

public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected
public import Mathlib.Combinatorics.SimpleGraph.Hasse
public import Mathlib.Combinatorics.SimpleGraph.Prod

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.Kurodoko

/-- An instance `(w, h, clues)`: the width `w`, the height `h` (both in binary), and the
clues, each a square `(r, c)` with its value `N(r, c)`. -/
abbrev KurodokoInstance := ℕ × ℕ × List ((ℕ × ℕ) × ℕ)

/-- The grid graph: squares `(r, c)` with `r < h`, `c < w`, adjacent when horizontally or
vertically adjacent. -/
def Grid (i : KurodokoInstance) : SimpleGraph (Fin i.2.1 × Fin i.1) :=
  SimpleGraph.pathGraph i.2.1 □ SimpleGraph.pathGraph i.1

/-- Square `u` is visible from square `v` given the black squares `B`: they share a row or a
column, and every square on the segment from `v` to `u` (both ends included) is white. -/
def Visible {h w : ℕ} (B : Finset (Fin h × Fin w)) (v u : Fin h × Fin w) : Prop :=
  (u.1 = v.1 ∧ ∀ c : Fin w, min v.2 u.2 ≤ c → c ≤ max v.2 u.2 → (v.1, c) ∉ B) ∨
    (u.2 = v.2 ∧ ∀ r : Fin h, min v.1 u.1 ≤ r → r ≤ max v.1 u.1 → (r, v.2) ∉ B)

instance {h w : ℕ} (B : Finset (Fin h × Fin w)) (v : Fin h × Fin w) :
    DecidablePred (Visible B v) := fun _ => by
  unfold Visible; infer_instance

/-- Well-formedness of an instance `(w, h, clues)`: `w, h ≥ 1`, the clue squares are distinct
squares of the grid, and each clue value lies in `{1, …, w + h - 1}`. -/
def WellFormed (i : KurodokoInstance) : Prop :=
  0 < i.1 ∧ 0 < i.2.1 ∧ (i.2.2.map Prod.fst).Nodup ∧
    ∀ q ∈ i.2.2, q.1.1 < i.2.1 ∧ q.1.2 < i.1 ∧ 1 ≤ q.2 ∧ q.2 ≤ i.1 + i.2.1 - 1

/-- Some set `B` of black squares satisfies rules 1-4. -/
def KurodokoFeasible (i : KurodokoInstance) : Prop :=
  ∃ B : Finset (Fin i.2.1 × Fin i.1),
    (∀ q ∈ i.2.2, ∀ v : Fin i.2.1 × Fin i.1, ((v.1 : ℕ), (v.2 : ℕ)) = q.1 → v ∉ B) ∧
    (∀ a ∈ B, ∀ b ∈ B, ¬ (Grid i).Adj a b) ∧
    ((Grid i).induce {v | v ∉ B}).Preconnected ∧
    ∀ q ∈ i.2.2, ∀ v : Fin i.2.1 × Fin i.1, ((v.1 : ℕ), (v.2 : ℕ)) = q.1 →
      (Finset.univ.filter (Visible B v)).card = q.2

open Classical in
/-- KURODOKO as a decision problem over bitstrings. -/
noncomputable def kurodokoDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := KurodokoInstance) x with
  | some i => decide (WellFormed i ∧ KurodokoFeasible i)
  | none => false

end MetaMathlibExt.Complexity.NPComplete.Kurodoko
