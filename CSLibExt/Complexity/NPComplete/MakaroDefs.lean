/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# MAKARO: definitions

Source:
C. Iwamoto, M. Haruishi and T. Ibusuki, "Computational complexity of Herugolf and Makaro",
IEICE Transactions on Fundamentals of Electronics, Communications and Computer Sciences
E102-A(9) (2019), 1118-1125, doi:10.1587/transfun.E102.A.1118; conference version:
"Herugolf and Makaro are NP-complete", 9th International Conference on Fun with Algorithms
(FUN 2018), LIPIcs 100 (2018), 24:1-24:11, doi:10.4230/LIPIcs.FUN.2018.24.
-/
module

public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import CSLibExt.Complexity.NPComplete.DosunFuwariDefs

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.Makaro

open DosunFuwari (DosunFuwariInstance label grid)

/-- An instance: the grid of black cells (`0`) and rooms (`k ≥ 1`), and the grid of arrow
directions (`0` up, `1` right, `2` down, `3` left) of black cells, `0` at room cells. -/
abbrev MakaroInstance := DosunFuwariInstance × List (List ℕ)

/-- The cells of the grid. -/
abbrev Cell (i : MakaroInstance) := Fin (DosunFuwari.rows i.1) × Fin (DosunFuwari.cols i.1)

/-- The arrow direction of the cell `p` (`0` up, `1` right, `2` down, `3` left). -/
def arrow (i : MakaroInstance) (p : Cell i) : ℕ :=
  (i.2.getD p.1 []).getD p.2 0

/-- Well-formedness of an instance: the board is well formed as in `DosunFuwariWanted`, the
arrow grid has the same shape with every direction below `4`, and room cells carry `0`. -/
def WellFormed (i : MakaroInstance) : Prop :=
  DosunFuwari.WellFormed i.1 ∧ i.2.length = DosunFuwari.rows i.1 ∧
    (∀ row ∈ i.2, row.length = DosunFuwari.cols i.1) ∧ (∀ row ∈ i.2, ∀ d ∈ row, d < 4) ∧
    ∀ p : Cell i, label i.1 p ≠ 0 → arrow i p = 0

/-- An arrow with direction `d` in the cell `p` points at the cell `q`: `q` is the neighbor of
`p` above, to the right, below, or to the left, for `d = 0, 1, 2, 3`. -/
def PointsAt {h w : ℕ} (d : ℕ) (p q : Fin h × Fin w) : Prop :=
  (d = 0 ∧ q.2 = p.2 ∧ (q.1 : ℕ) + 1 = p.1) ∨
  (d = 1 ∧ q.1 = p.1 ∧ (p.2 : ℕ) + 1 = q.2) ∨
  (d = 2 ∧ q.2 = p.2 ∧ (p.1 : ℕ) + 1 = q.1) ∨
  (d = 3 ∧ q.1 = p.1 ∧ (q.2 : ℕ) + 1 = p.2)

/-- The number of cells of the board with the same label as `p`. For a cell with a nonzero
label this is the size of its room; for a black cell (label `0`) it counts all black cells. -/
def roomSize (i : MakaroInstance) (p : Cell i) : ℕ :=
  (Finset.univ.filter fun q => label i.1 q = label i.1 p).card

/-- The numbers `f` of the white cells satisfy the rules: the numbers of a room with `s` cells
are distinct and lie in `1, …, s`; every arrow points at an adjacent white cell whose number is
bigger than the numbers of the other adjacent white cells; and adjacent white cells of different
rooms hold different numbers. -/
def Solves (i : MakaroInstance) (f : Cell i → ℕ) : Prop :=
  (∀ p, label i.1 p ≠ 0 → 1 ≤ f p ∧ f p ≤ roomSize i p) ∧
  (∀ p q, label i.1 p ≠ 0 → label i.1 q = label i.1 p → p ≠ q → f p ≠ f q) ∧
  (∀ p, label i.1 p = 0 → ∃ q, PointsAt (arrow i p) p q ∧ label i.1 q ≠ 0 ∧
    ∀ r, (grid _ _).Adj p r → r ≠ q → label i.1 r ≠ 0 → f r < f q) ∧
  ∀ p q, (grid _ _).Adj p q → label i.1 p ≠ 0 → label i.1 q ≠ 0 →
    label i.1 p ≠ label i.1 q → f p ≠ f q

/-- Some filling of the white cells satisfies the rules. -/
def MakaroFeasible (i : MakaroInstance) : Prop :=
  ∃ f : Cell i → ℕ, Solves i f

open Classical in
/-- MAKARO as a decision problem over bitstrings. -/
noncomputable def makaroDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := MakaroInstance) x with
  | some i => decide (WellFormed i ∧ MakaroFeasible i)
  | none => false

end MetaMathlibExt.Complexity.NPComplete.Makaro
