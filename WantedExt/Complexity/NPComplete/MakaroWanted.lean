/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# MAKARO is NP-complete

Source:
C. Iwamoto, M. Haruishi and T. Ibusuki, "Computational complexity of Herugolf and Makaro",
IEICE Transactions on Fundamentals of Electronics, Communications and Computer Sciences
E102-A(9) (2019), 1118-1125, doi:10.1587/transfun.E102.A.1118; conference version:
"Herugolf and Makaro are NP-complete", 9th International Conference on Fun with Algorithms
(FUN 2018), LIPIcs 100 (2018), 24:1-24:11, doi:10.4230/LIPIcs.FUN.2018.24.
-/
module

public import Batteries.Util.ProofWanted
public import CSLibExt.Computability.CookLevin
public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import WantedExt.Complexity.NPComplete.DosunFuwariWanted

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.Makaro

open DosunFuwari (DosunFuwariInstance label grid)

/-!
# MAKARO is NP-complete

Makaro is played on a rectangular grid of cells. Some cells are colored black and contain an
arrow, and the remaining cells are divided into rooms surrounded by bold lines. All white cells
are filled with numbers so that:
1. each room contains all the natural numbers up to the number of cells in it, starting from 1;
2. every arrow in a black cell points at the biggest number among the numbers in the adjacent
   cells;
3. a number is not next to the same number in another room.

INSTANCE: a rectangular grid of black cells with arrows and rooms.
QUESTION: can the white cells be filled with numbers so that rules 1-3 hold?

Rule 1 says that the numbers of a room with `s` cells are `1, …, s`, each once. In rule 2 the
arrow points at an orthogonally adjacent white cell whose number is bigger than the number of
every other white cell adjacent to the black cell; adjacent means sharing a side. The biggest
number is strict, as in the source's Fig. 2(b), where an arrow between two 2-cell rooms forces
`2` at the cell it points at and `1` at the other neighbor. An arrow pointing off the grid or at
a black cell cannot be satisfied.

The grid of black cells and rooms is a `DosunFuwari.DosunFuwariInstance`, the same board as in
`DosunFuwariWanted`: the rows, top to bottom, where entry `0` is a black cell and an entry
`k ≥ 1` is a cell of room `k`; `DosunFuwari.WellFormed` requires at least one row and one
column, rows of equal length, and every room connected (a room is a region surrounded by bold
lines). The second component gives, row by row, the direction of the arrow of each black cell
(`0` up, `1` right, `2` down, `3` left), and `0` for every room cell (no ignored payload).

Encoding: the instance is decoded from a bitstring with the repository's
canonical `MetaMathlibExt.BitstringEncoding`. Undecodable bitstrings, and
bitstrings decoding to malformed instances, are no-instances.

NP-completeness is stated in the same form as the proved results in
`CSLibExt.Computability.Complexity.Karp`: membership in
`MetaMathlibExt.ComplexityTheory.NP`, plus a polynomial-time many-one
reduction from every language in `NP`
(`Cslib.CookLevin.PolyManyOneRed`).
-/

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

/-- The number of cells of the room containing `p`. -/
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

/-- **MAKARO is NP-complete.** Source: Iwamoto, Haruishi and Ibusuki (2019). -/
public theorem_wanted makaro_npComplete :
    makaroDec ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L makaroDec

end MetaMathlibExt.Complexity.NPComplete.Makaro
