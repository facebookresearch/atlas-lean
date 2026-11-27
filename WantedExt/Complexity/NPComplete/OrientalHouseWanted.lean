/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# ORIENTAL HOUSE is NP-complete

Source:
H. Tang, "On the NP-Completeness of Satisfying Certain Path and Loop Puzzles",
arXiv:2004.12849 (2020), Section 1.3 (rules) and Section 3.4.
-/
module

public import Batteries.Util.ProofWanted
public import CSLibExt.Computability.Complexity.Defs
public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import Mathlib.Combinatorics.SimpleGraph.Hamiltonian
public import Mathlib.Combinatorics.SimpleGraph.Hasse
public import Mathlib.Combinatorics.SimpleGraph.Prod

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.OrientalHouse

/-!
# ORIENTAL HOUSE is NP-complete

Tang (2020), Section 1.3: in Oriental House the player is given a rectangular grid divided into
regions, including two one-cell regions labelled with `S` for Start and `F` for Finish. The aim
is to draw a directed orthogonal path from `S` to `F` passing through every cell exactly once.
Some orthogonal arrows have been given in some cells: if the path passes over an arrow on a
particular visit to a region, either it entered the region in that direction or will exit the
region in that direction on this visit.

INSTANCE: a rectangular grid divided into regions, with one-cell regions `S` and `F` and
orthogonal arrows in some cells.
QUESTION: is there a directed orthogonal path from `S` to `F` through every cell exactly once
satisfying the arrow rule? (Tang proves this NP-complete, Sections 2 and 3.4.)

The instance is `(S, F, grid)`: the cells `S` and `F` as `(row, column)`, and the grid row by
row, entry `j` of row `k` being `(region, arrow)` for the cell in row `k` and column `j`, with
arrow `0` (none), `1` (up), `2` (down), `3` (left) or `4` (right); row `0` is the top row.
Regions are the classes of cells with equal region index. `WellFormed` requires `m, n ≥ 1`,
rows of equal length, arrows at most `4`, `S` and `F` distinct cells of the grid, and the regions
of `S` and of `F` to contain no other cell. Tang's rules do not require regions to be
connected, and neither does this statement.

Cells are `Fin m × Fin n`, orthogonally adjacent when adjacent in Mathlib's grid graph
`pathGraph m □ pathGraph n`. The path is a walk from `S` to `F` visiting every cell exactly once
(`SimpleGraph.Walk.IsHamiltonian`); its cells in order are its support `q`. A visit to a region
is a maximal run `q[a], …, q[b]` of consecutive cells of the path in that region: the path
entered the region by the move `q[a - 1] → q[a]` (when `a > 0`) and exits it on this visit by
the move `q[b] → q[b + 1]` (when `q[b]` is not the last cell). The arrow rule asks, for each
cell `q[t]` with an arrow, that the visit containing position `t` entered or exits in the
direction of the arrow.

Encoding: the instance is decoded from a bitstring with the repository's
canonical `MetaMathlibExt.BitstringEncoding`. Undecodable bitstrings, and
bitstrings decoding to malformed instances, are no-instances.

NP-completeness is stated in the same form as the proved results in
`CSLibExt.Computability.Complexity.Karp`: membership in
`MetaMathlibExt.ComplexityTheory.NP`, plus a polynomial-time many-one
reduction from every language in `NP`
(`Cslib.CookLevin.PolyManyOneRed`).
-/

/-- An instance: the cells `S` and `F` as `(row, column)`, and the grid row by row, each cell
`(region, arrow)` with arrow `0` (none), `1` (up), `2` (down), `3` (left) or `4` (right). -/
abbrev OrientalHouseInstance := (ℕ × ℕ) × (ℕ × ℕ) × List (List (ℕ × ℕ))

/-- The number of rows. -/
def rows (i : OrientalHouseInstance) : ℕ := i.2.2.length

/-- The number of columns (the length of the first row). -/
def cols (i : OrientalHouseInstance) : ℕ := (i.2.2.headD []).length

/-- The cells of the grid. -/
abbrev Cell (i : OrientalHouseInstance) := Fin (rows i) × Fin (cols i)

/-- The entry `(region, arrow)` of cell `x`. -/
def entry (i : OrientalHouseInstance) (x : Cell i) : ℕ × ℕ :=
  (i.2.2.getD x.1 []).getD x.2 (0, 0)

/-- The coordinates `(row, column)` of cell `x`. -/
def coords {i : OrientalHouseInstance} (x : Cell i) : ℕ × ℕ := ((x.1 : ℕ), (x.2 : ℕ))

/-- The grid graph on the cells: cells sharing a side are adjacent. -/
abbrev Grid (i : OrientalHouseInstance) : SimpleGraph (Cell i) :=
  SimpleGraph.pathGraph (rows i) □ SimpleGraph.pathGraph (cols i)

/-- Well-formedness: at least one row and one column, rows of equal length, arrows at most `4`,
`S` and `F` distinct cells of the grid, and the regions of `S` and of `F` contain no other
cell. -/
def WellFormed (i : OrientalHouseInstance) : Prop :=
  0 < rows i ∧ 0 < cols i ∧ (∀ row ∈ i.2.2, row.length = cols i) ∧
    (∀ row ∈ i.2.2, ∀ e ∈ row, e.2 ≤ 4) ∧
    i.1.1 < rows i ∧ i.1.2 < cols i ∧ i.2.1.1 < rows i ∧ i.2.1.2 < cols i ∧ i.1 ≠ i.2.1 ∧
    ∀ x y : Cell i, (entry i x).1 = (entry i y).1 →
      (coords x = i.1 → coords y = i.1) ∧ (coords x = i.2.1 → coords y = i.2.1)

/-- The move from cell `y` to the adjacent cell `z` goes in the direction of arrow `d`. -/
def MovesInDirection {i : OrientalHouseInstance} (y z : Cell i) (d : ℕ) : Prop :=
  (d = 1 ∧ (z.1 : ℕ) + 1 = y.1 ∧ z.2 = y.2) ∨ (d = 2 ∧ (y.1 : ℕ) + 1 = z.1 ∧ z.2 = y.2) ∨
    (d = 3 ∧ z.1 = y.1 ∧ (z.2 : ℕ) + 1 = y.2) ∨ (d = 4 ∧ z.1 = y.1 ∧ (y.2 : ℕ) + 1 = z.2)

/-- The move from position `j` to position `j'` of the cell sequence `q` goes in the direction
of arrow `d`. -/
def StepInDirection {i : OrientalHouseInstance} (q : List (Cell i)) (j j' d : ℕ) : Prop :=
  ∃ y z, q[j]? = some y ∧ q[j']? = some z ∧ MovesInDirection y z d

/-- The cell sequence `q` of a path satisfies the arrow rule: for each position `t` holding a
cell with an arrow, the visit `q[a], …, q[b]` to its region that contains `t` (a maximal run of
cells in that region) entered the region in the direction of the arrow or exits it in that
direction. -/
def ArrowRule (i : OrientalHouseInstance) (q : List (Cell i)) : Prop :=
  ∀ t x, q[t]? = some x → (entry i x).2 ≠ 0 →
    ∃ a b, a ≤ t ∧ t ≤ b ∧ b < q.length ∧
      (∀ j, a ≤ j → j ≤ b → (q[j]?).map (fun y => (entry i y).1) = some (entry i x).1) ∧
      (a = 0 ∨ (q[a - 1]?).map (fun y => (entry i y).1) ≠ some (entry i x).1) ∧
      (q[b + 1]?).map (fun y => (entry i y).1) ≠ some (entry i x).1 ∧
      ((0 < a ∧ StepInDirection q (a - 1) a (entry i x).2) ∨
        StepInDirection q b (b + 1) (entry i x).2)

/-- Some path from `S` to `F` through every cell exactly once satisfies the arrow rule. -/
def OrientalHouseFeasible (i : OrientalHouseInstance) : Prop :=
  ∃ s f : Cell i, coords s = i.1 ∧ coords f = i.2.1 ∧
    ∃ c : (Grid i).Walk s f, c.IsHamiltonian ∧ ArrowRule i c.support

open Classical in
/-- ORIENTAL HOUSE as a decision problem over bitstrings. -/
noncomputable def orientalHouseDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := OrientalHouseInstance) x with
  | some i => decide (WellFormed i ∧ OrientalHouseFeasible i)
  | none => false

/-- **ORIENTAL HOUSE is NP-complete.** Source: Tang (2020), Section 3.4. -/
public theorem_wanted orientalHouse_npComplete :
    orientalHouseDec ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L orientalHouseDec

end MetaMathlibExt.Complexity.NPComplete.OrientalHouse
