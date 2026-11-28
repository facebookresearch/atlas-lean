/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected
public import Mathlib.Combinatorics.SimpleGraph.Hasse
public import Mathlib.Combinatorics.SimpleGraph.Prod

/-!
# FILLOMINO: definitions

Yato (2003, Section 3.3) states the rules of Fillomino:
* "A problem is given as a rectangular grid, with some cells filled with positive integers. The
  length of sides of the rectangle is called the size of the problem."
* "The goal is to fill each blank cell with a integer and divide the board into several blocks
  so that
  - each block consists of one or more consecutive cells (forms a polyomino),
  - all the cells in a block are filled with the same integer, which equals to the area of the
    block,
  - blocks with the same area do not share their edges."

INSTANCE: a rectangular grid, some cells filled with positive integers.
QUESTION: can every blank cell be filled with an integer, and the grid divided into blocks,
satisfying these rules?

Yato (2003, Theorem 3.8) proves that finding a solution is ASP-complete, by a reduction from a
planar version of 3SAT, and (Theorem 2.7, with `n = 0`) that the decision problem of an
ASP-complete problem is NP-complete.

Representation. The grid is given explicitly, row by row: entry `c` of row `r` is `0` when cell
`(r, c)` is blank and the given integer otherwise (given integers are positive). `WellFormed`
requires at least one row and one column and rows of equal length. Cells are `Fin m × Fin n`,
adjacent when they share a side in Mathlib's grid graph `pathGraph m □ pathGraph n`. A solution
is a filling `f` of all cells that keeps the given integers, and a division of the grid into
blocks, the classes of a labeling `block` of the cells. A block forms a polyomino when its cells
induce a connected subgraph of the grid graph. Two blocks share an edge when a cell of one is
adjacent to a cell of the other.

Encoding: the instance is decoded from a bitstring with the repository's
canonical `MetaMathlibExt.BitstringEncoding`. Undecodable bitstrings, and
bitstrings decoding to malformed instances, are no-instances.

Source:
T. Yato, "Complexity and completeness of finding another solution and its application to
puzzles", Master's thesis, University of Tokyo (2003), Section 3.3, Theorem 3.8.
-/

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.Fillomino

/-- An instance: the grid row by row, each entry `0` (blank cell) or the given integer. -/
abbrev FillominoInstance := List (List ℕ)

/-- The number of rows `m`. -/
abbrev rows (i : FillominoInstance) : ℕ := i.length

/-- The number of columns `n` (the length of the first row). -/
abbrev cols (i : FillominoInstance) : ℕ := (i.headD []).length

/-- A cell `(row, column)` of the grid. -/
abbrev Cell (i : FillominoInstance) := Fin (rows i) × Fin (cols i)

/-- The grid graph on the cells: cells sharing a side are adjacent. -/
abbrev Grid (i : FillominoInstance) : SimpleGraph (Cell i) :=
  SimpleGraph.pathGraph (rows i) □ SimpleGraph.pathGraph (cols i)

/-- The entry of cell `x`: `0` for a blank cell, otherwise the given integer. -/
def cell (i : FillominoInstance) (x : Cell i) : ℕ :=
  (i.getD x.1 []).getD x.2 0

/-- Well-formedness: at least one row and one column, and rows of equal length. -/
def WellFormed (i : FillominoInstance) : Prop :=
  0 < rows i ∧ 0 < cols i ∧ ∀ row ∈ i, row.length = cols i

/-- Some filling `f` of the cells and some division of the grid into blocks (the classes of
`block`) satisfy the rules. -/
def FillominoFeasible (i : FillominoInstance) : Prop :=
  ∃ (f : Cell i → ℕ) (block : Cell i → ℕ),
    -- the filling keeps the given integers
    (∀ x, cell i x ≠ 0 → f x = cell i x) ∧
    -- each block forms a polyomino
    (∀ x, ((Grid i).induce {y | block y = block x}).Connected) ∧
    -- the cells of a block are filled with the area of the block
    (∀ x, f x = (Finset.univ.filter fun y => block y = block x).card) ∧
    -- blocks with the same area do not share an edge
    ∀ x y, (Grid i).Adj x y → block x ≠ block y → f x ≠ f y

open Classical in
/-- FILLOMINO as a decision problem over bitstrings. -/
noncomputable def fillominoDec : MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode (α := FillominoInstance) x with
  | some i => decide (WellFormed i ∧ FillominoFeasible i)
  | none => false

end MetaMathlibExt.Complexity.NPComplete.Fillomino
