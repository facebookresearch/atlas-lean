/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# FILLOMINO: definitions

Source:
T. Yato, "Complexity and completeness of finding another solution and its application to
puzzles", Master's thesis, University of Tokyo (2003), Section 3.3, Theorem 3.8.
-/
module

public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected
public import Mathlib.Combinatorics.SimpleGraph.Hasse
public import Mathlib.Combinatorics.SimpleGraph.Prod

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
