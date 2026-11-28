/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# FIVE CELLS: definitions

Source:
C. Iwamoto and T. Ide, "Five Cells and Tilepaint are NP-complete", IEICE Transactions on
Information and Systems E105-D(3) (2022), 508-516, doi:10.1587/transinf.2021FCP0001.
-/
module

public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected
public import Mathlib.Combinatorics.SimpleGraph.Hasse
public import Mathlib.Combinatorics.SimpleGraph.Prod

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.FiveCells

/-- An instance: the grid row by row; each cell is `0` (no number) or `k + 1` (the number `k`).
-/
abbrev FiveCellsInstance := List (List ℕ)

/-- The number of rows `m`. -/
abbrev rows (i : FiveCellsInstance) : ℕ := i.length

/-- The number of columns `n` (the length of the first row). -/
abbrev cols (i : FiveCellsInstance) : ℕ := (i.headD []).length

/-- The grid graph of the instance: cells `(r, c)`, adjacent when they share a side. -/
abbrev Grid (i : FiveCellsInstance) : SimpleGraph (Fin (rows i) × Fin (cols i)) :=
  SimpleGraph.pathGraph (rows i) □ SimpleGraph.pathGraph (cols i)

/-- The content of cell `(r, c)`: `0` for no number, `k + 1` for the number `k`. -/
def cell (i : FiveCellsInstance) (x : Fin (rows i) × Fin (cols i)) : ℕ :=
  (i.getD x.1 []).getD x.2 0

/-- Well-formedness of an instance: the grid has at least one row and one column, all rows have
the same length `n` (the grid is rectangular), and the number of cells `m n` is a multiple of
five. -/
def WellFormed (i : FiveCellsInstance) : Prop :=
  0 < rows i ∧ 0 < cols i ∧ (∀ row ∈ i, row.length = cols i) ∧ (rows i * cols i) % 5 = 0

open Classical in
/-- The grid can be divided into connected blocks of five cells (the classes of `block`) so that
every cell `x` with a number `k` satisfies: `x` has `4 - k` neighbors in its own block, i.e. `k`
lines of blocks (including the outer frame) around it. -/
def FiveCellsFeasible (i : FiveCellsInstance) : Prop :=
  ∃ block : Fin (rows i) × Fin (cols i) → ℕ,
    (∀ x, (Finset.univ.filter fun y => block y = block x).card = 5) ∧
    (∀ x, ((Grid i).induce {y | block y = block x}).Connected) ∧
    ∀ x, cell i x ≠ 0 →
      (Finset.univ.filter fun y => (Grid i).Adj x y ∧ block y = block x).card + (cell i x - 1) = 4

open Classical in
/-- FIVE CELLS as a decision problem over bitstrings. -/
noncomputable def fiveCellsDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := FiveCellsInstance) x with
  | some i => decide (WellFormed i ∧ FiveCellsFeasible i)
  | none => false

end MetaMathlibExt.Complexity.NPComplete.FiveCells
