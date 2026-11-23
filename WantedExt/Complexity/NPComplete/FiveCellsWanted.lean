/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# FIVE CELLS is NP-complete

Source:
C. Iwamoto and T. Ide, "Five Cells and Tilepaint are NP-complete", IEICE Transactions on
Information and Systems E105-D(3) (2022), 508-516, doi:10.1587/transinf.2021FCP0001.
-/
module

public import Batteries.Util.ProofWanted
public import CSLibExt.Computability.CookLevin
public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected
public import Mathlib.Combinatorics.SimpleGraph.Hasse
public import Mathlib.Combinatorics.SimpleGraph.Prod

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.FiveCells

/-!
# FIVE CELLS is NP-complete

INSTANCE: a rectangular grid of cells whose number of cells is a multiple of five, some of whose
cells contain numbers.
QUESTION: can the grid be divided into blocks of five cells (each block a connected region
enclosed by lines) so that every number equals the number of lines of a block around its cell,
counting the lines of the outer frame?

The grid is given explicitly, row by row: a list of `m` rows of `n` cells each, a cell holding
`0` (no number) or `k + 1` (the number `k`). Its cells are `Fin m × Fin n`, and two cells are
adjacent when they share a side, i.e. in Mathlib's grid graph `pathGraph m □ pathGraph n`
(`Grid`). A division into blocks is a labelling `block` of the cells; the blocks are the label
classes, each of exactly five cells and connected in the grid graph. Each of the four sides of a
cell `x` is either on the outer frame or shared with a neighbor `y`, and it is a line of a block
exactly when it is on the frame or `y` is in another block. So the number of lines around `x` is
`4` minus the number of neighbors of `x` in its own block.

Encoding: the instance is decoded from a bitstring with the repository's
canonical `MetaMathlibExt.BitstringEncoding`. Undecodable bitstrings, and
bitstrings decoding to malformed instances, are no-instances.

NP-completeness is stated in the same form as the proved results in
`CSLibExt.Computability.Complexity.Karp`: membership in
`MetaMathlibExt.ComplexityTheory.NP`, plus a polynomial-time many-one
reduction from every language in `NP`
(`Cslib.CookLevin.PolyManyOneRed`).
-/

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

/-- **FIVE CELLS is NP-complete.** Source: Iwamoto and Ide (2022). -/
public theorem_wanted fiveCells_npComplete :
    fiveCellsDec ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L fiveCellsDec

end MetaMathlibExt.Complexity.NPComplete.FiveCells
