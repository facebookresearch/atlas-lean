/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# REMEMBERED LENGTH is NP-complete

Source:
P. Eua-anant, P. Apinyanon, T. Jirachaisri, N. Ruangsuksriwong and S. Ruangwises,
"NP-Completeness Proofs of All or Nothing, Water Walk, and Remembered Length Using the
T-Metacell Framework", arXiv:2510.21938 (2025), Section 2.3;
puzzle rules: puzz.link, "Remembered Length", https://puzz.link/rules.html?remlen.
-/
module

public import Batteries.Util.ProofWanted
public import CSLibExt.Computability.Complexity.Defs
public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected
public import Mathlib.Combinatorics.SimpleGraph.Hasse
public import Mathlib.Combinatorics.SimpleGraph.Paths
public import Mathlib.Combinatorics.SimpleGraph.Prod

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.RememberedLength

/-!
# REMEMBERED LENGTH is NP-complete

Remembered Length (Palmer Mebane) is played on a rectangular grid divided into polyominoes
called regions, with some cells shaded and some regions labeled with a positive integer. The
goal is to draw a non-crossing directed loop passing through orthogonally adjacent cells such
that (Eua-anant et al. 2025, Section 2.3):
1. the loop passes through all unshaded cells;
2. each time the loop exits a region containing a number, its section in the next region
   consists of exactly that number of cells.
puzz.link's rules add that the loop cannot branch off or cross itself, and that rule 2 applies
again each time the loop passes through the same region.

INSTANCE: a rectangular grid divided into regions, some cells shaded, some regions numbered.
QUESTION: is there a directed loop satisfying rules 1 and 2?

The loop never enters a shaded cell: Eua-anant et al. obtain the shaded version from
Hamiltonian cycles in grid graphs by shading the vertices that are not in the graph.

The instance lists the region numbers (entry `k` for region `k`, `0` for an unnumbered region)
and the grid row by row: entry `c` of row `r` is `(region, shaded)` for cell `(r, c)`. The
regions are `0, …, R - 1` with `R` the length of the number list. `WellFormed` requires at least
one row and one column, rows of equal length, region indices below `R`, and every region a
nonempty connected set of cells (a polyomino).

Cells are `Fin m × Fin n`, adjacent when they share a side in Mathlib's grid graph
`pathGraph m □ pathGraph n`. The loop is a cycle `c` of the grid graph
(`SimpleGraph.Walk.IsCycle`), traversed in the direction of the walk; its cells are exactly the
unshaded cells. Write `L` for the length of `c` and `c_j` for its `j`-th cell, indices taken mod
`L`. Rule 2: whenever `c_j` and `c_{j+1}` lie in different regions and the region of `c_j` has
number `k > 0`, the cells `c_{j+1}, …, c_{j+k}` lie in the region of `c_{j+1}` and `c_{j+k+1}`
does not.

Encoding: the instance is decoded from a bitstring with the repository's
canonical `MetaMathlibExt.BitstringEncoding`. Undecodable bitstrings, and
bitstrings decoding to malformed instances, are no-instances.

NP-completeness is stated in the same form as the proved results in
`CSLibExt.Computability.Complexity.Karp`: membership in
`MetaMathlibExt.ComplexityTheory.NP`, plus a polynomial-time many-one
reduction from every language in `NP`
(`Cslib.CookLevin.PolyManyOneRed`).
-/

/-- An instance: the region numbers (`0` = unnumbered), and the grid row by row, each cell
`(region, shaded)`. -/
abbrev RememberedLengthInstance := List ℕ × List (List (ℕ × Bool))

/-- The number of rows. -/
def rows (i : RememberedLengthInstance) : ℕ := i.2.length

/-- The number of columns (the length of the first row). -/
def cols (i : RememberedLengthInstance) : ℕ := (i.2.headD []).length

/-- The entry `(region, shaded)` of cell `x`. -/
def cell (i : RememberedLengthInstance) (x : Fin (rows i) × Fin (cols i)) : ℕ × Bool :=
  (i.2.getD x.1 []).getD x.2 (0, false)

/-- The number of region `k` (`0` = unnumbered). -/
def number (i : RememberedLengthInstance) (k : ℕ) : ℕ := i.1.getD k 0

/-- The grid graph on the cells: cells sharing a side are adjacent. -/
abbrev Grid (i : RememberedLengthInstance) : SimpleGraph (Fin (rows i) × Fin (cols i)) :=
  SimpleGraph.pathGraph (rows i) □ SimpleGraph.pathGraph (cols i)

/-- Well-formedness: at least one row and one column, rows of equal length, region indices
below `R`, and every region a nonempty connected set of cells. -/
def WellFormed (i : RememberedLengthInstance) : Prop :=
  0 < rows i ∧ 0 < cols i ∧ (∀ row ∈ i.2, row.length = cols i) ∧
    (∀ row ∈ i.2, ∀ e ∈ row, e.1 < i.1.length) ∧
    ∀ k < i.1.length, ((Grid i).induce {x | (cell i x).1 = k}).Connected

/-- The cycle `c` satisfies the rules: its cells are exactly the unshaded cells, and each time
it moves from a region numbered `k > 0` into another region, its next `k` cells, and not the
one after them, lie in that other region. -/
def Solves (i : RememberedLengthInstance) {u : Fin (rows i) × Fin (cols i)}
    (c : (Grid i).Walk u u) : Prop :=
  (∀ x, x ∈ c.support ↔ (cell i x).2 = false) ∧
  ∀ j < c.length, (cell i (c.getVert j)).1 ≠ (cell i (c.getVert (j + 1))).1 →
    0 < number i (cell i (c.getVert j)).1 →
      (∀ t, 1 ≤ t → t ≤ number i (cell i (c.getVert j)).1 →
        (cell i (c.getVert ((j + t) % c.length))).1 = (cell i (c.getVert (j + 1))).1) ∧
      (cell i (c.getVert ((j + number i (cell i (c.getVert j)).1 + 1) % c.length))).1 ≠
        (cell i (c.getVert (j + 1))).1

/-- Some cycle of the grid graph satisfies the rules. -/
def RememberedLengthFeasible (i : RememberedLengthInstance) : Prop :=
  ∃ u, ∃ c : (Grid i).Walk u u, c.IsCycle ∧ Solves i c

open Classical in
/-- REMEMBERED LENGTH as a decision problem over bitstrings. -/
noncomputable def rememberedLengthDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := RememberedLengthInstance) x with
  | some i => decide (WellFormed i ∧ RememberedLengthFeasible i)
  | none => false

/-- **REMEMBERED LENGTH is NP-complete.** Source: Eua-anant, Apinyanon, Jirachaisri,
Ruangsuksriwong and Ruangwises (2025). -/
public theorem_wanted rememberedLength_npComplete :
    rememberedLengthDec ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L rememberedLengthDec

end MetaMathlibExt.Complexity.NPComplete.RememberedLength
