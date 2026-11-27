/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# WITNESS PUZZLES WITH EDGE HEXAGONS are NP-complete

Source:
Z. Abel, J. Bosboom, M. Coulombe, E. D. Demaine, L. Hamilton, A. Hesterberg, J. Kopinsky,
J. Lynch, M. Rudoy and C. Thielen, "Who witnesses The Witness? Finding witnesses in The Witness
is hard and sometimes impossible", Theoretical Computer Science 839 (2020), 41-102,
doi:10.1016/j.tcs.2020.05.031, Theorem 3.4.
-/
module

public import Batteries.Util.ProofWanted
public import CSLibExt.Computability.Complexity.Defs
public import Mathlib.Combinatorics.SimpleGraph.Hasse
public import Mathlib.Combinatorics.SimpleGraph.Paths
public import Mathlib.Combinatorics.SimpleGraph.Prod
public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.WitnessEdgeHexagons

/-!
# WITNESS PUZZLES WITH EDGE HEXAGONS are NP-complete

INSTANCE: a full rectangular grid of `x × y` cells, one or more start circles at its vertices,
one or more end caps at vertices on its boundary, and hexagon clues on some of its edges.
QUESTION: is there a simple path in the grid from a start circle to an end cap that includes
every edge carrying a hexagon?

Abel et al. (Section 1): "Single-panel puzzles in The Witness ... consist of an `x × y` full
rectangular grid; one or more start circles (drawn as a large dot); one or more end caps (drawn
as half-edges leaving the rectangle boundary); and zero or more clues ... each drawn on a vertex,
edge, or cell of the rectangular grid. ... The goal of the puzzle is to find a simple path that
starts at one of the start circles, ends at one of the end caps, and satisfies all the
constraints imposed by the clues." Table 2: a hexagon drawn on an edge means "The solution path
must include this edge." Theorem 3.4: "It is NP-complete to solve Witness puzzles containing
only hexagons on edges (and no broken edges)."

Representation. The grid of `x × y` cells (`x, y ≥ 1`) has the vertices `Fin (y + 1) ×
Fin (x + 1)` (`(row, column)`), adjacent when orthogonally neighboring (the box product of two
path graphs, as in `WantedExt.Complexity.NPComplete.EntryExitWanted`). A path ending at an end
cap ends at the boundary vertex the cap leaves from; the path is a path of the grid graph
(`SimpleGraph.Walk.IsPath`), so it visits no vertex twice. The instance gives, explicitly, a
mark for every vertex (`y + 1` rows of `x + 1` entries: `1` start circle, `2` end cap, `3`
both, `0` neither), a hexagon flag for every horizontal edge (`y + 1` rows of `x` flags, flag
`c` of row `r` for the edge from `(r, c)` to `(r, c + 1)`), and one for every vertical edge
(`y` rows of `x + 1` flags, flag `c` of row `r` for the edge from `(r, c)` to `(r + 1, c)`).

Encoding: the instance is decoded from a bitstring with the repository's
canonical `MetaMathlibExt.BitstringEncoding`. Undecodable bitstrings, and
bitstrings decoding to malformed instances, are no-instances.

NP-completeness is stated in the same form as the proved results in
`CSLibExt.Computability.Complexity.Karp`: membership in
`MetaMathlibExt.ComplexityTheory.NP`, plus a polynomial-time many-one
reduction from every language in `NP`
(`Cslib.CookLevin.PolyManyOneRed`).
-/

/-- An instance: the vertex marks (row by row), the horizontal-edge hexagon flags and the
vertical-edge hexagon flags. -/
abbrev WitnessEdgeHexagonsInstance := List (List ℕ) × List (List Bool) × List (List Bool)

/-- The number `y + 1` of vertex rows. -/
def rows (i : WitnessEdgeHexagonsInstance) : ℕ := i.1.length

/-- The number `x + 1` of vertex columns (the length of the first row of marks). -/
def cols (i : WitnessEdgeHexagonsInstance) : ℕ := (i.1.headD []).length

/-- A vertex `(row, column)` of the grid. -/
abbrev Vertex (i : WitnessEdgeHexagonsInstance) := Fin (rows i) × Fin (cols i)

/-- Orthogonal adjacency of vertices: the grid graph, the box product of two path graphs. -/
abbrev gridGraph (i : WitnessEdgeHexagonsInstance) : SimpleGraph (Vertex i) :=
  SimpleGraph.pathGraph (rows i) □ SimpleGraph.pathGraph (cols i)

/-- The mark of vertex `(r, c)`. -/
def mark (i : WitnessEdgeHexagonsInstance) (r c : ℕ) : ℕ := (i.1.getD r []).getD c 0

/-- Vertex `v` holds a start circle. -/
def IsStart (i : WitnessEdgeHexagonsInstance) (v : Vertex i) : Prop :=
  mark i v.1 v.2 = 1 ∨ mark i v.1 v.2 = 3

/-- An end cap leaves the grid at vertex `v`. -/
def IsEnd (i : WitnessEdgeHexagonsInstance) (v : Vertex i) : Prop :=
  mark i v.1 v.2 = 2 ∨ mark i v.1 v.2 = 3

/-- The edge from `u` to `v` carries a hexagon: `v` is right of `u` and the horizontal flag of
`u` is set, or `v` is below `u` and the vertical flag of `u` is set. -/
def HasHexagon (i : WitnessEdgeHexagonsInstance) (u v : Vertex i) : Prop :=
  ((u.1 : ℕ) = v.1 ∧ (u.2 : ℕ) + 1 = v.2 ∧ (i.2.1.getD u.1 []).getD u.2 false = true) ∨
    ((u.2 : ℕ) = v.2 ∧ (u.1 : ℕ) + 1 = v.1 ∧ (i.2.2.getD u.1 []).getD u.2 false = true)

/-- Well-formedness: `x, y ≥ 1`; `y + 1` rows of `x + 1` marks, each at most `3`, with end caps
only on the boundary; `y + 1` rows of `x` horizontal flags and `y` rows of `x + 1` vertical
flags; at least one start circle and at least one end cap. -/
def WellFormed (i : WitnessEdgeHexagonsInstance) : Prop :=
  2 ≤ rows i ∧ 2 ≤ cols i ∧ (∀ row ∈ i.1, row.length = cols i ∧ ∀ e ∈ row, e ≤ 3) ∧
    i.2.1.length = rows i ∧ (∀ row ∈ i.2.1, row.length = cols i - 1) ∧
    i.2.2.length = rows i - 1 ∧ (∀ row ∈ i.2.2, row.length = cols i) ∧
    (∀ v : Vertex i, IsEnd i v →
      (v.1 : ℕ) = 0 ∨ (v.1 : ℕ) + 1 = rows i ∨ (v.2 : ℕ) = 0 ∨ (v.2 : ℕ) + 1 = cols i) ∧
    (∃ v, IsStart i v) ∧ ∃ v, IsEnd i v

/-- The puzzle has a solution: a path of the grid from a start circle to an end cap containing
every edge that carries a hexagon. -/
def WitnessEdgeHexagonsFeasible (i : WitnessEdgeHexagonsInstance) : Prop :=
  ∃ s t : Vertex i, IsStart i s ∧ IsEnd i t ∧ ∃ p : (gridGraph i).Walk s t, p.IsPath ∧
    ∀ u v : Vertex i, HasHexagon i u v → s(u, v) ∈ p.edges

open Classical in
/-- WITNESS PUZZLES WITH EDGE HEXAGONS as a decision problem over bitstrings. -/
noncomputable def witnessEdgeHexagonsDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode (α := WitnessEdgeHexagonsInstance) x with
  | some i => decide (WellFormed i ∧ WitnessEdgeHexagonsFeasible i)
  | none => false

/-- **WITNESS PUZZLES WITH EDGE HEXAGONS are NP-complete.** Source: Abel et al. (2020),
Theorem 3.4. -/
public theorem_wanted witnessEdgeHexagons_npComplete :
    witnessEdgeHexagonsDec ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L witnessEdgeHexagonsDec

end MetaMathlibExt.Complexity.NPComplete.WitnessEdgeHexagons
