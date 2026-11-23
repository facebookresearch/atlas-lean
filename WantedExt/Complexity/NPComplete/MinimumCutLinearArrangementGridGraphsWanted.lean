/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# MINIMUM CUT LINEAR ARRANGEMENT for grid graphs is NP-complete

Source:
J. Díaz, M. D. Penrose, J. Petit and M. Serna, "Linear orderings of random geometric graphs
(extended abstract)", in *Graph-Theoretic Concepts in Computer Science (WG '99)*, Lecture Notes
in Computer Science 1665 (1999), 291-302, doi:10.1007/3-540-46784-X_28, Theorem 1 ("Bandwidth,
MinCut and VertSep remain NP-complete even when restricted to grid graphs"); full version:
"Approximating layout problems on random geometric graphs", Journal of Algorithms 39(1) (2001),
78-116, doi:10.1006/jagm.2000.1149;
M. R. Garey and D. S. Johnson, *Computers and Intractability: A Guide to the Theory of
NP-Completeness*, W. H. Freeman (1979), problem [GT44] MINIMUM CUT LINEAR ARRANGEMENT.
-/
module

public import Batteries.Util.ProofWanted
public import CSLibExt.Computability.CookLevin
public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import WantedExt.Complexity.NPComplete.GridGraphHamiltonianCircuitWanted
public import WantedExt.Complexity.NPComplete.MinimumCutLinearArrangementWanted

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.MinimumCutLinearArrangementGridGraphs

open MetaMathlibExt.Complexity.NPComplete.GridGraphHamiltonianCircuit
  (GridGraphHamiltonianCircuitInstance gridEdges)

/-!
# MINIMUM CUT LINEAR ARRANGEMENT for grid graphs is NP-complete

INSTANCE: a grid graph `G = (V, E)`, that is, a finite node-induced subgraph of the infinite grid
(the graph on the points of the plane with integer coordinates in which two points are adjacent
when their distance is `1`), and a positive integer `K`.
QUESTION: is there a one-to-one function `f : V → {1, 2, …, |V|}` such that for all `i`,
`1 ≤ i < |V|`, `|{{u, v} ∈ E : f(u) ≤ i < f(v)}| ≤ K`? (This is the cutwidth problem, `MinCut`
in Díaz, Penrose, Petit and Serna.)

This is the restriction of MINIMUM CUT LINEAR ARRANGEMENT ([GT44],
`MinimumCutLinearArrangementWanted`) to grid graphs. The grid graph is given by its finite
vertex set `V ⊆ ℤ²`, exactly as in `GridGraphHamiltonianCircuitWanted` and
`DominatingSetGridGraphsWanted`, whose definitions are reused: the points are listed without
repetition (`GridGraphHamiltonianCircuit.WellFormed`), an integer coordinate is a pair `(a, b)` of
naturals standing for `a - b`, vertex `u` is the `u`-th point, and the edges are
`GridGraphHamiltonianCircuit.gridEdges`, the pairs `u < v` whose points are adjacent in
MathlibExt's infinite grid `StatMech.Lattice.hypercubicLattice 2` (one list entry per edge). The
question is the parent's `MinimumCutLinearArrangement.MinimumCutLinearArrangementFeasible` on the
instance with `|V|` vertices, the grid edges and the bound `K`
(`toMinimumCutLinearArrangementInstance`), and `WellFormed` adds the parent's `0 < K`.

Encoding: the instance is decoded from a bitstring with the repository's
canonical `MetaMathlibExt.BitstringEncoding`. Undecodable bitstrings, and
bitstrings decoding to malformed instances, are no-instances.

NP-completeness is stated in the same form as the proved results in
`CSLibExt.Computability.Complexity.Karp`: membership in
`MetaMathlibExt.ComplexityTheory.NP`, plus a polynomial-time many-one
reduction from every language in `NP`
(`Cslib.CookLevin.PolyManyOneRed`).
-/

/-- An instance: the points of the grid graph and the bound `K`. -/
abbrev MinimumCutLinearArrangementGridGraphsInstance := GridGraphHamiltonianCircuitInstance × ℕ

/-- The grid graph and the bound as a MINIMUM CUT LINEAR ARRANGEMENT instance: `|V|` vertices,
the grid edges, and `K`. -/
def toMinimumCutLinearArrangementInstance (i : MinimumCutLinearArrangementGridGraphsInstance) :
    MinimumCutLinearArrangement.MinimumCutLinearArrangementInstance :=
  (i.1.length, gridEdges i.1, i.2)

/-- Well-formedness of an instance: the listed points are pairwise distinct (`V` is a set), and
`0 < K`. -/
def WellFormed (i : MinimumCutLinearArrangementGridGraphsInstance) : Prop :=
  GridGraphHamiltonianCircuit.WellFormed i.1 ∧ 0 < i.2

open Classical in
/-- MINIMUM CUT LINEAR ARRANGEMENT for grid graphs as a decision problem over bitstrings. -/
noncomputable def minimumCutLinearArrangementGridGraphsDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := MinimumCutLinearArrangementGridGraphsInstance) x with
  | some i =>
    decide (WellFormed i ∧ MinimumCutLinearArrangement.MinimumCutLinearArrangementFeasible
      (toMinimumCutLinearArrangementInstance i))
  | none => false

/-- **MINIMUM CUT LINEAR ARRANGEMENT for grid graphs is NP-complete.** Source: Díaz, Penrose,
Petit and Serna (1999), Theorem 1; Garey and Johnson (1979), [GT44]. -/
public theorem_wanted minimumCutLinearArrangementGridGraphs_npComplete :
    minimumCutLinearArrangementGridGraphsDec ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L minimumCutLinearArrangementGridGraphsDec

end MetaMathlibExt.Complexity.NPComplete.MinimumCutLinearArrangementGridGraphs
