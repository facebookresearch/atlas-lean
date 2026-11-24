/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# 3-COLORABILITY OF LINE GRAPHS is NP-complete

Source:
I. Holyer, "The NP-completeness of edge-coloring", SIAM Journal on Computing 10(4) (1981),
718-720, doi:10.1137/0210055 (deciding whether a cubic graph has chromatic index 3 is
NP-complete; a proper 3-edge-coloring of `H` is a proper 3-coloring of its line graph);
M. R. Garey and D. S. Johnson, *Computers and Intractability: A Guide to the
Theory of NP-Completeness*, W. H. Freeman (1979), problem [GT4] GRAPH K-COLORABILITY (the parent
problem), and [OPEN5] CHROMATIC INDEX;
ISGCI, *Information System on Graph Classes and their Inclusions*, class "line" (gc_249),
problem 3-Colourability: NP-complete, with the reference to Holyer (1981).
-/
module

public import Batteries.Util.ProofWanted
public import CSLibExt.Computability.Complexity.Defs
public import MathlibExt.Combinatorics.SimpleGraph.LineGraph
public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import WantedExt.Complexity.NPComplete.GraphColoringWanted

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.ThreeColorabilityLineGraphs

open GraphColoring (GraphColoringInstance Graph GraphColoringFeasible)

/-!
# 3-COLORABILITY OF LINE GRAPHS is NP-complete

INSTANCE: a finite simple undirected graph `G = (V, E)` that is a line graph. QUESTION: is `G`
properly 3-colorable, i.e., is there a map `c : V → {1, 2, 3}` with `c(u) ≠ c(v)` for every edge
`uv`?

This is GRAPH COLORING (`GraphColoringWanted`, [GT4]) with the bound fixed to `K = 3`, restricted
to line graphs. A line graph is a graph isomorphic to the line graph `L(H)` of some finite simple
graph `H`: the vertices of `L(H)` are the edges of `H`, two of them adjacent when they share an
endpoint. This is the shared MathlibExt predicate `MetaMathlibExt.SimpleGraph.IsLineGraph`, over
Mathlib's `SimpleGraph.lineGraph` and graph isomorphisms `≃g`. Holyer proves that deciding
whether a cubic graph `H` has a proper 3-edge-coloring is NP-complete; the proper 3-edge-colorings
of `H` are exactly the proper 3-colorings of `L(H)`, which is computed from `H` in polynomial time,
so 3-colorability is NP-hard already on line graphs of cubic graphs. Membership in NP holds for
all graphs.

The instance type is a vertex count and an edge list; `withThreeColors` pairs it with the bound
`3` to reuse GRAPH COLORING's graph (`Graph`, a simple graph on `Fin n`), well-formedness
(simple edge list) and question (`Colorable 3`), as in `ThreeColorabilityDiameterThreeWanted`.

Encoding: the instance is decoded from a bitstring with the repository's
canonical `MetaMathlibExt.BitstringEncoding`. Undecodable bitstrings, and
bitstrings decoding to malformed instances, are no-instances.

NP-completeness is stated in the same form as the proved results in
`CSLibExt.Computability.Complexity.Karp`: membership in
`MetaMathlibExt.ComplexityTheory.NP`, plus a polynomial-time many-one
reduction from every language in `NP`
(`Cslib.CookLevin.PolyManyOneRed`).
-/

/-- An instance: vertex count `n` (vertices `0, …, n - 1`) and edge list. -/
abbrev ThreeColorabilityLineGraphsInstance := ℕ × List (ℕ × ℕ)

/-- The GRAPH COLORING instance with the same graph and bound `K = 3`. -/
abbrev withThreeColors (i : ThreeColorabilityLineGraphsInstance) : GraphColoringInstance :=
  (i.1, i.2, 3)

/-- Well-formedness of an instance: the edge list describes a simple graph on `Fin n` (GRAPH
COLORING's well-formedness), and the graph is a line graph. -/
def WellFormed (i : ThreeColorabilityLineGraphsInstance) : Prop :=
  GraphColoring.WellFormed (withThreeColors i) ∧
    MetaMathlibExt.SimpleGraph.IsLineGraph (Graph (withThreeColors i))

/-- The graph is properly 3-colorable. -/
def ThreeColorabilityLineGraphsFeasible (i : ThreeColorabilityLineGraphsInstance) : Prop :=
  GraphColoringFeasible (withThreeColors i)

open Classical in
/-- 3-COLORABILITY OF LINE GRAPHS as a decision problem over bitstrings. -/
noncomputable def threeColorabilityLineGraphsDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := ThreeColorabilityLineGraphsInstance) x with
  | some i => decide (WellFormed i ∧ ThreeColorabilityLineGraphsFeasible i)
  | none => false

/-- **3-COLORABILITY OF LINE GRAPHS is NP-complete.** Source: Holyer (1981); Garey and Johnson
(1979), [GT4] (parent problem); ISGCI, class "line". -/
public theorem_wanted threeColorabilityLineGraphs_npComplete :
    threeColorabilityLineGraphsDec ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L threeColorabilityLineGraphsDec

end MetaMathlibExt.Complexity.NPComplete.ThreeColorabilityLineGraphs
