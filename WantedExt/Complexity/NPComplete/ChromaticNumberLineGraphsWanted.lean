/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# CHROMATIC NUMBER for line graphs is NP-complete

Source:
M. R. Garey and D. S. Johnson, *Computers and Intractability: A Guide to the
Theory of NP-Completeness*, W. H. Freeman (1979), problem [GT4] GRAPH K-COLORABILITY (CHROMATIC
NUMBER, the unrestricted problem);
I. Holyer, "The NP-completeness of edge-coloring", SIAM Journal on Computing 10(4) (1981),
718-720, doi:10.1137/0210055 (deciding whether a cubic graph has chromatic index 3 is
NP-complete);
D. S. Johnson, "The NP-completeness column: an ongoing guide", Journal of Algorithms 6 (1985),
434-451, doi:10.1016/0196-6774(85)90012-4, Table 1 (row "Edge (or line)", column CHROMATIC
NUMBER);
C. M. H. de Figueiredo, A. A. de Melo, D. Sasaki and A. Silva, "Revising Johnson's table for the
21st century", Discrete Applied Mathematics 323 (2022), 184-200,
doi:10.1016/j.dam.2021.05.021, Table 1 (row EDGE (OR LINE), column CHR NUM: "N [OG]").
-/
module

public import Batteries.Util.ProofWanted
public import CSLibExt.Computability.CookLevin
public import MathlibExt.Combinatorics.SimpleGraph.LineGraph
public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import WantedExt.Complexity.NPComplete.GraphColoringWanted

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.ChromaticNumberLineGraphs

open MetaMathlibExt.Complexity.NPComplete.GraphColoring
  (GraphColoringInstance Graph GraphColoringFeasible)

/-!
# CHROMATIC NUMBER for line graphs is NP-complete

INSTANCE: a graph `G = (V, E)` that is a line graph, and a positive integer `K ≤ |V|`. QUESTION:
is `G` `K`-colorable, i.e., does there exist a function `f : V → {1, 2, …, K}` such that
`f(u) ≠ f(v)` whenever `{u, v} ∈ E` (equivalently, is the chromatic number of `G` at most `K`)?

This is the restriction of GRAPH COLORING (`WantedExt.Complexity.NPComplete.GraphColoringWanted`,
[GT4]) to line graphs, with `K` part of the input. The instance, the graph, the parent
well-formedness condition (a simple edge list) and the question (`Colorable K`) are that
module's; the restriction and the bound `0 < K ≤ |V|` ([GT4]) are added to `WellFormed`. A line
graph is a graph isomorphic to the line graph `L(H)` of some finite simple graph `H` (vertices
the edges of `H`, adjacent when they share an endpoint): the shared MathlibExt predicate
`MetaMathlibExt.SimpleGraph.IsLineGraph`, over Mathlib's `SimpleGraph.lineGraph`, as in
`ThreeColorabilityLineGraphsWanted` (which fixes `K = 3`).

Hardness: the proper `K`-colorings of `L(H)` are exactly the proper `K`-edge-colorings of `H`,
and `L(H)` is computed from `H` in polynomial time, so Holyer's theorem (chromatic index `3` of
cubic graphs) gives NP-hardness with `K = 3`. Membership in NP holds as for GRAPH COLORING.

Encoding: the instance is decoded from a bitstring with the repository's
canonical `MetaMathlibExt.BitstringEncoding`. Undecodable bitstrings, and
bitstrings decoding to malformed instances, are no-instances.

NP-completeness is stated in the same form as the proved results in
`CSLibExt.Computability.Complexity.Karp`: membership in
`MetaMathlibExt.ComplexityTheory.NP`, plus a polynomial-time many-one
reduction from every language in `NP`
(`Cslib.CookLevin.PolyManyOneRed`).
-/

/-- Well-formedness of an instance: a well-formed GRAPH COLORING instance (simple edge list) whose
graph is a line graph, with `0 < K ≤ |V|`. -/
def WellFormed (i : GraphColoringInstance) : Prop :=
  GraphColoring.WellFormed i ∧ MetaMathlibExt.SimpleGraph.IsLineGraph (Graph i) ∧
    0 < i.2.2 ∧ i.2.2 ≤ i.1

open Classical in
/-- CHROMATIC NUMBER for line graphs as a decision problem over bitstrings. -/
noncomputable def chromaticNumberLineGraphsDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := GraphColoringInstance) x with
  | some i => decide (WellFormed i ∧ GraphColoringFeasible i)
  | none => false

/-- **CHROMATIC NUMBER is NP-complete for line graphs.** Source: Holyer (1981); Garey and Johnson
(1979), [GT4]; Johnson (1985), Table 1; de Figueiredo, de Melo, Sasaki and Silva (2022),
Table 1. -/
public theorem_wanted chromaticNumberLineGraphs_npComplete :
    chromaticNumberLineGraphsDec ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L chromaticNumberLineGraphsDec

end MetaMathlibExt.Complexity.NPComplete.ChromaticNumberLineGraphs
