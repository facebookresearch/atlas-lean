/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# EDGE-SUBGRAPH on graphs of maximum degree 4 is NP-complete

Source:
M. R. Garey and D. S. Johnson, *Computers and Intractability: A Guide to the
Theory of NP-Completeness*, W. H. Freeman (1979), problem [GT28] EDGE-SUBGRAPH, comment:
"Remains NP-complete even if `G` has no vertex with degree exceeding 4";
M. Yannakakis, "Node- and edge-deletion NP-complete problems", Proceedings of
the 10th Annual ACM Symposium on Theory of Computing (STOC 1978), 253-264,
doi:10.1145/800133.804355 (Theorem 12).
-/
module

public import Batteries.Util.ProofWanted
public import CSLibExt.Computability.Complexity.Defs
public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import Mathlib.Data.Set.Card
public import WantedExt.Complexity.NPComplete.EdgeSubgraphWanted

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.EdgeSubgraphMaxDegreeFour

/-!
# EDGE-SUBGRAPH on graphs of maximum degree 4 is NP-complete

INSTANCE: a graph `G = (V, E)` with no vertex of degree exceeding 4, and a positive integer
`K ≤ |E|`. QUESTION: is there a subset `E' ⊆ E` with `|E'| ≥ K` such that the subgraph
`G' = (V, E')` is an edge graph (line graph)?

This is the restriction of EDGE-SUBGRAPH
(`WantedExt.Complexity.NPComplete.EdgeSubgraphWanted`, Garey and Johnson [GT28]) recorded in the
[GT28] comment. Yannakakis (1978), Theorem 12: "The edge-deletion 'line invertible' graph problem
on graphs with maximum degree 4 is NP-complete"; he remarks that the bound 4 is best possible
(maximum degree 3 is polynomial). The instance, the graph, `EdgeSubgraph.WellFormed` (a simple
edge list and `0 < K ≤ |E|`) and `EdgeSubgraphFeasible` are reused unchanged; the degree bound is
added to well-formedness. The degree of `v` is the number of its neighbours,
`((Graph i).neighborSet v).ncard`.

Encoding: the instance is decoded from a bitstring with the repository's
canonical `MetaMathlibExt.BitstringEncoding`. Undecodable bitstrings, and
bitstrings decoding to malformed instances, are no-instances.

NP-completeness is stated in the same form as the proved results in
`CSLibExt.Computability.Complexity.Karp`: membership in
`MetaMathlibExt.ComplexityTheory.NP`, plus a polynomial-time many-one
reduction from every language in `NP`
(`Cslib.CookLevin.PolyManyOneRed`).
-/

open EdgeSubgraph (EdgeSubgraphInstance Graph EdgeSubgraphFeasible)

/-- Well-formedness of an instance: EDGE-SUBGRAPH well-formedness (a simple edge list and
`0 < K ≤ |E|`), and every vertex has at most 4 neighbours. -/
def WellFormed (i : EdgeSubgraphInstance) : Prop :=
  EdgeSubgraph.WellFormed i ∧ ∀ v, ((Graph i).neighborSet v).ncard ≤ 4

open Classical in
/-- EDGE-SUBGRAPH on graphs of maximum degree 4 as a decision problem over bitstrings. -/
noncomputable def edgeSubgraphMaxDegreeFourDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode (α := EdgeSubgraphInstance) x with
  | some i => decide (WellFormed i ∧ EdgeSubgraphFeasible i)
  | none => false

/-- **EDGE-SUBGRAPH is NP-complete on graphs of maximum degree 4.** Source: Garey and Johnson
(1979), [GT28], comment; Yannakakis (1978), Theorem 12. -/
public theorem_wanted edgeSubgraphMaxDegreeFour_npComplete :
    edgeSubgraphMaxDegreeFourDec ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L edgeSubgraphMaxDegreeFourDec

end MetaMathlibExt.Complexity.NPComplete.EdgeSubgraphMaxDegreeFour
