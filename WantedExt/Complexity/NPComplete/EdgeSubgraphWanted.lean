/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# EDGE-SUBGRAPH is NP-complete

Source:
M. R. Garey and D. S. Johnson, *Computers and Intractability: A Guide to the
Theory of NP-Completeness*, W. H. Freeman (1979), problem [GT28] EDGE-SUBGRAPH;
M. Yannakakis, "Node- and edge-deletion NP-complete problems", Proceedings of
the 10th Annual ACM Symposium on Theory of Computing (STOC 1978), 253-264,
doi:10.1145/800133.804355 (Theorem 12);
M. Yannakakis, "Edge-deletion problems", SIAM Journal on Computing 10 (1981),
297-309, doi:10.1137/0210021.
-/
module

public import Batteries.Util.ProofWanted
public import CSLibExt.Computability.Complexity.Defs
public import CSLibExt.Complexity.NPComplete.EdgeSubgraphDefs

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.EdgeSubgraph

/-!
# EDGE-SUBGRAPH is NP-complete

INSTANCE: a graph `G = (V, E)` and a positive integer `K ≤ |E|`. QUESTION: is there a subset
`E' ⊆ E` with `|E'| ≥ K` such that the subgraph `G' = (V', E')`, where `V'` is the set of
endpoints of edges in `E'`, is an edge graph (line graph) of some graph?

`E'` is a sublist of the edge list; under `WellFormed` the edge list has no duplicate edges in
either orientation, so the sublist's length is `|E'|` and the edge list's length is `|E|`.
`G' = (V', E')` is the spanning graph `edgeGraph n E'` induced on its support (the vertices
with a neighbour, which under `WellFormed` are exactly the endpoints of edges in `E'`). "Is the
edge graph of some graph" is the shared MathlibExt predicate
`MetaMathlibExt.SimpleGraph.IsLineGraph`: isomorphic to Mathlib's `SimpleGraph.lineGraph` of a
finite simple graph. Taking `V'` or all of `V` as the vertex set gives the same problem: an
isolated vertex of a line graph is an edge of the root graph forming its own component, so
adding or deleting isolated vertices preserves being a line graph.

Encoding: the instance is decoded from a bitstring with the repository's
canonical `MetaMathlibExt.BitstringEncoding`. Undecodable bitstrings, and
bitstrings decoding to malformed instances, are no-instances.

NP-completeness is stated in the same form as the proved results in
`CSLibExt.Computability.Complexity.Karp`: membership in
`MetaMathlibExt.ComplexityTheory.NP`, plus a polynomial-time many-one
reduction from every language in `NP`
(`Cslib.CookLevin.PolyManyOneRed`).
-/

/-- **EDGE-SUBGRAPH is NP-complete.** Source: Garey and Johnson (1979), [GT28];
Yannakakis (1978), Theorem 12; Yannakakis (1981). -/
public theorem_wanted edgeSubgraph_npComplete :
    edgeSubgraphDec ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L edgeSubgraphDec

end MetaMathlibExt.Complexity.NPComplete.EdgeSubgraph
