/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# CONNECTED EDGE-SUBGRAPH on graphs of maximum degree 3 is NP-complete

Source:
M. R. Garey and D. S. Johnson, *Computers and Intractability: A Guide to the
Theory of NP-Completeness*, W. H. Freeman (1979), problem [GT28] EDGE-SUBGRAPH, comment;
M. Yannakakis, "Node- and edge-deletion NP-complete problems", Proceedings of
the 10th Annual ACM Symposium on Theory of Computing (STOC 1978), 253-264,
doi:10.1145/800133.804355 (Theorem 12 and its Remark (2)).
-/
module

public import Batteries.Util.ProofWanted
public import CSLibExt.Computability.Complexity.Defs
public import CSLibExt.Complexity.NPComplete.ConnectedEdgeSubgraphMaxDegreeThreeDefs

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.ConnectedEdgeSubgraphMaxDegreeThree

/-!
# CONNECTED EDGE-SUBGRAPH on graphs of maximum degree 3 is NP-complete

INSTANCE: a graph `G = (V, E)` with no vertex of degree exceeding 3, and a positive integer
`K ≤ |E|`. QUESTION: is there a subset `E' ⊆ E` with `|E'| ≥ K` such that the subgraph
`G' = (V, E')` is connected and is an edge graph (line graph) of some graph?

This is the variant of EDGE-SUBGRAPH (`WantedExt.Complexity.NPComplete.EdgeSubgraphWanted`,
Garey and Johnson [GT28]) recorded in the [GT28] comment: "If we require that the subgraph be
connected, the degree bound for NP-completeness can be reduced to 3." Yannakakis (1978),
Theorem 12, proves EDGE-SUBGRAPH NP-complete on graphs of maximum degree 4, and his Remark (2)
after it reads: "If a connectivity requirement is included, then the best bound can be brought
down to 3." (Without the connectivity requirement, maximum degree 3 is polynomial: Remark (1).)

The instance type, the graph and `EdgeSubgraph.WellFormed` (a simple edge list on `Fin n` and
`0 < K ≤ |E|`) are reused from EDGE-SUBGRAPH; the degree bound is added to well-formedness, with
Mathlib's `SimpleGraph.degree`. `E'` is a sublist of the duplicate-free edge list, so its length
is `|E'|`. `G' = (V, E')` is the spanning subgraph `edgeGraph n E'` on all `n` vertices, as in
Garey and Johnson's question and in Yannakakis's edge-deletion problems, where deleting edges
keeps every vertex. It must be connected (Mathlib's `SimpleGraph.Connected`) and a line graph
(the shared MathlibExt predicate `MetaMathlibExt.SimpleGraph.IsLineGraph`: isomorphic to
Mathlib's `SimpleGraph.lineGraph` of a finite simple graph). A connected `(V, E')` has
`|V| ≤ |E'| + 1`, so yes-instances have `n ≤ |E| + 1` and the binary vertex count does not
affect membership in NP.

Encoding: the instance is decoded from a bitstring with the repository's
canonical `MetaMathlibExt.BitstringEncoding`. Undecodable bitstrings, and
bitstrings decoding to malformed instances, are no-instances.

NP-completeness is stated in the same form as the proved results in
`CSLibExt.Computability.Complexity.Karp`: membership in
`MetaMathlibExt.ComplexityTheory.NP`, plus a polynomial-time many-one
reduction from every language in `NP`
(`Cslib.CookLevin.PolyManyOneRed`).
-/

/-- **CONNECTED EDGE-SUBGRAPH is NP-complete on graphs of maximum degree 3.** Source: Garey
and Johnson (1979), [GT28], comment; Yannakakis (1978), Theorem 12, Remark (2). -/
public theorem_wanted connectedEdgeSubgraphMaxDegreeThree_npComplete :
    connectedEdgeSubgraphMaxDegreeThreeDec ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L connectedEdgeSubgraphMaxDegreeThreeDec

end MetaMathlibExt.Complexity.NPComplete.ConnectedEdgeSubgraphMaxDegreeThree
