/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# COMPARABILITY SUBGRAPH is NP-complete

Source:
M. R. Garey and D. S. Johnson, *Computers and Intractability: A Guide to the
Theory of NP-Completeness*, W. H. Freeman (1979), problem [GT29] TRANSITIVE SUBGRAPH, comment;
M. Yannakakis, "Node- and edge-deletion NP-complete problems", Proceedings of
the 10th Annual ACM Symposium on Theory of Computing (STOC 1978), 253-264,
doi:10.1145/800133.804355 (Theorem 14);
M. Yannakakis, "Edge-deletion problems", SIAM Journal on Computing 10 (1981),
297-309, doi:10.1137/0210021.
-/
module

public import Batteries.Util.ProofWanted
public import CSLibExt.Computability.Complexity.Defs
public import CSLibExt.Complexity.NPComplete.ComparabilitySubgraphDefs

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.ComparabilitySubgraph

/-!
# COMPARABILITY SUBGRAPH is NP-complete

INSTANCE: a graph `G = (V, E)` and a positive integer `K ≤ |E|`. QUESTION: is there a subset
`E' ⊆ E` with `|E'| ≥ K` such that the subgraph `G' = (V, E')` is a comparability graph, i.e.,
can be made into a transitive digraph by directing each of its edges in one of the two possible
directions?

This is the undirected variant of TRANSITIVE SUBGRAPH recorded in the Garey-Johnson [GT29]
comment ("The variant in which `G` is undirected and we ask for a subgraph that is a
'comparability graph' ... is also NP-complete, even if `G` has no vertex with degree exceeding
3"). Yannakakis (1978), Theorem 14: "The edge-deletion 'comparability graph' problem is
NP-complete, even on cubic graphs"; the general problem stated here contains that restriction.

`E'` is a sublist of the edge list; under `WellFormed` the edge list has no duplicate edges in
either orientation, so the sublist's length is `|E'|` and the edge list's length is `|E|`.
`G' = (V, E')` is the spanning subgraph `edgeGraph n E'`. Being a comparability graph is the
shared predicate `ComparabilityGraphSandwich.IsComparabilityGraph`: some strict order `r` on the
vertices with `G'.Adj u v ↔ r u v ∨ r v u`. A strict order is asymmetric, so it directs each
edge one way, and it is transitive; conversely a transitive orientation of a loopless graph is
an irreflexive transitive relation, a strict order whose symmetric closure is the adjacency.

Encoding: the instance is decoded from a bitstring with the repository's
canonical `MetaMathlibExt.BitstringEncoding`. Undecodable bitstrings, and
bitstrings decoding to malformed instances, are no-instances.

NP-completeness is stated in the same form as the proved results in
`CSLibExt.Computability.Complexity.Karp`: membership in
`MetaMathlibExt.ComplexityTheory.NP`, plus a polynomial-time many-one
reduction from every language in `NP`
(`Cslib.CookLevin.PolyManyOneRed`).
-/

/-- **COMPARABILITY SUBGRAPH is NP-complete.** Source: Garey and Johnson (1979), [GT29],
comment; Yannakakis (1978), Theorem 14; Yannakakis (1981). -/
public theorem_wanted comparabilitySubgraph_npComplete :
    comparabilitySubgraphDec ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L comparabilitySubgraphDec

end MetaMathlibExt.Complexity.NPComplete.ComparabilitySubgraph
