/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# CONNECTED OUTERPLANAR SUBGRAPH is NP-complete

Source:
M. R. Garey and D. S. Johnson, *Computers and Intractability: A Guide to the
Theory of NP-Completeness*, W. H. Freeman (1979), problem [GT27] PLANAR SUBGRAPH, comment:
"The related problem in which we ask if `G` contains a connected "outerplanar" subgraph with
`K` or more edges is also NP-complete";
M. Yannakakis, "Node- and edge-deletion NP-complete problems", Proceedings of
the 10th Annual ACM Symposium on Theory of Computing (STOC 1978), 253-264,
doi:10.1145/800133.804355 (Theorem 10 and the closing remark of Section 4).
-/
module

public import Batteries.Util.ProofWanted
public import CSLibExt.Computability.Complexity.Defs
public import CSLibExt.Complexity.NPComplete.ConnectedOuterplanarSubgraphDefs

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.ConnectedOuterplanarSubgraph

open MathlibExt.GraphTheory.BookThicknessOfSubdivisionsWanted (HasBookEmbedding)

/-!
# CONNECTED OUTERPLANAR SUBGRAPH is NP-complete

INSTANCE: a graph `G = (V, E)` and a positive integer `K ≤ |E|`. QUESTION: does `G` contain a
connected outerplanar subgraph with `K` or more edges?

Garey and Johnson record this in the [GT27] comment, crediting [Yannakakis, 1978b]. Yannakakis
(1978) proves "The edge-deletion "outerplanar" problem is NP-complete" (Theorem 10, by a
reduction from HAMILTONIAN PATH that takes "two copies of the original graph and two new nodes
that we connect to all the nodes of the original graphs", a connected graph) and closes Section 4
with "for all the above properties the edge deletion problem remains NP-complete if we include a
connectivity requirement". It is in NP: the subgraph's edges are a certificate, and
outerplanarity is testable in polynomial time.

A subgraph with `K ≥ 1` edges that is connected has no isolated vertex, so it is determined by
its edge set `E'`: it is `(V', E')` with `V'` the set of endpoints of edges in `E'`. `E'` is a
sublist of the edge list (under `WellFormed`, no duplicate edges in either orientation, so its
length is `|E'|`), and `(V', E')` is `edgeGraph n E'` induced on its support (the vertices with a
neighbour), as in `EdgeSubgraphWanted`. "Connected" is Mathlib's `SimpleGraph.Connected`.
Outerplanarity is book thickness at most `1`, which Bernhart and Kainen ("The book thickness of
a graph", J. Combin. Theory Ser. B 27 (1979), 320-331, doi:10.1016/0095-8956(79)90021-2) prove
equivalent to it, stated with the repository's predicate `HasBookEmbedding G 1` (from
`WantedExt.GraphTheory.BookThicknessOfSubdivisionsWanted`), as in
`SubgraphIsomorphismOuterplanarWanted`: an injective placement of the vertices on a spine with
no two edges whose endpoints alternate `v ≺ x ≺ w ≺ y`.

Encoding: the instance is decoded from a bitstring with the repository's
canonical `MetaMathlibExt.BitstringEncoding`. Undecodable bitstrings, and
bitstrings decoding to malformed instances, are no-instances.

NP-completeness is stated in the same form as the proved results in
`CSLibExt.Computability.Complexity.Karp`: membership in
`MetaMathlibExt.ComplexityTheory.NP`, plus a polynomial-time many-one
reduction from every language in `NP`
(`Cslib.CookLevin.PolyManyOneRed`).
-/

/-- **CONNECTED OUTERPLANAR SUBGRAPH is NP-complete.** Source: Garey and Johnson (1979), [GT27],
comment; Yannakakis (1978), Theorem 10. -/
public theorem_wanted connectedOuterplanarSubgraph_npComplete :
    connectedOuterplanarSubgraphDec ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L connectedOuterplanarSubgraphDec

end MetaMathlibExt.Complexity.NPComplete.ConnectedOuterplanarSubgraph
