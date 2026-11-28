/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# PLANAR SUBGRAPH is NP-complete

Source:
M. R. Garey and D. S. Johnson, *Computers and Intractability: A Guide to the
Theory of NP-Completeness*, W. H. Freeman (1979), problem [GT27] PLANAR SUBGRAPH;
P. C. Liu and R. C. Geldmacher, "On the deletion of nonplanar edges of a graph",
Proceedings of the 10th Southeastern Conference on Combinatorics, Graph Theory,
and Computing (Boca Raton, 1979), Congressus Numerantium 23-24 (1979), 727-738;
M. Yannakakis, "Node- and edge-deletion NP-complete problems", Proceedings of
the 10th Annual ACM Symposium on Theory of Computing (STOC 1978), 253-264,
doi:10.1145/800133.804355 (Theorem 11).
-/
module

public import Batteries.Util.ProofWanted
public import CSLibExt.Computability.Complexity.Defs
public import CSLibExt.Complexity.NPComplete.PlanarSubgraphDefs

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.PlanarSubgraph

/-!
# PLANAR SUBGRAPH is NP-complete

INSTANCE: a graph `G = (V, E)` and a positive integer `K ≤ |E|`. QUESTION: is there a subset
`E' ⊆ E` with `|E'| ≥ K` such that `G' = (V, E')` is planar?

`E'` is a sublist of the edge list; under `WellFormed` the edge list has no duplicate edges in
either orientation, so the sublist's length is `|E'|` and the edge list's length is `|E|`.
`G' = (V, E')` is the spanning subgraph `edgeGraph n E'` on all `n` vertices. Planarity is the
shared MathlibExt predicate `SimpleGraph.IsPlanar` (a crossing-free straight-line drawing); by
Fáry's theorem this is planarity for finite simple graphs.

Encoding: the instance is decoded from a bitstring with the repository's
canonical `MetaMathlibExt.BitstringEncoding`. Undecodable bitstrings, and
bitstrings decoding to malformed instances, are no-instances.

NP-completeness is stated in the same form as the proved results in
`CSLibExt.Computability.Complexity.Karp`: membership in
`MetaMathlibExt.ComplexityTheory.NP`, plus a polynomial-time many-one
reduction from every language in `NP`
(`Cslib.CookLevin.PolyManyOneRed`).
-/

/-- **PLANAR SUBGRAPH is NP-complete.** Source: Garey and Johnson (1979), [GT27];
Liu and Geldmacher (1979); Yannakakis (1978), Theorem 11. -/
public theorem_wanted planarSubgraph_npComplete :
    planarSubgraphDec ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L planarSubgraphDec

end MetaMathlibExt.Complexity.NPComplete.PlanarSubgraph
