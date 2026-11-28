/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# SHORTEST TOTAL PATH LENGTH SPANNING TREE is NP-complete

Source:
M. R. Garey and D. S. Johnson, *Computers and Intractability: A Guide to the
Theory of NP-Completeness*, W. H. Freeman (1979), problem [ND3] SHORTEST TOTAL
PATH LENGTH SPANNING TREE;
D. S. Johnson, J. K. Lenstra, and A. H. G. Rinnooy Kan, "The complexity of the
network design problem", Networks 8 (1978), 279-285, doi:10.1002/net.3230080402.
-/
module

public import Batteries.Util.ProofWanted
public import CSLibExt.Computability.Complexity.Defs
public import CSLibExt.Complexity.NPComplete.ShortestTotalPathLengthSpanningTreeDefs

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.ShortestTotalPathLengthSpanningTree

/-!
# SHORTEST TOTAL PATH LENGTH SPANNING TREE is NP-complete

INSTANCE: a graph `G = (V, E)` and an integer bound `B ∈ ℤ⁺`.
QUESTION: is there a spanning tree `T` for `G` such that the sum, over all pairs of vertices
`u, v ∈ V`, of the length of the path in `T` from `u` to `v` is no more than `B`?

(Garey and Johnson name the bound `B` in the instance and `K` in the question; it is the same
number.) The graph is unweighted: the length of a path is its number of edges, which in a tree
is `T.dist u v`. Each unordered pair `{u, v}` of distinct vertices is counted once (pairs with
`u = v` contribute `0`). A spanning tree for `G` is a Mathlib `SimpleGraph.IsTree` on all of
`V` with `T ≤ G`.

Encoding: the instance is decoded from a bitstring with the repository's
canonical `MetaMathlibExt.BitstringEncoding`. Undecodable bitstrings, and
bitstrings decoding to malformed instances, are no-instances.

NP-completeness is stated in the same form as the proved results in
`CSLibExt.Computability.Complexity.Karp`: membership in
`MetaMathlibExt.ComplexityTheory.NP`, plus a polynomial-time many-one
reduction from every language in `NP`
(`Cslib.CookLevin.PolyManyOneRed`).
-/

/-- **SHORTEST TOTAL PATH LENGTH SPANNING TREE is NP-complete.** Source: Garey and Johnson
(1979), [ND3]; Johnson, Lenstra, and Rinnooy Kan (1978). -/
public theorem_wanted shortestTotalPathLengthSpanningTree_npComplete :
    shortestTotalPathLengthSpanningTreeDec ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L shortestTotalPathLengthSpanningTreeDec

end MetaMathlibExt.Complexity.NPComplete.ShortestTotalPathLengthSpanningTree
