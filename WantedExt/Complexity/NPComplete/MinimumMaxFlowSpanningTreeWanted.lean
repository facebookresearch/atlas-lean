/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# MINIMUM MAX-FLOW SPANNING TREE is NP-complete

Source:
D. S. Johnson, "The NP-completeness column: an ongoing guide" (fourteenth edition), Journal of
Algorithms 6 (1985), 145-159, problem [1] MINIMUM MAX-FLOW SPANNING TREE;
P. M. Camerini, G. Galbiati and F. Maffioli, "Complexity of spanning tree problems: Part I",
European Journal of Operational Research 5(5) (1980), 346-352,
doi:10.1016/0377-2217(80)90164-2.
-/
module

public import Batteries.Util.ProofWanted
public import CSLibExt.Computability.Complexity.Defs
public import CSLibExt.Complexity.NPComplete.MinimumMaxFlowSpanningTreeDefs

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.MinimumMaxFlowSpanningTree

open ShortestTotalPathLengthSpanningTree (ShortestTotalPathLengthSpanningTreeInstance Graph
  WellFormed)

/-!
# MINIMUM MAX-FLOW SPANNING TREE is NP-complete

INSTANCE: a graph `G = (V, E)` and a bound `B > 0`.
QUESTION: is there a spanning tree `T = (V, E')` for `G` such that for all edges `e ∈ E'`, the
"flow" on `e`, i.e., the number `f(e)` of pairs of vertices `u, v ∈ V` that would be
disconnected if `e` were removed from `T`, is no more than `B`?

This is Johnson's statement in the fourteenth edition of the NP-completeness column, with the
reference Camerini, Galbiati and Maffioli (1980) (a transformation from 3-DIMENSIONAL MATCHING).
The column notes that replacing the maximum of the flows by their sum gives SHORTEST TOTAL PATH
LENGTH SPANNING TREE ([ND3]), stated on `main` as
`WantedExt.Complexity.NPComplete.ShortestTotalPathLengthSpanningTreeWanted`; this module reuses
its instance (vertex count `n`, edge list, bound `B`), its graph
(`Cslib.Complexity.Karp.edgeGraph` on `Fin n`), its `WellFormed` (simple edge list, `0 < B`)
and its notion of a spanning tree for `G` (a Mathlib `SimpleGraph.IsTree` on all of `V` with
`T ≤ G`).

`edgeFlow T u v` counts the unordered pairs `{x, y}` of vertices (each once, as `x < y`) that are
not connected in `T.deleteEdges {s(u, v)}`, the tree with the edge `{u, v}` removed. In a tree
this is the product of the sizes of the two components that the edge separates.

Encoding: the instance is decoded from a bitstring with the repository's
canonical `MetaMathlibExt.BitstringEncoding`. Undecodable bitstrings, and
bitstrings decoding to malformed instances, are no-instances.

NP-completeness is stated in the same form as the proved results in
`CSLibExt.Computability.Complexity.Karp`: membership in
`MetaMathlibExt.ComplexityTheory.NP`, plus a polynomial-time many-one
reduction from every language in `NP`
(`Cslib.CookLevin.PolyManyOneRed`).
-/

/-- **MINIMUM MAX-FLOW SPANNING TREE is NP-complete.** Source: Johnson (1985), NP-completeness
column 14, problem [1]; Camerini, Galbiati and Maffioli (1980). -/
public theorem_wanted minimumMaxFlowSpanningTree_npComplete :
    minimumMaxFlowSpanningTreeDec ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L minimumMaxFlowSpanningTreeDec

end MetaMathlibExt.Complexity.NPComplete.MinimumMaxFlowSpanningTree
