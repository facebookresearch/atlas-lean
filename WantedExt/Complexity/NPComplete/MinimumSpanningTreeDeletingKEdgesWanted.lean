/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# MINIMUM SPANNING TREE DELETING K EDGES is NP-complete

Source:
G. N. Frederickson and R. Solis-Oba, "Increasing the weight of minimum spanning trees",
Journal of Algorithms 33 (1999), 244-266, doi:10.1006/jagm.1999.1026 (the version in which
edge weights are fixed and edges are removed at unit cost is NP-hard);
W. Liang, "Finding the k most vital edges with respect to minimum spanning trees for fixed k",
Discrete Applied Mathematics 113 (2001), 319-327, doi:10.1016/S0166-218X(01)00189-5
(Section 1 states the problem with `|S*| = k` and records that Frederickson and Solis-Oba proved
it NP-complete);
P. Crescenzi and V. Kann (eds.), *A compendium of NP optimization problems*, problem
MAXIMUM MINIMUM SPANNING TREE DELETING K
EDGES. -/
module

public import Batteries.Util.ProofWanted
public import CSLibExt.Computability.Complexity.Defs
public import CSLibExt.Complexity.NPComplete.MinimumSpanningTreeDeletingKEdgesDefs

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.MinimumSpanningTreeDeletingKEdges

/-!
# MINIMUM SPANNING TREE DELETING K EDGES is NP-complete

INSTANCE: a connected graph `G = (V, E)`, a weight function `w : E → ℕ`, a number `k`, and a
positive integer `K`.
QUESTION: is there a subset `E' ⊆ E` of `k` edges and a minimum spanning tree `T` of the graph
`(V, E - E')` whose weight is at least `K`?

This is the decision version of MAXIMUM MINIMUM SPANNING TREE DELETING K EDGES in the
Crescenzi-Kann compendium ("Subset E' ⊆ E of k edges and a minimum spanning tree T in the graph
(V, E - E')", measure "Weight of T"), the `k` most vital edges problem for minimum spanning
trees, which Frederickson and Solis-Oba proved NP-hard (as recorded by Liang). The graph
`(V, E - E')` must have a spanning tree, so it is connected.

The graph is given as a list of weighted edges `(u, v, w)`, at most one per unordered pair. An
edge set is a sublist of this list; its graph is `Cslib.Complexity.Karp.edgeGraph` on its
endpoint pairs and its weight is the sum of its entries' weights. A spanning tree of an edge
list `R` is a sublist of `R` whose graph is a tree on all `n` vertices (`SimpleGraph.IsTree`),
and it is minimum when no spanning tree of `R` weighs less.

Encoding: the instance is decoded from a bitstring with the repository's
canonical `MetaMathlibExt.BitstringEncoding`. Undecodable bitstrings, and
bitstrings decoding to malformed instances, are no-instances.

NP-completeness is stated in the same form as the proved results in
`CSLibExt.Computability.Complexity.Karp`: membership in
`MetaMathlibExt.ComplexityTheory.NP`, plus a polynomial-time many-one
reduction from every language in `NP`
(`Cslib.CookLevin.PolyManyOneRed`).
-/

/-- **MINIMUM SPANNING TREE DELETING K EDGES is NP-complete.** Source: Frederickson and
Solis-Oba (1999); Liang (2001); Crescenzi and Kann, MAXIMUM MINIMUM SPANNING TREE DELETING K
EDGES. -/
public theorem_wanted minimumSpanningTreeDeletingKEdges_npComplete :
    minimumSpanningTreeDeletingKEdgesDec ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L minimumSpanningTreeDeletingKEdgesDec

end MetaMathlibExt.Complexity.NPComplete.MinimumSpanningTreeDeletingKEdges
