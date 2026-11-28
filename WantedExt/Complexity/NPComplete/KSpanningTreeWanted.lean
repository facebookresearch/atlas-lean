/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# K-SPANNING TREE is NP-complete

Source:
P. Crescenzi and V. Kann, *A compendium of NP optimization problems*, problem
MINIMUM K-SPANNING TREE;
R. Ravi, R. Sundaram, M. V. Marathe, D. J. Rosenkrantz, and S. S. Ravi, "Spanning trees -
short or small", SIAM Journal on Discrete Mathematics 9 (1996), 178-200,
doi:10.1137/S0895480194266331.
-/
module

public import Batteries.Util.ProofWanted
public import CSLibExt.Computability.Complexity.Defs
public import CSLibExt.Complexity.NPComplete.KSpanningTreeDefs

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.KSpanningTree

open BoundedDiameterSpanningTree (BoundedDiameterSpanningTreeInstance endpoints Graph weight)

/-!
# K-SPANNING TREE is NP-complete

INSTANCE: a graph `G = (V, E)`, a positive integer `k ≤ |V|`, a weight function `w : E → ℕ`,
and a positive integer `K`.
QUESTION: is there a `k`-spanning tree, i.e. a subtree `T` of `G` with at least `k` nodes, whose
weight `∑_{e ∈ T} w(e)` is at most `K`?

This is the decision version of MINIMUM K-SPANNING TREE from the Crescenzi-Kann compendium, the kMST
problem of Ravi, Sundaram, Marathe, Rosenkrantz and Ravi ("a tree of minimum weight spanning at
least `k` nodes in an edge-weighted graph"), which they prove NP-complete (Theorem 2.1, by a
reduction from STEINER TREE whose weights include `0`).

The instance, the graph and the weights are those of BOUNDED DIAMETER SPANNING TREE
(`WantedExt.Complexity.NPComplete.BoundedDiameterSpanningTreeWanted`), reused unchanged: the
vertex count `n` (vertices `Fin n`), a simple edge list with weights (an entry `(u, v, w)` is the
edge `{u, v}` of weight `w`), then `k` and `K`. Here weights may be `0`. A subtree of `G` is a
Mathlib `SimpleGraph.Subgraph` `T` of `G` whose coercion `T.coe` is a tree (`IsTree`: connected,
hence nonempty, and acyclic); its nodes are `T.verts` and its weight is the sum of `w(e)` over
its (finitely many) edges `T.edgeSet`. Weights are in binary.

Encoding: the instance is decoded from a bitstring with the repository's
canonical `MetaMathlibExt.BitstringEncoding`. Undecodable bitstrings, and
bitstrings decoding to malformed instances, are no-instances.

NP-completeness is stated in the same form as the proved results in
`CSLibExt.Computability.Complexity.Karp`: membership in
`MetaMathlibExt.ComplexityTheory.NP`, plus a polynomial-time many-one
reduction from every language in `NP`
(`Cslib.CookLevin.PolyManyOneRed`).
-/

/-- **K-SPANNING TREE is NP-complete.** Source: Crescenzi and Kann, MINIMUM K-SPANNING TREE; Ravi,
Sundaram, Marathe, Rosenkrantz, and Ravi (1996), Theorem 2.1. -/
public theorem_wanted kSpanningTree_npComplete :
    kSpanningTreeDec ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L kSpanningTreeDec

end MetaMathlibExt.Complexity.NPComplete.KSpanningTree
