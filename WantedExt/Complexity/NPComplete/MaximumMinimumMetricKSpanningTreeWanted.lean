/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# MAXIMUM MINIMUM METRIC K-SPANNING TREE is NP-complete

Source:
P. Crescenzi and V. Kann (eds.), *A compendium of NP optimization problems* (web edition,
2000), MAXIMUM MINIMUM METRIC K-SPANNING TREE (decision version);
M. M. Halldórsson, K. Iwano, N. Katoh, and T. Tokuyama, "Finding subsets maximizing minimum
structures", SIAM Journal on Discrete Mathematics 12 (1999), 342-359,
doi:10.1137/S0895480196309791.
-/
module

public import Batteries.Util.ProofWanted
public import CSLibExt.Computability.Complexity.Defs
public import CSLibExt.Complexity.NPComplete.MaximumMinimumMetricKSpanningTreeDefs

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.MaximumMinimumMetricKSpanningTree

/-!
# MAXIMUM MINIMUM METRIC K-SPANNING TREE is NP-complete

INSTANCE: a complete graph on a set `V` of `n` vertices with a length `l(u, v) ∈ ℤ⁺` on each
edge satisfying the triangle inequality, a number `k`, and a bound `K`. QUESTION: is there a
subset `V' ⊆ V` with `|V'| = k` such that the minimum spanning tree of the subgraph induced by
`V'` has length at least `K`?

This is the decision version of the compendium's MAXIMUM MINIMUM METRIC K-SPANNING TREE,
also called REMOTE-MST: Halldórsson, Iwano, Katoh, and Tokuyama (1999) show that on metric
graphs it is NP-hard to approximate within a factor less than `2` (the compendium notes a
reduction from MAXIMUM INDEPENDENT SET: with lengths `1` on the edges of a graph and `2` on its
non-edges, the minimum spanning tree on `k` vertices has length `2 (k - 1)` exactly when they
are independent).

The lengths are an `n × n` matrix that is a metric on the vertices: zero exactly on the
diagonal (positive between distinct vertices), symmetric, and satisfying the triangle
inequality. The induced subgraph on `V'` is complete, so
its minimum spanning tree has length at least `K` exactly when every tree on the vertex set
`V'` (a `SimpleGraph` on the subtype with `SimpleGraph.IsTree`) has total edge length at least
`K`. The length of an edge `{u, v}` is read as `min (l(u, v), l(v, u))`, which is `l(u, v)` for
a symmetric matrix and makes the edge length a function of the unordered pair. `1 ≤ k ≤ n` (a
tree needs a vertex). Binary encoding of all numbers.

Encoding: the instance is decoded from a bitstring with the repository's
canonical `MetaMathlibExt.BitstringEncoding`. Undecodable bitstrings, and
bitstrings decoding to malformed instances, are no-instances.

NP-completeness is stated in the same form as the proved results in
`CSLibExt.Computability.Complexity.Karp`: membership in
`MetaMathlibExt.ComplexityTheory.NP`, plus a polynomial-time many-one
reduction from every language in `NP`
(`Cslib.CookLevin.PolyManyOneRed`).
-/

/-- **MAXIMUM MINIMUM METRIC K-SPANNING TREE is NP-complete.** Source: Crescenzi and Kann,
MAXIMUM MINIMUM METRIC K-SPANNING TREE; Halldórsson, Iwano, Katoh, and Tokuyama (1999). -/
public theorem_wanted maximumMinimumMetricKSpanningTree_npComplete :
    maximumMinimumMetricKSpanningTreeDec ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L maximumMinimumMetricKSpanningTreeDec

end MetaMathlibExt.Complexity.NPComplete.MaximumMinimumMetricKSpanningTree
