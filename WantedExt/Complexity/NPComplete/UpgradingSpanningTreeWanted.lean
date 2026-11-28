/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# UPGRADING SPANNING TREE is NP-complete

Source:
S. O. Krumke, M. V. Marathe, H. Noltemeier, R. Ravi, S. S. Ravi, R. Sundaram and H.-C. Wirth,
"Improving minimum cost spanning trees by upgrading nodes", Journal of Algorithms 33 (1999),
92-111, doi:10.1006/jagm.1999.1021 (Definition 2; Section 5, Lemma 18: reduction from MINIMUM
DOMINATING SET);
P. Crescenzi and V. Kann (eds.), *A compendium of NP optimization problems*, problem
MINIMUM UPGRADING SPANNING TREE.
-/
module

public import Batteries.Util.ProofWanted
public import CSLibExt.Computability.Complexity.Defs
public import CSLibExt.Complexity.NPComplete.UpgradingSpanningTreeDefs

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.UpgradingSpanningTree

/-!
# UPGRADING SPANNING TREE is NP-complete

INSTANCE: a connected graph `G = (V, E)`, three edge weights `d₀(e) ≥ d₁(e) ≥ d₂(e) ≥ 0` for
each `e ∈ E`, an upgrade cost `c(v) ∈ ℕ` for each `v ∈ V`, a bound `D ∈ ℕ`, and a positive
integer `K`.
QUESTION: is there a set `W ⊆ V` with `c(W) = ∑_{v ∈ W} c(v) ≤ K` such that the weight of a
minimum spanning tree of `G` under the edge weights `d_W` is at most `D`, where
`d_W(u, v) = d_i(u, v)` for `i = |W ∩ {u, v}|`?

This is the decision version of the upgrading minimum spanning tree problem of Krumke, Marathe,
Noltemeier, Ravi, Ravi, Sundaram and Wirth (Definition 2: "upgrade a set W ⊆ V of nodes such
that MST(G, d_W) ≤ D and c(W) is minimized"; `d_i(e)` "represents the length or delay of the
edge e if exactly i of its endpoints are upgraded"), MINIMUM UPGRADING SPANNING TREE in the
Crescenzi-Kann compendium. Their Lemma 18 reduces MINIMUM DOMINATING SET to it, so the decision
version is NP-hard; a certificate is `W` with a spanning tree.

The minimum spanning tree weight is at most `D` exactly when some spanning tree of `G` weighs at
most `D` under `d_W`, which is what is stated. The graph is given as a list of edges
`(u, v, d₀, d₁, d₂)`, at most one per unordered pair; a spanning tree is a sublist of it whose
graph (`Cslib.Complexity.Karp.edgeGraph`) is a tree on all `n` vertices
(`SimpleGraph.IsTree`). Upgrade costs are a list with one entry per vertex.

Encoding: the instance is decoded from a bitstring with the repository's
canonical `MetaMathlibExt.BitstringEncoding`. Undecodable bitstrings, and
bitstrings decoding to malformed instances, are no-instances.

NP-completeness is stated in the same form as the proved results in
`CSLibExt.Computability.Complexity.Karp`: membership in
`MetaMathlibExt.ComplexityTheory.NP`, plus a polynomial-time many-one
reduction from every language in `NP`
(`Cslib.CookLevin.PolyManyOneRed`).
-/

/-- **UPGRADING SPANNING TREE is NP-complete.** Source: Krumke, Marathe, Noltemeier, Ravi,
Ravi, Sundaram and Wirth (1999), Definition 2 and Lemma 18; Crescenzi and Kann, MINIMUM UPGRADING
SPANNING TREE. -/
public theorem_wanted upgradingSpanningTree_npComplete :
    upgradingSpanningTreeDec ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L upgradingSpanningTreeDec

end MetaMathlibExt.Complexity.NPComplete.UpgradingSpanningTree
