/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# GRAPH BURNING is NP-complete

Source:
S. Bessy, A. Bonato, J. Janssen, D. Rautenbach and E. Roshanbin, "Burning a graph is hard",
Discrete Applied Mathematics 232 (2017), 73-87, doi:10.1016/j.dam.2017.07.016.
-/
module

public import Batteries.Util.ProofWanted
public import CSLibExt.Computability.Complexity.Defs
public import CSLibExt.Complexity.NPComplete.GraphBurningDefs

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.GraphBurning

/-!
# GRAPH BURNING is NP-complete

INSTANCE: a graph `G = (V, E)` (finite, simple, undirected, with at least one vertex) and an
integer `k ≥ 2`.
QUESTION: is the burning number `b(G)` at most `k`?

Bessy, Bonato, Janssen, Rautenbach and Roshanbin, Lemma 2: "The burning number of a graph G is
the minimum length of a sequence (x₁, …, x_k) of nodes in G that satisfies" the covering
condition `N_{k-1}[x₁] ∪ N_{k-2}[x₂] ∪ ⋯ ∪ N₀[x_k] = V(G)`, where `N_r[x]` is the set of
vertices at distance at most `r` from `x`. So `b(G) ≤ k` exactly when some sequence
`x₀, …, x_{k-1}` (indexed from `0`) has every vertex within distance `k - 1 - j` of some `x_j`.
Distances are Mathlib's extended distance `SimpleGraph.edist` (`⊤` between different
components), since the graph need not be connected. The burning process burns one vertex per
round, so the graph has at least one vertex (the source's "simple graph G of order n" with a
burning sequence); the null graph is malformed.

Encoding: the instance is decoded from a bitstring with the repository's
canonical `MetaMathlibExt.BitstringEncoding`. Undecodable bitstrings, and
bitstrings decoding to malformed instances, are no-instances.

NP-completeness is stated in the same form as the proved results in
`CSLibExt.Computability.Complexity.Karp`: membership in
`MetaMathlibExt.ComplexityTheory.NP`, plus a polynomial-time many-one
reduction from every language in `NP`
(`Cslib.CookLevin.PolyManyOneRed`).
-/

/-- **GRAPH BURNING is NP-complete.** Source: Bessy, Bonato, Janssen, Rautenbach and Roshanbin
(2017). -/
public theorem_wanted graphBurning_npComplete :
    graphBurningDec ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L graphBurningDec

end MetaMathlibExt.Complexity.NPComplete.GraphBurning
