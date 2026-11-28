/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# s-CLUB is NP-complete

Source:
B. Balasundaram, S. Butenko and S. Trukhanov, "Novel approaches for analyzing biological
networks", Journal of Combinatorial Optimization 10(1) (2005), 23-39,
doi:10.1007/s10878-005-1857-x;
S. Hartung, C. Komusiewicz and A. Nichterlein, "On structural parameterizations for the 2-club
problem", SOFSEM 2013, Lecture Notes in Computer Science 7741 (2013), 233-243,
doi:10.1007/978-3-642-35843-2_21 (Section 1: the problem statement, and "For all `s ≥ 1`,
s-Club is NP-complete on graphs of diameter `s+1`", citing Balasundaram, Butenko and
Trukhanov).
-/
module

public import Batteries.Util.ProofWanted
public import CSLibExt.Computability.Complexity.Defs
public import CSLibExt.Complexity.NPComplete.SClubDefs

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.SClub

/-!
# s-CLUB is NP-complete

For a fixed integer `s ≥ 2`: INSTANCE: a graph `G = (V, E)` (finite, simple, undirected) and a
positive integer `K`. QUESTION: is there a set `S ⊆ V` with `|S| ≥ K` such that the subgraph
`G[S]` induced by `S` has diameter at most `s` (an `s`-club of size at least `K`)?

Hartung, Komusiewicz and Nichterlein (Section 1) state the problem as "Input: An undirected
graph `G = (V, E)` and an integer `ℓ ≥ 1`. Question: Is there a vertex set `S ⊆ V` of size at
least `ℓ` such that `G[S]` has diameter at most `s`?", and record that for all `s ≥ 1` it is
NP-complete, even on graphs of diameter `s + 1`, by Balasundaram, Butenko and Trukhanov (whose
full text was not available). For `s = 1` the problem is CLIQUE, already in
`CSLibExt.Computability.Complexity.Karp`; this module states the cases `s ≥ 2`. Here `s` is a
constant of the language, not part of the input.

The induced subgraph is Mathlib's `SimpleGraph.induce`, and its diameter is Mathlib's
`SimpleGraph.ediam`, the supremum of the distances `SimpleGraph.edist`, which is `⊤` for a
disconnected graph, so an `s`-club induces a connected subgraph. The property is not hereditary
(the 5-cycle is a 2-club, but four of its vertices induce a path of diameter 3), so "size at
least `K`" is kept as in the source rather than "size exactly `K`".

The graph is given by an edge list on `Fin n`.

Encoding: the instance is decoded from a bitstring with the repository's
canonical `MetaMathlibExt.BitstringEncoding`. Undecodable bitstrings, and
bitstrings decoding to malformed instances, are no-instances.

NP-completeness is stated in the same form as the proved results in
`CSLibExt.Computability.Complexity.Karp`: membership in
`MetaMathlibExt.ComplexityTheory.NP`, plus a polynomial-time many-one
reduction from every language in `NP`
(`Cslib.CookLevin.PolyManyOneRed`).
-/

/-- **s-CLUB is NP-complete for every fixed `s ≥ 2`.** Source: Balasundaram, Butenko and
Trukhanov (2005); Hartung, Komusiewicz and Nichterlein (2013), Section 1. -/
public theorem_wanted sClub_npComplete (s : ℕ) (hs : 2 ≤ s) :
    sClubDec s ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L (sClubDec s)

end MetaMathlibExt.Complexity.NPComplete.SClub
