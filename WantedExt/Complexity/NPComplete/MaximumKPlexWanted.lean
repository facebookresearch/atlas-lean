/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# MAXIMUM K-PLEX is NP-complete

Source:
B. Balasundaram, S. Butenko and I. V. Hicks, "Clique relaxations in social network analysis: the
maximum k-plex problem", Operations Research 59(1) (2011), 133-142, doi:10.1287/opre.1100.0851.
-/
module

public import Batteries.Util.ProofWanted
public import CSLibExt.Computability.Complexity.Defs
public import CSLibExt.Complexity.NPComplete.MaximumKPlexDefs

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.MaximumKPlex

/-!
# MAXIMUM K-PLEX is NP-complete

Fix a positive integer `k`. INSTANCE: a simple undirected graph `G = (V, E)` and a positive
integer `c`. QUESTION: does there exist a `k`-plex of size `c` in `G`, where `S ⊆ V` is a
`k`-plex if every vertex of `S` has at least `|S| - k` neighbors in `S`
(`deg_{G[S]}(v) = |N(v) ∩ S| ≥ |S| - k` for all `v ∈ S`)? This is k-PLEX of Balasundaram,
Butenko and Hicks (Definition 1 and Section 2.1); their Theorem 2: "k-PLEX is NP-complete for
any fixed positive integer k". For `k = 1` a `k`-plex is a clique.

The family is stated as one theorem with `k` and `1 ≤ k` as parameters. `S` is a `Finset` of
vertices `Fin n` of the graph `Cslib.Complexity.Karp.edgeGraph n E`, and `N(v) ∩ S` is the set
of vertices of `S` adjacent to `v`.

Encoding: the instance is decoded from a bitstring with the repository's
canonical `MetaMathlibExt.BitstringEncoding`. Undecodable bitstrings, and
bitstrings decoding to malformed instances, are no-instances.

NP-completeness is stated in the same form as the proved results in
`CSLibExt.Computability.Complexity.Karp`: membership in
`MetaMathlibExt.ComplexityTheory.NP`, plus a polynomial-time many-one
reduction from every language in `NP`
(`Cslib.CookLevin.PolyManyOneRed`).
-/

/-- **MAXIMUM K-PLEX is NP-complete** for every fixed positive integer `k`. Source:
Balasundaram, Butenko and Hicks (2011), Theorem 2. -/
public theorem_wanted maximumKPlex_npComplete (k : ℕ) (hk : 1 ≤ k) :
    maximumKPlexDec k ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L (maximumKPlexDec k)

end MetaMathlibExt.Complexity.NPComplete.MaximumKPlex
