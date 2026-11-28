/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# MAXIMUM EDGE BICLIQUE is NP-complete

Source:
R. Peeters, "The maximum edge biclique problem is NP-complete", Discrete Applied Mathematics
131(3) (2003), 651-654, doi:10.1016/S0166-218X(03)00333-0;
N. Gillis and F. Glineur, "Nonnegative factorization and the maximum edge biclique problem",
arXiv:0810.4225 (2008), Section 3.1 (the problem as stated here; its decision version "has been
shown to be NP-complete" by Peeters).
-/
module

public import Batteries.Util.ProofWanted
public import CSLibExt.Computability.Complexity.Defs
public import CSLibExt.Complexity.NPComplete.MaximumEdgeBicliqueDefs

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.MaximumEdgeBiclique

/-!
# MAXIMUM EDGE BICLIQUE is NP-complete

INSTANCE: a bipartite graph `G = (V₁ ∪ V₂, E)` with `E ⊆ V₁ × V₂`, and a positive integer `K`.
QUESTION: does `G` contain a biclique with at least `K` edges, that is, sets `A ⊆ V₁` and
`B ⊆ V₂` with `A × B ⊆ E` and `|A| · |B| ≥ K`?

The sides are `V₁ = Fin p` and `V₂ = Fin q`, and an edge is a pair `(a, b)` with `a ∈ V₁`,
`b ∈ V₂`, so the bipartition is part of the instance, as in the source. A biclique `A ∪ B`
with `A × B ⊆ E` has exactly the `|A| · |B|` edges `A × B`. `K` uses the canonical binary
encoding. Since `K` is positive, a biclique meeting the bound has `A` and `B` nonempty, and
then every vertex of `A ∪ B` is an endpoint of a listed edge.

Encoding: the instance is decoded from a bitstring with the repository's
canonical `MetaMathlibExt.BitstringEncoding`. Undecodable bitstrings, and
bitstrings decoding to malformed instances, are no-instances.

NP-completeness is stated in the same form as the proved results in
`CSLibExt.Computability.Complexity.Karp`: membership in
`MetaMathlibExt.ComplexityTheory.NP`, plus a polynomial-time many-one
reduction from every language in `NP`
(`Cslib.CookLevin.PolyManyOneRed`).
-/

/-- **MAXIMUM EDGE BICLIQUE is NP-complete.** Source: Peeters (2003). -/
public theorem_wanted maximumEdgeBiclique_npComplete :
    maximumEdgeBicliqueDec ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L maximumEdgeBicliqueDec

end MetaMathlibExt.Complexity.NPComplete.MaximumEdgeBiclique
