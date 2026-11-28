/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# MINIMUM BROADCAST TIME is NP-complete

Source:
M. R. Garey and D. S. Johnson, *Computers and Intractability: A Guide to the
Theory of NP-Completeness*, W. H. Freeman (1979), problem [ND49] MINIMUM BROADCAST TIME
(credited there to Garey and Johnson, unpublished: transformation from 3DM);
P. J. Slater, E. J. Cockayne and S. T. Hedetniemi, "Information dissemination in trees", SIAM
Journal on Computing 10 (1981), 692-701, doi:10.1137/0210052.
-/
module

public import Batteries.Util.ProofWanted
public import CSLibExt.Computability.Complexity.Defs
public import CSLibExt.Complexity.NPComplete.MinimumBroadcastTimeDefs

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.MinimumBroadcastTime

/-!
# MINIMUM BROADCAST TIME is NP-complete

INSTANCE: a graph `G = (V, E)`, a subset `V₀ ⊆ V`, and a positive integer `K`.
QUESTION: can a message be "broadcast" from the base set `V₀` to all other vertices in time `K`,
that is, is there a sequence `V₀, E₁, V₁, E₂, …, E_K, V_K` such that each `Vᵢ ⊆ V`, each
`Eᵢ ⊆ E`, `V_K = V`, and, for `1 ≤ i ≤ K`, (1) each edge in `Eᵢ` has exactly one endpoint in
`Vᵢ₋₁`, (2) no two edges in `Eᵢ` share a common endpoint, and (3)
`Vᵢ = Vᵢ₋₁ ∪ {v : {u, v} ∈ Eᵢ}`?

The graph is a Mathlib `SimpleGraph (Fin n)` given by an edge list, and `V₀` is a list of
distinct vertices. The sequence is a pair of functions `V : ℕ → Set (Fin n)` and
`E : ℕ → Set (Sym2 (Fin n))`, constrained at the indices `0, …, K` the question names;
`BroadcastStep` states conditions `Eᵢ ⊆ E`, (1), (2) and (3) for one step. An edge has exactly
one endpoint in `Vᵢ₋₁` when it is `s(u, v)` with `u ∈ Vᵢ₋₁` and `v ∉ Vᵢ₋₁`. As in the source,
the sequence has exactly `K` steps; a step with `Eᵢ = ∅` keeps `Vᵢ = Vᵢ₋₁`, so this is the same
as "at most `K` steps". The special case `|V₀| = 1` is the single-originator problem that Slater,
Cockayne and Hedetniemi prove NP-complete, which gives hardness of this problem. A broadcast that
finishes at all finishes within `|V|` steps, so `K` may be capped at `|V|` and the binary
encoding of `K` does not affect membership in `NP`.

Encoding: the instance is decoded from a bitstring with the repository's
canonical `MetaMathlibExt.BitstringEncoding`. Undecodable bitstrings, and
bitstrings decoding to malformed instances, are no-instances.

NP-completeness is stated in the same form as the proved results in
`CSLibExt.Computability.Complexity.Karp`: membership in
`MetaMathlibExt.ComplexityTheory.NP`, plus a polynomial-time many-one
reduction from every language in `NP`
(`Cslib.CookLevin.PolyManyOneRed`).
-/

/-- **MINIMUM BROADCAST TIME is NP-complete.** Source: Garey and Johnson (1979), [ND49];
Slater, Cockayne and Hedetniemi (1981). -/
public theorem_wanted minimumBroadcastTime_npComplete :
    minimumBroadcastTimeDec ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L minimumBroadcastTimeDec

end MetaMathlibExt.Complexity.NPComplete.MinimumBroadcastTime
