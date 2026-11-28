/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# MINIMUM BROADCAST TIME for fixed K ≥ 4 is NP-complete

Source:
M. R. Garey and D. S. Johnson, *Computers and Intractability: A Guide to the
Theory of NP-Completeness*, W. H. Freeman (1979), problem [ND49] MINIMUM BROADCAST TIME,
p. 219 (comment: "Remains NP-complete for any fixed `K ≥ 4`"; the entry's reference is
[Garey and Johnson, unpublished], "Transformation from 3DM").
-/
module

public import Batteries.Util.ProofWanted
public import CSLibExt.Computability.Complexity.Defs
public import CSLibExt.Complexity.NPComplete.MinimumBroadcastTimeFixedKDefs

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.MinimumBroadcastTimeFixedK

/-!
# MINIMUM BROADCAST TIME for fixed K ≥ 4 is NP-complete

For a fixed integer `K ≥ 4`:
INSTANCE: a graph `G = (V, E)` and a subset `V₀ ⊆ V`.
QUESTION: can a message be "broadcast" from the base set `V₀` to all other vertices in time `K`,
that is, is there a sequence `V₀, E₁, V₁, E₂, …, E_K, V_K` such that each `Vᵢ ⊆ V`, each
`Eᵢ ⊆ E`, `V_K = V`, and, for `1 ≤ i ≤ K`, (1) each edge in `Eᵢ` has exactly one endpoint in
`Vᵢ₋₁`, (2) no two edges in `Eᵢ` share a common endpoint, and (3)
`Vᵢ = Vᵢ₋₁ ∪ {v : {u, v} ∈ Eᵢ}`?

This is MINIMUM BROADCAST TIME ([ND49], `MinimumBroadcastTimeWanted`) with the time bound `K`
fixed instead of part of the instance. An instance is a graph with a base set, `(n, E, V₀)`; it
is decided as the [ND49] instance `(n, E, V₀, K)` (`withBound K`), whose
`MinimumBroadcastTime.WellFormed` (simple edge list, `V₀` a list of distinct vertices, `0 < K`)
and `MinimumBroadcastTime.MinimumBroadcastTimeFeasible` are reused unchanged. Garey and Johnson
state the hardness for every fixed `K ≥ 4`, credited to their own unpublished work, and note
that the problem is solvable in polynomial time by matching for `K = 1`.

Encoding: the instance is decoded from a bitstring with the repository's
canonical `MetaMathlibExt.BitstringEncoding`. Undecodable bitstrings, and
bitstrings decoding to malformed instances, are no-instances.

NP-completeness is stated in the same form as the proved results in
`CSLibExt.Computability.Complexity.Karp`: membership in
`MetaMathlibExt.ComplexityTheory.NP`, plus a polynomial-time many-one
reduction from every language in `NP`
(`Cslib.CookLevin.PolyManyOneRed`).
-/

/-- **MINIMUM BROADCAST TIME is NP-complete for every fixed `K ≥ 4`.** Source: Garey and Johnson
(1979), [ND49], comment (Garey and Johnson, unpublished). -/
public theorem_wanted minimumBroadcastTimeFixedK_npComplete (K : ℕ) (hK : 4 ≤ K) :
    minimumBroadcastTimeFixedKDec K ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L (minimumBroadcastTimeFixedKDec K)

end MetaMathlibExt.Complexity.NPComplete.MinimumBroadcastTimeFixedK
