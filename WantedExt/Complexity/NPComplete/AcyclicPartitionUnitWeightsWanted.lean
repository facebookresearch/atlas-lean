/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# ACYCLIC PARTITION with unit weights and costs is NP-complete

Source:
M. R. Garey and D. S. Johnson, *Computers and Intractability: A Guide to the Theory of
NP-Completeness*, W. H. Freeman (1979), problem [ND15] ACYCLIC PARTITION, p. 209, comment:
"Remains NP-complete even if all v ∈ V have w(v) = 1 and all a ∈ A have c(a) = 1" (the
entry's reference is [Garey and Johnson, ——], unpublished; transformation from X3C).
-/
module

public import Batteries.Util.ProofWanted
public import CSLibExt.Computability.Complexity.Defs
public import CSLibExt.Complexity.NPComplete.AcyclicPartitionUnitWeightsDefs

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.AcyclicPartitionUnitWeights

open MetaMathlibExt.Complexity.NPComplete.AcyclicPartition
  (AcyclicPartitionInstance AcyclicPartitionFeasible)

/-!
# ACYCLIC PARTITION with unit weights and costs is NP-complete

INSTANCE: a directed graph `G = (V, A)`, weight `w(v) = 1` for each `v ∈ V`, cost `c(a) = 1`
for each `a ∈ A`, and positive integers `B` and `K`.
QUESTION: is there a partition of `V` into disjoint sets `V₁, V₂, …, V_m` such that the
directed graph `G' = (V', A')`, where `V' = {V₁, V₂, …, V_m}` and `(Vᵢ, Vⱼ) ∈ A'` if and only if
`(vᵢ, vⱼ) ∈ A` for some `vᵢ ∈ Vᵢ` and some `vⱼ ∈ Vⱼ` (`i ≠ j`: an arc inside one block gives no
arc of `G'`), is acyclic, such that the sum of the weights of the vertices in each `Vᵢ` does not
exceed `B` (at most `B` vertices), and such that the sum of the costs of all those arcs having
their endpoints in different sets does not exceed `K` (at most `K` such arcs)?

The instance, `WellFormed` (one positive weight per vertex, an arc list without loops or
repeated arcs, positive costs, `0 < B`, `0 < K`) and the question are those of
`AcyclicPartitionWanted` ([ND15]); this module adds the restriction that every vertex weight and
every arc cost equals `1` to well-formedness.

Encoding: the instance is decoded from a bitstring with the repository's
canonical `MetaMathlibExt.BitstringEncoding`. Undecodable bitstrings, and
bitstrings decoding to malformed instances, are no-instances.

NP-completeness is stated in the same form as the proved results in
`CSLibExt.Computability.Complexity.Karp`: membership in
`MetaMathlibExt.ComplexityTheory.NP`, plus a polynomial-time many-one
reduction from every language in `NP`
(`Cslib.CookLevin.PolyManyOneRed`).
-/

/-- **ACYCLIC PARTITION with unit weights and costs is NP-complete.** Source: Garey and
Johnson (1979), [ND15], comment. -/
public theorem_wanted acyclicPartitionUnitWeights_npComplete :
    acyclicPartitionUnitWeightsDec ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L acyclicPartitionUnitWeightsDec

end MetaMathlibExt.Complexity.NPComplete.AcyclicPartitionUnitWeights
