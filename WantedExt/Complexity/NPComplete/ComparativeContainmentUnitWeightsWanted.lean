/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# COMPARATIVE CONTAINMENT with unit weights is NP-complete

Source:
M. R. Garey and D. S. Johnson, *Computers and Intractability: A Guide to the
Theory of NP-Completeness*, W. H. Freeman (1979), problem [SP10] COMPARATIVE CONTAINMENT,
p. 223, comment: "Remains NP-complete even if all subsets in R and S have weight 1 [Garey and
Johnson, ——]" (unpublished; the result and its attribution are those recorded by Garey and
Johnson).
-/
module

public import Batteries.Util.ProofWanted
public import CSLibExt.Computability.Complexity.Defs
public import CSLibExt.Complexity.NPComplete.ComparativeContainmentUnitWeightsDefs

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.ComparativeContainmentUnitWeights

open MetaMathlibExt.Complexity.NPComplete.ComparativeContainment
  (ComparativeContainmentInstance ComparativeContainmentFeasible)

/-!
# COMPARATIVE CONTAINMENT with unit weights is NP-complete

INSTANCE: two collections `R = {R₁, …, R_k}` and `S = {S₁, …, S_l}` of subsets of a finite set
`X`, all of weight 1. QUESTION: is there a subset `Y ⊆ X` such that the number of `R_i`
containing `Y` is at least the number of `S_j` containing `Y`, that is,
`∑_{Y ⊆ R_i} w(R_i) ≥ ∑_{Y ⊆ S_j} w(S_j)` with `w ≡ 1`?

The instance, its well-formedness and the question are those of
`WantedExt.Complexity.NPComplete.ComparativeContainmentWanted` ([SP10]: `X = Fin n`, each
collection an indexed list of (subset, weight) pairs), with every weight equal to 1.

Hardness (the comment credits unpublished work): for a graph `(V, E)` and `K ≤ |V|`, take
`X = V` and write `[Y ⊆ T]` for the indicator that `Y` is contained in `T`. Then
`[Y ⊆ V] = 1`, `[Y ⊆ V - {u}] = [u ∉ Y]` and `[Y ⊆ V - {u, v}] = [u ∉ Y ∧ v ∉ Y]`, so
`|Y| - K - (|V| + 1) e(Y)`, with `e(Y)` the number of edges inside `Y`, equals
`(|V| - K - (|V| + 1) |E|) [Y ⊆ V] + ∑_u ((|V| + 1) deg u - 1) [Y ⊆ V - {u}] -
(|V| + 1) ∑_{uv ∈ E} [Y ⊆ V - {u, v}]`. List each of these subsets in `R` as many times as its
coefficient when the coefficient is positive and in `S` as many times as its absolute value
when it is negative, all with weight 1 (a collection is an indexed list, so a subset may occur
more than once; there are polynomially many entries). The count of `R_i ⊇ Y` minus the count of
`S_j ⊇ Y` is then `|Y| - K - (|V| + 1) e(Y)`, which is nonnegative exactly when `Y` is an
independent set of size at least `K`; so INDEPENDENT SET reduces to this problem. Membership in
NP is inherited from [SP10]: `Y` is a certificate.

Encoding: the instance is decoded from a bitstring with the repository's
canonical `MetaMathlibExt.BitstringEncoding`. Undecodable bitstrings, and
bitstrings decoding to malformed instances, are no-instances.

NP-completeness is stated in the same form as the proved results in
`CSLibExt.Computability.Complexity.Karp`: membership in
`MetaMathlibExt.ComplexityTheory.NP`, plus a polynomial-time many-one
reduction from every language in `NP`
(`Cslib.CookLevin.PolyManyOneRed`).
-/

/-- **COMPARATIVE CONTAINMENT with unit weights is NP-complete.** Source: Garey and Johnson
(1979), [SP10], comment. -/
public theorem_wanted comparativeContainmentUnitWeights_npComplete :
    comparativeContainmentUnitWeightsDec ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L comparativeContainmentUnitWeightsDec

end MetaMathlibExt.Complexity.NPComplete.ComparativeContainmentUnitWeights
