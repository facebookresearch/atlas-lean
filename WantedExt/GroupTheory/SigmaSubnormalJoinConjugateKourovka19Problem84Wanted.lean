/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# σ-subnormality from joins with conjugates (Kourovka Notebook Problem 19.84)

Kourovka Notebook, Archive of Solved Problems, Problem 19.84 (A. N. Skiba): for a partition `σ` of
the primes, a subgroup `A` of a finite group `G` is `σ`-subnormal if there is a chain `A = A₀ ≤ ⋯ ≤
Aₙ = G` with each `Aᵢ₋₁ ⊴ Aᵢ` or `Aᵢ / (Aᵢ₋₁)_{Aᵢ}` `σ`-primary. Suppose that `A` is `σ`-subnormal
in `⟨A, A^x⟩` for all `x ∈ G`. Is `A` `σ`-subnormal in `G`?
-/

module

public import Batteries.Util.ProofWanted
public import WantedExt.GroupTheory.KourovkaNotebookShared

@[expose] public section

namespace MathlibExt.GroupTheory.SigmaSubnormalJoinConjugateKourovka19Problem84Wanted

/-!
Source: E. I. Khukhro and V. D. Mazurov (eds.), Unsolved Problems in Group Theory: The Kourovka
Notebook, 21st issue, arXiv:1401.0300v49 (2026), Archive of Solved Problems, Problem 19.84 (A. N.
Skiba). UnsolvedMath record UM-00701632 (`KOU-19.84`), dataset ulamai/UnsolvedMath v1.8.0.

A partition `σ` of the primes is a family `σ : I → Set ℕ` of nonempty, pairwise disjoint sets of
primes covering all primes; a positive integer (a finite group) is `σ`-primary when its prime
divisors (those of its order) lie in one block `σᵢ`. `σ`-subnormality is the chain condition of the
Archive text of 19.84, with the quotient `Aᵢ₊₁ / (Aᵢ)_{Aᵢ₊₁}` replaced by its order, the index of
the normal core. `σ`-subnormality in `⟨A, A^x⟩` is that of `A.subgroupOf (A ⊔ A^x)`. The refutation
is one explicit finite configuration; checking it requires an argument about subgroup chains in
`S₅`, not a decision procedure on a small object. The `σ`-definitions are the shared ones in
`WantedExt/GroupTheory/KourovkaNotebookShared.lean`.
-/

open MathlibExt.GroupTheory.KourovkaNotebookShared

/-- Kourovka 19.84 (A. N. Skiba): for every partition `σ` of the primes, a subgroup `A` of a finite
group `G` that is `σ`-subnormal in `⟨A, A^x⟩` for every `x ∈ G` is `σ`-subnormal in `G`. -/
def sigmaSubnormalFromJoinsWithConjugates : Prop :=
  ∀ (I : Type) (σ : I → Set ℕ), IsPrimePartition σ → ∀ (G : Type) [Group G] [Finite G]
    (A : Subgroup G),
    (∀ x : G, IsSigmaSubnormal σ (A.subgroupOf (A ⊔ A.map (MulAut.conj x).toMonoidHom))) →
    IsSigmaSubnormal σ A

/--
Resolved false: the Kourovka Archive answers 19.84 "No, not always": in `S₅` with the partition `{2,
3} ∪ {5} ∪ …`, `A = ⟨(12)⟩` is `σ`-subnormal in every `⟨A, A^x⟩` but not in `S₅` (Tyutyanov).
Wielandt's theorem gives the affirmative answer for the partition into single primes. Source: E. I.
Khukhro and V. D. Mazurov (eds.), Unsolved Problems in Group Theory: The Kourovka Notebook, 21st
issue, arXiv:1401.0300v49 (2026), Archive of Solved Problems, Problem 19.84 (A. N. Skiba);
resolution: V. N. Tyutyanov, letter of 28 August 2019, Kourovka Archive, Problem 19.84: No, not
always; in G = S₅ with σ = {2, 3} ∪ {5} the subgroup A = ⟨(12)⟩ is σ-subnormal in ⟨A, A^x⟩ for every
x but not σ-subnormal in G, https://arxiv.org/abs/1401.0300v49.
-/
public theorem_wanted sigmaSubnormalFromJoinsWithConjugates_refuted :
    ¬ sigmaSubnormalFromJoinsWithConjugates

end MathlibExt.GroupTheory.SigmaSubnormalJoinConjugateKourovka19Problem84Wanted
