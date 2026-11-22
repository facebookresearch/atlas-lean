/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Shifted restricted sumsets in sets of positive density (Erdős Problem 656)

Erdős Problem 656: let `A ⊆ ℕ` be a set with positive upper density. Must there exist an infinite
set `B ⊆ A` and integer `t` such that `{b₁ + b₂ : b₁ ≠ b₂ ∈ B} + t ⊆ A`?
-/

module

public import Batteries.Util.ProofWanted
public import MathlibExt.Data.Set.Density

@[expose] public section

namespace MathlibExt.Combinatorics.DensityRestrictedSumsetShiftErdosProblem656Wanted

/-!
Source: T. F. Bloom, Erdős Problems, Problem #656, https://www.erdosproblems.com/656 (status
PROVED). UnsolvedMath record UM-30006971 (`EP-656`), dataset ulamai/UnsolvedMath v1.8.0.

Positive upper density is `0 < A.upperDensity`, with MathlibExt's `Set.upperDensity` (the limsup
of `|A ∩ [0, N)| / N`; whether `0 ∈ ℕ` does not matter); the shift `t` is an integer, and each `b₁ +
b₂ + t` is required to be an element of `A`.
-/

/-- Erdős Problem 656: if `A ⊆ ℕ` has positive upper density, then there are an infinite `B ⊆ A`
and an integer `t` with `b₁ + b₂ + t ∈ A` for all distinct `b₁, b₂ ∈ B`. -/
def restrictedSumsetShiftInDenseSet : Prop :=
  ∀ A : Set ℕ, 0 < A.upperDensity →
    ∃ B ⊆ A, B.Infinite ∧ ∃ t : ℤ, ∀ b₁ ∈ B, ∀ b₂ ∈ B, b₁ ≠ b₂ →
      ∃ a ∈ A, (a : ℤ) = b₁ + b₂ + t

/--
Resolved true: Kra, Moreira, Richter and Robertson proved that every set `A` of natural numbers with
positive upper density can be shifted to contain the restricted sumset `{b₁ + b₂ : b₁, b₂ ∈ B, b₁ ≠
b₂}` for some infinite `B ⊆ A`; erdosproblems.com/656 lists the problem as proved. Source: T. F.
Bloom, Erdős Problems, Problem #656, https://www.erdosproblems.com/656 (status PROVED); resolution:
B. Kra, J. Moreira, F. K. Richter and D. Robertson, A proof of Erdős's B + B + t conjecture, Commun.
Am. Math. Soc. (2024), 480-494, arXiv:2206.12377, abstract: every set A of natural numbers with
positive upper density can be shifted to contain the restricted sumset {b₁ + b₂ : b₁, b₂ ∈ B, b₁ ≠
b₂} for some infinite set B ⊂ A, https://arxiv.org/abs/2206.12377.
-/
public theorem_wanted restrictedSumsetShiftInDenseSet_holds : restrictedSumsetShiftInDenseSet

end MathlibExt.Combinatorics.DensityRestrictedSumsetShiftErdosProblem656Wanted
