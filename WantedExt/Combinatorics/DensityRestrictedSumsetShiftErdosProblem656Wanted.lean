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

/-- **Erdős Problem 656 (shifted restricted sumsets in dense sets).** The statement that for every
set $A$ of natural numbers with positive upper density, that is, with
$\limsup_{N \to \infty} |A \cap \{0, \dots, N - 1\}| / N > 0$, there are an infinite set
$B \subseteq A$ and an integer $t$ such that $b_1 + b_2 + t \in A$ for all distinct
$b_1, b_2 \in B$. -/
def restrictedSumsetShiftInDenseSet : Prop :=
  ∀ A : Set ℕ, 0 < A.upperDensity →
    ∃ B ⊆ A, B.Infinite ∧ ∃ t : ℤ, ∀ b₁ ∈ B, ∀ b₂ ∈ B, b₁ ≠ b₂ →
      ∃ a ∈ A, (a : ℤ) = b₁ + b₂ + t

/--
**Erdős Problem 656 is true.** For every set $A$ of natural numbers with positive upper density,
that is, with $\limsup_{N \to \infty} |A \cap \{0, \dots, N - 1\}| / N > 0$, there are an infinite
set $B \subseteq A$ and an integer $t$ such that $b_1 + b_2 + t \in A$ for all distinct
$b_1, b_2 \in B$.

This is the theorem of Kra, Moreira, Richter and Robertson.

Source: T. F.
Bloom, Erdős Problems, Problem #656, https://www.erdosproblems.com/656 (status PROVED); resolution:
B. Kra, J. Moreira, F. K. Richter and D. Robertson, A proof of Erdős's B + B + t conjecture, Commun.
Am. Math. Soc. (2024), 480-494, arXiv:2206.12377, abstract: every set A of natural numbers with
positive upper density can be shifted to contain the restricted sumset {b₁ + b₂ : b₁, b₂ ∈ B, b₁ ≠
b₂} for some infinite set B ⊂ A, https://arxiv.org/abs/2206.12377.
-/
public theorem_wanted restrictedSumsetShiftInDenseSet_holds : restrictedSumsetShiftInDenseSet

end MathlibExt.Combinatorics.DensityRestrictedSumsetShiftErdosProblem656Wanted
