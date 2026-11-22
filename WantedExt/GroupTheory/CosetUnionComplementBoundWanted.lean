/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.Algebra.Group.Subgroup.Basic
import Mathlib.SetTheory.Cardinal.Finite
import Batteries.Util.ProofWanted

/-!
# Complements of finite unions of group cosets

Kourovka Notebook Problem 21.115 asks whether the complement of a non-covering union of `n`
left-or-right cosets in a finite group has at least a `2⁻ⁿ` proportion of the group.
-/

namespace MathlibExt.GroupTheory.CosetUnionComplementBoundWanted

/-- `C` is a left coset or a right coset of some subgroup of `G`. -/
def IsLeftOrRightCoset {G : Type} [Group G] (C : Set G) : Prop :=
  ∃ (H : Subgroup G) (g : G),
    C = { x : G | g⁻¹ * x ∈ H } ∨ C = { x : G | x * g⁻¹ ∈ H }

/-- If `n` left-or-right cosets do not cover a finite group, their complement has size at least
the group order divided by `2 ^ n`. -/
def conjecture : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (n : ℕ) (C : Fin n → Set G),
    (∀ i, IsLeftOrRightCoset (C i)) →
      (∃ x : G, ∀ i, x ∉ C i) →
        Nat.card G ≤ 2 ^ n * Nat.card { x : G // ∀ i, x ∉ C i }

/--
Resolved true: Resolved affirmatively: B. Sambale (arXiv:2609.09052, 2026), Theorem 1, proves
that if left or right cosets C₁, …, Cₙ of subgroups of a group G leave A = G ∖ (C₁ ∪ ⋯ ∪ Cₙ)
nonempty, then G is the union of at most 2ⁿ left translates of A, so |A| ≥ |G|/2ⁿ for finite G.
The Kourovka Notebook (arXiv:1401.0300v49) marks Problem 21.115 solved (AI-found proof confirmed
by Sambale, and Sambale's preprint). Source: B. Sambale, On the complement of a union of cosets,
arXiv:2609.09052 (2026), https://arxiv.org/abs/2609.09052; E. I. Khukhro and V. D. Mazurov
(eds.), Unsolved Problems in Group Theory: The Kourovka Notebook, 21st issue, arXiv:1401.0300v49
(20 October 2026), Problem 21.115, https://arxiv.org/abs/1401.0300v49. Moved from
`OpenConjectures/GroupTheory/CosetUnionComplementBound`.
-/
theorem_wanted conjecture_holds : conjecture

end MathlibExt.GroupTheory.CosetUnionComplementBoundWanted
