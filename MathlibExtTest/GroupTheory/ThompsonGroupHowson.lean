/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.GroupTheory.ThompsonGroupHowson

/-! # Tests for the presentation of Thompson's group and its Howson counterexample -/

namespace MathlibExtTest.GroupTheory.ThompsonGroupHowson

open MathlibExt.GroupTheory.ThompsonGroupHowsonKourovka19Problem40Wanted

-- The exponent of the second generator distinguishes the two generators in the quotient.
example : (PresentedGroup.of 0 : ThompsonF) ≠ PresentedGroup.of 1 := by
  let f : Fin 2 → Multiplicative ℤ := fun i => Multiplicative.ofAdd (i : ℕ)
  have hrel : ∀ r ∈ thompsonRelators, FreeGroup.lift f r = 1 := by
    intro r hr
    rcases hr with rfl | hr
    · simp [mul_comm, mul_left_comm]
    · obtain rfl := Set.mem_singleton_iff.mp hr
      simp [mul_comm, mul_left_comm]
  intro h
  have heq := congrArg (fun g => (PresentedGroup.toGroup hrel g).toAdd) h
  simp [f] at heq

-- Neither subgroup can contain the other, since the smaller subgroup would be the intersection.
example : ∃ H K : Subgroup ThompsonF,
    H.FG ∧ K.FG ∧ ¬ (H ⊓ K).FG ∧ ¬ H ≤ K ∧ ¬ K ≤ H := by
  obtain ⟨H, K, hH, hK, hHK⟩ : ∃ H K : Subgroup ThompsonF, H.FG ∧ K.FG ∧ ¬ (H ⊓ K).FG := by
    by_contra! h
    exact thompsonFHowson_refuted h
  exact ⟨H, K, hH, hK, hHK, fun h => hHK ((inf_eq_left.mpr h).symm ▸ hH),
    fun h => hHK ((inf_eq_right.mpr h).symm ▸ hK)⟩

end MathlibExtTest.GroupTheory.ThompsonGroupHowson
