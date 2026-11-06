/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationSixthMiddleOddPackedData
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationSixthMiddleOddCoverage

/-! The compact middle odd-short numerator is bound to every actual original coordinate. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
set_option backward.isDefEq.respectTransparency false

/-- Every middle odd-short coordinate outside the complete displayed support is genuinely zero. -/
theorem generatedSixth_middle_odd_zero_outside (d : Fin 2048) (i : Fin 24)
    (h : ¬ ∃ k : Fin 276, generatedSixthMiddleOddOutput k = Sum.inr (Sum.inr (d, i))) :
    (griessConwayEncode
      (rhoLocal (localFiberIntoH generatedSixthLocalFiber) generatedOddAxis)).2.1
        (Sum.inr (Sum.inr (d, i))) = 0 := by
  apply generatedSixth_middle_short_zero
  rintro ⟨⟨s, p⟩, hp⟩
  obtain ⟨k, hk⟩ := generatedSixth_middle_odd_actual_source s p d i hp
  have he := generatedSixth_middle_odd_permutation k
  rw [hk] at he
  exact h ⟨k, he.symm.trans hp⟩

/-- Every actual middle odd-short coefficient is the checked executable signed quarter numerator. -/
theorem generatedSixth_middle_odd_packed_coefficient (d : Fin 2048) (i : Fin 24) :
    (griessConwayEncode
      (rhoLocal (localFiberIntoH generatedSixthLocalFiber) generatedOddAxis)).2.1
        (Sum.inr (Sum.inr (d, i))) =
      (generatedSixthMiddleOddPackedNumerator d i : ℝ) / 4 := by
  by_cases h : ∃ k : Fin 276, generatedSixthMiddleOddTargetCoordinates k = (d, i)
  · obtain ⟨k, hk⟩ := h
    have ho : generatedSixthMiddleOddOutput k = Sum.inr (Sum.inr (d, i)) := by
      unfold generatedSixthMiddleOddOutput
      rw [hk]
    rw [← ho, generatedSixth_middle_odd_coefficient]
    have hn := generatedSixth_middle_odd_packed_value k
    rw [hk] at hn
    rw [hn]
  · have hz : generatedSixthMiddleOddPackedNumerator d i = 0 := by
      by_contra hn
      exact h (generatedSixth_middle_odd_packed_support d i hn)
    rw [hz, Int.cast_zero, zero_div]
    apply generatedSixth_middle_odd_zero_outside
    rintro ⟨k, hk⟩
    exact h ⟨k, Sum.inr.inj (Sum.inr.inj hk)⟩

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
