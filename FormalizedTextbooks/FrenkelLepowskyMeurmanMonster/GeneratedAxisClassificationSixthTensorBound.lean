/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationSixthSpinOrbitBound
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationSixthTrialityTensor
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.TrialityPairTensor

/-! A genuine pointwise bound on the outgoing contribution from the middle Y tensor. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
set_option backward.isDefEq.respectTransparency false

/-- The original outgoing Y contribution, scaled by the common tensor denominator. -/
def generatedSixthTensorYContribution (t : SpinIndex) (j : Fin 24) : ℝ :=
  16 * Real.sqrt 2 *
    qSign (golayMaskWeight (golayEncodedMask (spinDictionaryCode t).val) / 4 : ℕ) *
    (if (golayEncodedMask (spinDictionaryCode t).val).testBit j.val then -1 else 1) *
    ((griessConwayEncode
      (rhoLocal (localFiberIntoH generatedSixthLocalFiber) generatedOddAxis)).2.2
        (golayLabelCoefficients ⟨(spinDictionaryCode t).val, by omega⟩) j -
     (griessConwayEncode
      (rhoLocal (localFiberIntoH generatedSixthLocalFiber) generatedOddAxis)).2.2
        (golayLabelCoefficients ⟨(spinDictionaryCode t).val + 2048, by omega⟩) j)

/-- The scaled Y contribution is the original spin difference times the exact spatial column. -/
theorem generatedSixth_tensor_Y_state (t : SpinIndex) (j : Fin 24) :
    generatedSixthTensorYContribution t j =
      -16 * (generatedSixthFrameVectorData 8 0 j : ℝ) *
        qSign (golayMaskWeight (golayEncodedMask (spinDictionaryCode t).val) / 4 : ℕ) *
        (if (golayEncodedMask (spinDictionaryCode t).val).testBit j.val then -1 else 1) *
        (generatedSixthSpinState
          (golayLabelCoefficients ⟨(spinDictionaryCode t).val, by omega⟩) -
         generatedSixthSpinState
          (golayLabelCoefficients ⟨(spinDictionaryCode t).val + 2048, by omega⟩)) := by
  unfold generatedSixthTensorYContribution
  rw [generatedSixth_middle_tensor_rank_one, generatedSixth_middle_tensor_rank_one]
  change 16 * Real.sqrt 2 * _ * _ *
    (generatedOddTensorScale * generatedSixthSpinState _ *
      leechIsomMatrix generatedSixthLocalFiber.val.2 j 0 -
     generatedOddTensorScale * generatedSixthSpinState _ *
      leechIsomMatrix generatedSixthLocalFiber.val.2 j 0) = _
  rw [generatedSixth_forward_matrix_coordinate]
  unfold generatedOddTensorScale
  have hn : Real.sqrt 2 ≠ 0 := by positivity
  field_simp [hn]
  ring

/-- Every genuine outgoing Y contribution is bounded by its exact integer spatial column. -/
theorem generatedSixth_tensor_Y_square_bound (t : SpinIndex) (j : Fin 24) :
    (generatedSixthTensorYContribution t j) ^ 2 ≤
      (generatedSixthFrameVectorData 8 0 j : ℝ) ^ 2 := by
  rw [generatedSixth_tensor_Y_state]
  have hb := generatedSixth_spin_state_omega_difference_bound
    (golayLabelCoefficients ⟨(spinDictionaryCode t).val, by omega⟩)
  rw [golayLabel_low_add_omega] at hb
  have hs : (qSign
    (golayMaskWeight (golayEncodedMask (spinDictionaryCode t).val) / 4 : ℕ)) ^ 2 = 1 := by
    rw [pow_two, qSign_sq]
  have he : ((if (golayEncodedMask (spinDictionaryCode t).val).testBit j.val
      then -1 else 1) : ℝ) ^ 2 = 1 := by split_ifs <;> norm_num
  simp only [mul_pow, hs, he, mul_one]
  have hf : 0 ≤ (generatedSixthFrameVectorData 8 0 j : ℝ) ^ 2 := sq_nonneg _
  have hm := mul_le_mul_of_nonneg_left hb hf
  nlinarith only [hm]

/-- Column sixteen has outgoing Y contribution of absolute value at most three. -/
theorem generatedSixth_tensor_Y_sixteen_bound (t : SpinIndex) :
    (generatedSixthTensorYContribution t 16) ^ 2 ≤ 9 := by
  have h := generatedSixth_tensor_Y_square_bound t 16
  have hc : generatedSixthFrameVectorData 8 0 16 = -3 := by decide +kernel
  rw [hc] at h
  norm_num at h
  exact h

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
