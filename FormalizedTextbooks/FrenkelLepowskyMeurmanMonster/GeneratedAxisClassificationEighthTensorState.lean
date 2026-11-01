/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationEighthQSupportSquares
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationEighthSpatial
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationOddLocalFixed

/-! The genuine middle tensor of the eighth prototype has an exact integral numerator. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
set_option backward.isDefEq.respectTransparency false

/-- The original local image carries the genuine two-point state and first coordinate vector. -/
theorem generatedEighth_middle_tensor_rank_one (t : SpinIndex) (j : Fin 24) :
    (griessConwayEncode
      (rhoLocal (localFiberIntoH generatedEighthLocalFiber) generatedOddAxis)).2.2 t j =
      generatedOddTensorScale *
        generatedEighthLocalFiber.val.1.val (generatedOddSpinState 0 1 0) t *
        generatedEighthLocalFiber.val.2.val (Pi.single (0 : Fin 24) 1) j := by
  change (griessConwayEncode
    (localGriessRepresentation generatedEighthLocalFiber generatedOddAxis)).2.2 t j = _
  rw [localGriessRepresentation_encode, localConwayRawRepresentation_apply]
  change localTensorRepresentation generatedEighthLocalFiber
    (griessConwayEncode generatedOddAxis).2.2 t j = _
  rw [generatedOddAxis_tensor_tmul, map_smul, localTensorRepresentation_coordinates]
  change (generatedOddTensorScale • conwayTensorCoordinates
    (TensorProduct.congr generatedEighthLocalFiber.val.1.val
      generatedEighthLocalFiber.val.2.val
      ((generatedOddSpinState 0 1 0) ⊗ₜ[ℝ] Pi.single (0 : Fin 24) 1))) t j = _
  rw [TensorProduct.congr_tmul]
  simp only [Pi.smul_apply, smul_eq_mul, conwayTensorCoordinates_tmul]
  ring

/-- The original outgoing Y contribution, scaled by the common tensor denominator. -/
def generatedEighthTensorYContribution (t : SpinIndex) (j : Fin 24) : ℝ :=
  16 * Real.sqrt 2 *
    qSign (golayMaskWeight (golayEncodedMask (spinDictionaryCode t).val) / 4 : ℕ) *
    (if (golayEncodedMask (spinDictionaryCode t).val).testBit j.val then -1 else 1) *
    ((griessConwayEncode
      (rhoLocal (localFiberIntoH generatedEighthLocalFiber) generatedOddAxis)).2.2
        (golayLabelCoefficients ⟨(spinDictionaryCode t).val, by omega⟩) j -
     (griessConwayEncode
      (rhoLocal (localFiberIntoH generatedEighthLocalFiber) generatedOddAxis)).2.2
        (golayLabelCoefficients ⟨(spinDictionaryCode t).val + 2048, by omega⟩) j)

/-- The scaled Y contribution is the original spin difference times the exact spatial column. -/
theorem generatedEighth_tensor_Y_state (t : SpinIndex) (j : Fin 24) :
    generatedEighthTensorYContribution t j =
      -16 * (generatedEighthFrameVectorData 7 0 j : ℝ) *
        qSign (golayMaskWeight (golayEncodedMask (spinDictionaryCode t).val) / 4 : ℕ) *
        (if (golayEncodedMask (spinDictionaryCode t).val).testBit j.val then -1 else 1) *
        (generatedEighthSpinState
          (golayLabelCoefficients ⟨(spinDictionaryCode t).val, by omega⟩) -
         generatedEighthSpinState
          (golayLabelCoefficients ⟨(spinDictionaryCode t).val + 2048, by omega⟩)) := by
  unfold generatedEighthTensorYContribution
  rw [generatedEighth_middle_tensor_rank_one, generatedEighth_middle_tensor_rank_one]
  change 16 * Real.sqrt 2 * _ * _ *
    (generatedOddTensorScale * generatedEighthSpinState _ *
      leechIsomMatrix generatedEighthLocalFiber.val.2 j 0 -
     generatedOddTensorScale * generatedEighthSpinState _ *
      leechIsomMatrix generatedEighthLocalFiber.val.2 j 0) = _
  rw [generatedEighth_forward_matrix_coordinate]
  unfold generatedOddTensorScale
  have hn : Real.sqrt 2 ≠ 0 := by positivity
  field_simp [hn]
  ring

/-- In the original twentieth column the outgoing Y contribution always has square four. -/
theorem generatedEighth_tensor_Y_twenty_square (t : SpinIndex) :
    (generatedEighthTensorYContribution t 20) ^ 2 = 4 := by
  have hd := generatedEighth_spin_omega_difference_square
    (golayLabelCoefficients ⟨(spinDictionaryCode t).val, by omega⟩)
  rw [golayLabel_low_add_omega] at hd
  rw [generatedEighth_tensor_Y_state]
  have hv : generatedEighthFrameVectorData 7 0 20 = 4 := by decide +kernel
  simp only [hv, Int.cast_ofNat]
  rw [mul_pow, mul_pow, mul_pow, mul_pow, hd, pow_two (qSign _), qSign_sq]
  split_ifs <;> norm_num

/-- Both coordinates of every original omega pair retain the same outgoing Y contribution. -/
theorem generatedEighth_tensor_Y_omega (t : SpinIndex) :
    generatedEighthTensorYContribution (t + Pi.single (11 : Fin 12) 1) 20 =
      generatedEighthTensorYContribution t 20 := by
  unfold generatedEighthTensorYContribution
  simp only [spinDictionaryCode_add_omega]

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
