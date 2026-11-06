/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationSixthSpinCircuit
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationSixthSpatial
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationOddLocalFixed

/-! The genuine middle tensor of the sixth prototype has an exact integral numerator. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
set_option backward.isDefEq.respectTransparency false

/-- The original local image carries the genuine two-point state and first coordinate vector. -/
theorem generatedSixth_middle_tensor_rank_one (t : SpinIndex) (j : Fin 24) :
    (griessConwayEncode
      (rhoLocal (localFiberIntoH generatedSixthLocalFiber) generatedOddAxis)).2.2 t j =
      generatedOddTensorScale *
        generatedSixthLocalFiber.val.1.val (generatedOddSpinState 0 1 0) t *
        generatedSixthLocalFiber.val.2.val (Pi.single (0 : Fin 24) 1) j := by
  change (griessConwayEncode
    (localGriessRepresentation generatedSixthLocalFiber generatedOddAxis)).2.2 t j = _
  rw [localGriessRepresentation_encode, localConwayRawRepresentation_apply]
  change localTensorRepresentation generatedSixthLocalFiber
    (griessConwayEncode generatedOddAxis).2.2 t j = _
  rw [generatedOddAxis_tensor_tmul, map_smul, localTensorRepresentation_coordinates]
  change (generatedOddTensorScale • conwayTensorCoordinates
    (TensorProduct.congr generatedSixthLocalFiber.val.1.val
      generatedSixthLocalFiber.val.2.val
      ((generatedOddSpinState 0 1 0) ⊗ₜ[ℝ] Pi.single (0 : Fin 24) 1))) t j = _
  rw [TensorProduct.congr_tmul]
  simp only [Pi.smul_apply, smul_eq_mul, conwayTensorCoordinates_tmul]
  ring

/-- All actual middle tensor coefficients follow from the exact eight-factor spin circuit. -/
theorem generatedSixth_middle_tensor_integer (t : SpinIndex) (j : Fin 24) :
    (griessConwayEncode
      (rhoLocal (localFiberIntoH generatedSixthLocalFiber) generatedOddAxis)).2.2 t j =
      -((generatedSixthIntegerSpinNumerator (nortonUIntegerLabel t) : ℝ) *
        (generatedSixthFrameVectorData 8 0 j : ℝ)) / (512 * Real.sqrt 2) := by
  rw [generatedSixth_middle_tensor_rank_one, generatedSixth_integer_spin_numerator_actual]
  change generatedOddTensorScale *
    ((1 / 512 : ℝ) * nortonUIntegerEmbed generatedSixthIntegerSpinNumerator t) *
    leechIsomMatrix generatedSixthLocalFiber.val.2 j 0 = _
  rw [generatedSixth_forward_matrix_coordinate]
  simp only [generatedOddTensorScale, nortonUIntegerEmbed]
  ring

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
