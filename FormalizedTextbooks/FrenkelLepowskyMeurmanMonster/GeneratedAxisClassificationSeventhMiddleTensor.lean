/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationSeventhSpinPauliState
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationSeventhSpatial
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationOddLocalFixed

/-! The genuine middle tensor of the seventh prototype has an exact integral numerator. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
set_option backward.isDefEq.respectTransparency false

/-- The original local image carries the genuine two-point state and first coordinate vector. -/
theorem generatedSeventh_middle_tensor_rank_one (t : SpinIndex) (j : Fin 24) :
    (griessConwayEncode
      (rhoLocal (localFiberIntoH generatedSeventhLocalFiber) generatedOddAxis)).2.2 t j =
      generatedOddTensorScale *
        generatedSeventhLocalFiber.val.1.val (generatedOddSpinState 0 1 0) t *
        generatedSeventhLocalFiber.val.2.val (Pi.single (0 : Fin 24) 1) j := by
  change (griessConwayEncode
    (localGriessRepresentation generatedSeventhLocalFiber generatedOddAxis)).2.2 t j = _
  rw [localGriessRepresentation_encode, localConwayRawRepresentation_apply]
  change localTensorRepresentation generatedSeventhLocalFiber
    (griessConwayEncode generatedOddAxis).2.2 t j = _
  rw [generatedOddAxis_tensor_tmul, map_smul, localTensorRepresentation_coordinates]
  change (generatedOddTensorScale • conwayTensorCoordinates
    (TensorProduct.congr generatedSeventhLocalFiber.val.1.val
      generatedSeventhLocalFiber.val.2.val
      ((generatedOddSpinState 0 1 0) ⊗ₜ[ℝ] Pi.single (0 : Fin 24) 1))) t j = _
  rw [TensorProduct.congr_tmul]
  simp only [Pi.smul_apply, smul_eq_mul, conwayTensorCoordinates_tmul]
  ring

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
