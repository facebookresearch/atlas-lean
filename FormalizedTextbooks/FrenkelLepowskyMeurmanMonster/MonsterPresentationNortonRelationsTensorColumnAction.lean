/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/- Exact local tensor-column transport for arbitrary genuine spin vectors. -/
module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationNortonRelationsUCompactSparseTensor

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open scoped TensorProduct
set_option backward.isDefEq.respectTransparency false

private theorem local_pure_tensor (f : localFiberSubgroup) (T : SpinIndex → Fin 24 → ℝ) :
    localGriessRepresentation f (monsterNortonTensorLift T) =
      monsterNortonTensorLift (localTensorRepresentation f T) := by
  apply (Function.LeftInverse.injective griessConwayDecode_encode)
  rw [monsterNortonTensorLift_apply, localGriessRepresentation_encode,
    griessConwayEncode_decode _ (by intros; rfl), monsterNortonTensorLift_apply,
    griessConwayEncode_decode _ (by intros; rfl)]
  rw [localConwayRawRepresentation_apply]
  simp only [map_zero]

/-- Every genuine local fiber element transports a spin column by its two actual factors. -/
theorem monsterNortonLocalTensor_column (f : localFiberSubgroup) (a : SpinSpace) (j : Fin 24) :
    localGriessRepresentation f (monsterNortonTensorLift (conwaySpinColumn a j)) =
      monsterNortonTensorRankOne (f.val.2.val (Pi.single j 1)) (f.val.1.val a) := by
  rw [local_pure_tensor]
  have hc : conwaySpinColumn a j =
      conwayTensorCoordinates (a ⊗ₜ[ℝ] (Pi.single j 1 : Fin 24 → ℝ)) := by
    ext t i
    simp only [conwaySpinColumn, conwayTensorCoordinates_tmul, Pi.single_apply]
    by_cases h : i = j <;> simp [h]
  rw [hc, localTensorRepresentation_coordinates]
  change monsterNortonTensorLift (conwayTensorCoordinates
    (TensorProduct.congr f.val.1.val f.val.2.val
      (a ⊗ₜ[ℝ] (Pi.single j 1 : Fin 24 → ℝ)))) = _
  rw [TensorProduct.congr_tmul]
  rfl

/-- The literal Norton word transports any pure column by its actual spin and Leech factors. -/
theorem monsterNortonU_tensor_column (a : SpinSpace) (j : Fin 24) :
    y555NortonActualU.val (monsterNortonTensorLift (conwaySpinColumn a j)) =
      monsterNortonTensorRankOne (monsterNortonUFiber.val.2.val (Pi.single j 1))
        (monsterNortonUFiber.val.1.val a) := by
  rw [← monsterNortonULocal_generated]
  change localGriessRepresentation monsterNortonUFiber
    (monsterNortonTensorLift (conwaySpinColumn a j)) = _
  exact monsterNortonLocalTensor_column _ _ _

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
