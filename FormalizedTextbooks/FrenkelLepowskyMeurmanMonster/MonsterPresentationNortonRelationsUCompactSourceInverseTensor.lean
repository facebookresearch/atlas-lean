/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/- Actual inverse Norton source tensor transport with its exact integral Gaussian numerator. -/
module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationNortonRelationsUCompactSourceInverse

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open scoped TensorProduct
set_option backward.isDefEq.respectTransparency false

private theorem tensor_column (f : localFiberSubgroup) (a : SpinSpace) (j : Fin 24) :
    localTensorRepresentation f (conwaySpinColumn a j) =
      conwayTensorCoordinates
        (f.val.1.val a ⊗ₜ[ℝ] f.val.2.val (Pi.single j 1)) := by
  have hc : conwaySpinColumn a j =
      conwayTensorCoordinates (a ⊗ₜ[ℝ] (Pi.single j 1 : Fin 24 → ℝ)) := by
    ext t i
    simp only [conwaySpinColumn, conwayTensorCoordinates_tmul, Pi.single_apply]
    by_cases h : i = j <;> simp [h]
  rw [hc, localTensorRepresentation_coordinates]
  change conwayTensorCoordinates
    (TensorProduct.congr f.val.1.val f.val.2.val
      (a ⊗ₜ[ℝ] (Pi.single j 1 : Fin 24 → ℝ))) = _
  rw [TensorProduct.congr_tmul]

private theorem generated_inverse_tensor (x : GriessSpace) :
    (griessConwayEncode ((y555NortonActualU⁻¹).val x)).2.2 =
      localTensorRepresentation monsterNortonUFiber⁻¹ (griessConwayEncode x).2.2 := by
  have hu : y555NortonActualU⁻¹ = localIntoGenerated monsterNortonULocal⁻¹ := by
    rw [map_inv, monsterNortonULocal_generated]
  rw [hu]
  change (griessConwayEncode (localGriessRepresentation monsterNortonUFiber⁻¹ x)).2.2 = _
  rw [localGriessRepresentation_encode, localConwayRawRepresentation_tensor]

/-- Every actual source Y tensor has this exact inverse Norton spin numerator and Leech column. -/
theorem monsterNortonUCompactSourceYTensor_inverse (d : Fin 2048) (j i : Fin 24)
    (t : SpinIndex) :
    (griessConwayEncode ((y555NortonActualU⁻¹).val
      (trialityXYZBasis 1 (finProdFinEquiv (d,j))))).2.2 t i =
      ((((if (golayEncodedMask d.val).testBit j.val then (-1 : ℝ) else 1) / Real.sqrt 2) •
        ((-1 / 8 : ℝ) • nortonUIntegerEmbed
          (monsterNortonUCompactInverseNumerator (monsterNortonSourceYInteger d)))) t) *
        (monsterNortonUFiber.val.2⁻¹).val (Pi.single j 1) i := by
  rw [generated_inverse_tensor, griessConwayEncode_Y_basis, trialityYTensor_column,
    tensor_column, conwayTensorCoordinates_tmul]
  change (monsterNortonUFiber.val.1⁻¹).val (trialityYSpin d j) t * _ = _
  rw [monsterNortonUCompactSourceYSpin_inverse]
  rfl

/-- Every actual source Z tensor has the corresponding exact inverse numerator. -/
theorem monsterNortonUCompactSourceZTensor_inverse (d : Fin 2048) (j i : Fin 24)
    (t : SpinIndex) :
    (griessConwayEncode ((y555NortonActualU⁻¹).val
      (trialityXYZBasis 2 (finProdFinEquiv (d,j))))).2.2 t i =
      (((qSign (golayMaskWeight (golayEncodedMask d.val) / 4 : ℕ) / Real.sqrt 2) •
        ((-1 / 8 : ℝ) • nortonUIntegerEmbed
          (monsterNortonUCompactInverseNumerator (monsterNortonSourceZInteger d)))) t) *
        (monsterNortonUFiber.val.2⁻¹).val (Pi.single j 1) i := by
  rw [generated_inverse_tensor, griessConwayEncode_Z_basis, trialityZTensor_column,
    tensor_column, conwayTensorCoordinates_tmul]
  change (monsterNortonUFiber.val.1⁻¹).val (trialityZSpin d) t * _ = _
  rw [monsterNortonUCompactSourceZSpin_inverse]
  rfl

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
