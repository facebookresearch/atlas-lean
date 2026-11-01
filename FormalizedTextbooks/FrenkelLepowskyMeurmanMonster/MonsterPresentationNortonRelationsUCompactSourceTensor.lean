/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/- Exact compact actual Norton transport of every source Y/Z tensor basis vector. -/
module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationNortonRelationsUCompactSourceSpin
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationNortonRelationsUCompactTensor

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

private theorem generated_tensor (x : GriessSpace) :
    (griessConwayEncode (y555NortonActualU.val x)).2.2 =
      localTensorRepresentation monsterNortonUFiber (griessConwayEncode x).2.2 := by
  rw [← monsterNortonULocal_generated]
  change (griessConwayEncode (localGriessRepresentation monsterNortonUFiber x)).2.2 = _
  rw [localGriessRepresentation_encode, localConwayRawRepresentation_tensor]

/-- Every actual source Y vector has the compact spin expansion times its genuine Leech column. -/
theorem monsterNortonUCompactSourceYTensor (d : Fin 2048) (j i : Fin 24) (t : SpinIndex) :
    (griessConwayEncode (y555NortonActualU.val
      (trialityXYZBasis 1 (finProdFinEquiv (d,j))))).2.2 t i =
      ((((if (golayEncodedMask d.val).testBit j.val then (-1 : ℝ) else 1) / Real.sqrt 2) •
        (monsterNortonUCompactBasisExpansion (golayLabelCoefficients ⟨d.val, by omega⟩) -
          monsterNortonUCompactBasisExpansion
            (golayLabelCoefficients ⟨d.val + 2048, by omega⟩))) t) *
        monsterNortonUFiber.val.2.val (Pi.single j 1) i := by
  rw [generated_tensor, griessConwayEncode_Y_basis, trialityYTensor_column,
    tensor_column, conwayTensorCoordinates_tmul, monsterNortonUCompactSourceYSpin]

/-- Every actual source Z vector has the analogous exact sum of two compact spin expansions. -/
theorem monsterNortonUCompactSourceZTensor (d : Fin 2048) (j i : Fin 24) (t : SpinIndex) :
    (griessConwayEncode (y555NortonActualU.val
      (trialityXYZBasis 2 (finProdFinEquiv (d,j))))).2.2 t i =
      (((qSign (golayMaskWeight (golayEncodedMask d.val) / 4 : ℕ) / Real.sqrt 2) •
        (monsterNortonUCompactBasisExpansion (golayLabelCoefficients ⟨d.val, by omega⟩) +
          monsterNortonUCompactBasisExpansion
            (golayLabelCoefficients ⟨d.val + 2048, by omega⟩))) t) *
        monsterNortonUFiber.val.2.val (Pi.single j 1) i := by
  rw [generated_tensor, griessConwayEncode_Z_basis, trialityZTensor_column,
    tensor_column, conwayTensorCoordinates_tmul, monsterNortonUCompactSourceZSpin]

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
