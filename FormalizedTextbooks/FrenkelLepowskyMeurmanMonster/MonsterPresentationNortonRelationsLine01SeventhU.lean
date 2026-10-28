/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/- Full actual Norton U transport after the seventh first-line word step. -/
module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationNortonRelationsLine01SeventhForward
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationNortonRelationsLine01SeventhUTensorData
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationNortonRelationsLine01TensorSeventhColumns
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationNortonRelationsTensorColumnAction
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationNortonRelationsLine01ShortSeventhU

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
set_option backward.isDefEq.respectTransparency false

private theorem scalar_factor : (1 / (4096 * Real.sqrt 2) : ℝ) * 64 =
    1 / (64 * Real.sqrt 2) := by
  field_simp
  ring

/-- This finite tensor vector is the entire actual next-U tensor contribution. -/
theorem monsterNortonLine01TensorSeventhU_actual :
    y555NortonActualU.val (monsterNortonTensorLift
      (griessConwayEncode (sExtra monsterNortonLine01TensorAfterVUExtraInverseVInverseUV)).2.2) =
        monsterNortonLine01TensorSeventhUVector := by
  rw [monsterNortonLine01TensorSeventh_columns]
  simp only [map_smul, map_sum, monsterNortonU_tensor_column,
    monsterNortonLine01SeventhForward_spin_actual]
  rw [← Finset.smul_sum, smul_smul, scalar_factor]
  rfl

private theorem split_pure (X : GriessShortIndex → ℝ) (T : SpinIndex → Fin 24 → ℝ) :
    griessConwayDecode (0, (X, T)) =
      monsterNortonShortLiftLinear X + monsterNortonTensorLift T := by
  rw [monsterNortonShortLiftLinear_apply, monsterNortonTensorLift_apply]
  change griessConwayDecodeLinear (0, (X, T)) =
    griessConwayDecodeLinear (0, (X, 0)) + griessConwayDecodeLinear (0, (0, T))
  rw [← map_add]
  congr 1
  simp only [Prod.mk_add_mk, zero_add, add_zero]

/-- The full actual next-U word state consists of the checked short and tensor contributions. -/
theorem monsterNortonLine01SeventhU_actual :
    y555NortonActualU.val (sExtra monsterNortonLine01TensorAfterVUExtraInverseVInverseUV) =
      monsterNortonLine01ShortSeventhUVector + monsterNortonLine01TensorSeventhUVector := by
  have hs : (griessConwayEncode
      (sExtra monsterNortonLine01TensorAfterVUExtraInverseVInverseUV)).1 = 0 := by
    rw [monsterNortonLine01TensorSeventh_actual]
    change (griessConwayEncode (griessConwayDecode (0, (_, _)))).1 = 0
    rw [griessConwayEncode_decode _ (by intro i j; rfl)]
  have he : griessConwayDecode (0,
      ((griessConwayEncode (sExtra monsterNortonLine01TensorAfterVUExtraInverseVInverseUV)).2.1,
        (griessConwayEncode (sExtra monsterNortonLine01TensorAfterVUExtraInverseVInverseUV)).2.2)) =
      sExtra monsterNortonLine01TensorAfterVUExtraInverseVInverseUV := by
    have h := griessConwayDecode_encode
      (sExtra monsterNortonLine01TensorAfterVUExtraInverseVInverseUV)
    have hp : griessConwayEncode
        (sExtra monsterNortonLine01TensorAfterVUExtraInverseVInverseUV) =
        (0, ((griessConwayEncode
          (sExtra monsterNortonLine01TensorAfterVUExtraInverseVInverseUV)).2.1,
            (griessConwayEncode
              (sExtra monsterNortonLine01TensorAfterVUExtraInverseVInverseUV)).2.2)) :=
      Prod.ext hs rfl
    rw [hp] at h
    exact h
  rw [split_pure] at he
  calc
    _ = y555NortonActualU.val (_ + _) := congrArg y555NortonActualU.val he.symm
    _ = _ := by
      rw [map_add, monsterNortonLine01ShortSeventhU_actual,
        monsterNortonLine01TensorSeventhU_actual]

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
