/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/- Full raw coordinates of the proposed next-U state, using genuine short and tensor inclusions. -/
module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationNortonRelationsLine01SeventhUTensorData
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationNortonRelationsLine01SeventhUShortData

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
set_option backward.isDefEq.respectTransparency false

private theorem rank_one_recover (b : Fin 24 → ℝ) (a : SpinSpace) :
    monsterNortonTensorLift (monsterNortonTensorProjection (monsterNortonTensorRankOne b a)) =
      monsterNortonTensorRankOne b a := by
  rw [monsterNortonTensorProjection_rank_one]
  rfl

private theorem tensor_vector_recover :
    monsterNortonTensorLift
      (monsterNortonTensorProjection monsterNortonLine01TensorSeventhUVector) =
      monsterNortonLine01TensorSeventhUVector := by
  rw [monsterNortonLine01TensorSeventhUVector]
  simp only [map_smul, map_sum, rank_one_recover]

/-- The proposed next-U tensor has zero matrix and short coordinates in the original decoder. -/
theorem monsterNortonLine01SeventhUTensor_encode :
    griessConwayEncode monsterNortonLine01TensorSeventhUVector =
      (0, (0, monsterNortonTensorProjection monsterNortonLine01TensorSeventhUVector)) := by
  conv_lhs => rw [← tensor_vector_recover]
  rw [monsterNortonTensorLift_apply, griessConwayEncode_decode _ (by intro i j; rfl)]

/-- The full proposed next-U state has its precise original short and tensor coordinates. -/
theorem monsterNortonLine01SeventhU_candidate_encode :
    griessConwayEncode
      (monsterNortonLine01ShortSeventhUVector + monsterNortonLine01TensorSeventhUVector) =
        (0, (monsterNortonLine01SeventhUShortCoordinates,
          monsterNortonTensorProjection monsterNortonLine01TensorSeventhUVector)) := by
  have hs : griessConwayEncode monsterNortonLine01ShortSeventhUVector =
      (0, (monsterNortonLine01SeventhUShortCoordinates, 0)) := by
    rw [← monsterNortonLine01SeventhUShortCoordinates_actual,
      monsterNortonShortLiftLinear_apply,
      griessConwayEncode_decode _ (by intro i j; rfl)]
  change griessConwayEncodeLinear (_ + _) = _
  rw [map_add]
  change griessConwayEncode _ + griessConwayEncode _ = _
  rw [hs, monsterNortonLine01SeventhUTensor_encode]
  simp only [Prod.mk_add_mk, zero_add, add_zero]

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
