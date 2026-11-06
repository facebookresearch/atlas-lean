/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/- The entire actual eleventh state in the literal first Norton line-pair word. -/
module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationNortonRelationsLine01EleventhTensorCoordinates
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationNortonRelationsLine01EleventhOddCoordinates
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationNortonRelationsLine01EleventhZeroCoordinates

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
set_option backward.isDefEq.respectTransparency false

/-- The complete eleventh Griess vector in genuine short and rank-one tensor coordinates. -/
noncomputable def monsterNortonLine01EleventhVector : GriessSpace :=
  monsterNortonShortLiftLinear ((1 / 2 : ℝ) •
    Pi.single (Sum.inr (Sum.inr ((82 : Fin 2048), (1 : Fin 24)))) 1) +
      monsterNortonLine01EleventhTensorVector

/-- The entire actual eleventh short projection is one half of the original X82 short unit. -/
theorem monsterNortonLine01Eleventh_short_projection :
    (griessConwayEncode (sExtra.symm (y555NortonActualU.val
      (sExtra monsterNortonLine01TensorAfterVUExtraInverseVInverseUV)))).2.1 =
        (1 / 2 : ℝ) • Pi.single (Sum.inr (Sum.inr ((82 : Fin 2048), (1 : Fin 24)))) 1 := by
  funext r
  rcases r with ⟨s, p⟩ | (⟨d, e⟩ | ⟨d, i⟩)
  · rw [monsterNortonLine01Eleventh_pair_zero]
    simp
  · rw [monsterNortonLine01Eleventh_octad_zero]
    simp
  · simpa [Pi.single_apply, Fin.ext_iff, mul_ite] using monsterNortonLine01EleventhOdd_actual d i

private theorem tensor_recover :
    monsterNortonTensorLift
      (monsterNortonTensorProjection monsterNortonLine01EleventhTensorVector) =
      monsterNortonLine01EleventhTensorVector := by
  rw [monsterNortonLine01EleventhTensorVector]
  simp only [map_smul, monsterNortonTensorProjection_rank_one]
  rfl

private theorem tensor_encode :
    griessConwayEncode monsterNortonLine01EleventhTensorVector =
      (0, (0, monsterNortonTensorProjection monsterNortonLine01EleventhTensorVector)) := by
  conv_lhs => rw [← tensor_recover]
  rw [monsterNortonTensorLift_apply, griessConwayEncode_decode _ (by intro i j; rfl)]

/-- This is an equality of entire actual Griess vectors after the eleventh literal word step. -/
theorem monsterNortonLine01Eleventh_actual :
    sExtra.symm (y555NortonActualU.val
      (sExtra monsterNortonLine01TensorAfterVUExtraInverseVInverseUV)) =
        monsterNortonLine01EleventhVector := by
  have he : griessConwayEncode monsterNortonLine01EleventhVector =
      (0, ((1 / 2 : ℝ) • Pi.single (Sum.inr (Sum.inr ((82 : Fin 2048), (1 : Fin 24)))) 1,
        monsterNortonTensorProjection monsterNortonLine01EleventhTensorVector)) := by
    rw [monsterNortonLine01EleventhVector]
    change griessConwayEncodeLinear (_ + _) = _
    rw [map_add]
    change griessConwayEncode _ + griessConwayEncode _ = _
    rw [monsterNortonShortLiftLinear_apply,
      griessConwayEncode_decode _ (by intro i j; rfl), tensor_encode]
    simp only [Prod.mk_add_mk, zero_add, add_zero]
  apply (Function.LeftInverse.injective griessConwayDecode_encode)
  rw [he]
  refine Prod.ext ?_ (Prod.ext monsterNortonLine01Eleventh_short_projection
    monsterNortonLine01EleventhTensor_projection)
  ext i j
  exact monsterNortonLine01Eleventh_matrix_zero i j

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
