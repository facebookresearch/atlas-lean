/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/- The actual complete sixth tensor state is antisymmetric in its low and high spin labels. -/
module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationNortonRelationsLine01CompactTensorColumns
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationNortonRelationsLine01CompactInverse
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationNortonRelationsLine01CompactV
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationNortonRelationsTensorAntisymmetricTriality

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
set_option backward.isDefEq.respectTransparency false

private theorem high_flip_low (d : Fin 2048) :
    monsterNortonLine01CompactHighFlip ⟨d.val, by omega⟩ = ⟨d.val + 2048, by omega⟩ := by
  apply Fin.ext
  simp only [monsterNortonLine01CompactHighFlip, d.isLt, ite_true]

/-- The actual integer column reached at the sixth word step is high/low antisymmetric. -/
theorem monsterNortonLine01CompactTensorSpin_high (k : Fin 16) (d : Fin 2048) :
    monsterNortonLine01CompactTensorSpin k ⟨d.val + 2048, by omega⟩ =
      -monsterNortonLine01CompactTensorSpin k ⟨d.val, by omega⟩ := by
  rw [monsterNortonLine01CompactTensorSpin, monsterNortonLine01CompactInverse_actual]
  have h := monsterNortonLine01CompactV_output_high k ⟨d.val, by omega⟩
  rwa [high_flip_low] at h

private theorem rank_one_high (k : Fin 16) (b : Fin 24 → ℝ) (d : Fin 2048) (i : Fin 24) :
    monsterNortonTensorProjection
      (monsterNortonTensorRankOne b (nortonUIntegerEmbed (monsterNortonLine01CompactTensorSpin k)))
        (golayLabelCoefficients ⟨d.val + 2048, by omega⟩) i =
      -monsterNortonTensorProjection
        (monsterNortonTensorRankOne b
          (nortonUIntegerEmbed (monsterNortonLine01CompactTensorSpin k)))
          (golayLabelCoefficients ⟨d.val, by omega⟩) i := by
  simp only [monsterNortonTensorProjection_rank_one, conwayTensorCoordinates_tmul,
    nortonUIntegerEmbed, nortonUIntegerLabel_coeff,
    monsterNortonLine01CompactTensorSpin_high, Int.cast_neg, neg_mul]

/-- The full actual sixth Griess state has an antisymmetric physical tensor coordinate. -/
theorem monsterNortonLine01TensorSixth_high (d : Fin 2048) (i : Fin 24) :
    (griessConwayEncode monsterNortonLine01TensorAfterVUExtraInverseVInverseUV).2.2
      (golayLabelCoefficients ⟨d.val + 2048, by omega⟩) i =
        -(griessConwayEncode monsterNortonLine01TensorAfterVUExtraInverseVInverseUV).2.2
          (golayLabelCoefficients ⟨d.val, by omega⟩) i := by
  change monsterNortonTensorProjection _ _ i = -monsterNortonTensorProjection _ _ i
  rw [monsterNortonLine01TensorSixth_columns]
  simp only [Pi.smul_apply, smul_eq_mul, Finset.sum_apply, rank_one_high,
    mul_neg, Finset.sum_neg_distrib]

/-- The seventh actual extra step has no odd-short coordinate, for the complete reached state. -/
theorem monsterNortonLine01TensorSeventh_odd_short_zero (d : Fin 2048) (i : Fin 24) :
    (griessConwayEncode (sExtra monsterNortonLine01TensorAfterVUExtraInverseVInverseUV)).2.1
      (Sum.inr (Sum.inr (d, i))) = 0 := by
  exact monsterNortonTensor_extra_odd_short_zero _ monsterNortonLine01TensorSixth_high d i

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
