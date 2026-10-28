/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/- Exact integer physical coordinates for the complete sixth first-line tensor state. -/
module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationNortonRelationsLine01TensorSixthAntisymmetric
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationNortonRelationsUInversePhysicalMatrix

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
set_option backward.isDefEq.respectTransparency false

/-- The entire true sixth physical tensor numerator in source spin-label coordinates. -/
def monsterNortonLine01TensorSixthIntegerNumerator (n : Fin 4096) (i : Fin 24) : ℤ :=
  ∑ k : Fin 16,
    monsterNortonUNumerator1 (monsterNortonLine01ShortPhysicalColumn k) 0 *
      nortonUIntegerQ y555NortonVQ (monsterNortonLine01CompactOutputVector k) n *
      monsterNortonUNumerator12 i (monsterNortonLine01ShortPhysicalColumn k)

/-- Every complete actual sixth tensor coordinate is given by the exact integer numerator. -/
theorem monsterNortonLine01TensorSixthInteger_actual (n : Fin 4096) (i : Fin 24) :
    (griessConwayEncode monsterNortonLine01TensorAfterVUExtraInverseVInverseUV).2.2
      (golayLabelCoefficients n) i =
        (-1 / (2048 * Real.sqrt 2) : ℝ) *
          (monsterNortonLine01TensorSixthIntegerNumerator n i : ℝ) := by
  change monsterNortonTensorProjection monsterNortonLine01TensorAfterVUExtraInverseVInverseUV
    (golayLabelCoefficients n) i = _
  rw [monsterNortonLine01TensorSixth_columns]
  simp only [Pi.smul_apply, smul_eq_mul, Finset.sum_apply,
    monsterNortonTensorProjection_rank_one, conwayTensorCoordinates_tmul,
    nortonUIntegerEmbed, nortonUIntegerLabel_coeff, monsterNortonLine01CompactTensorSpin,
    monsterNortonLine01CompactInverse_actual, monsterNortonUInversePhysicalMatrix_basis,
    monsterNortonLine01TensorSixthIntegerNumerator, Int.cast_sum, Int.cast_mul]
  simp only [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro k _
  have hs : Real.sqrt 2 ≠ 0 := ne_of_gt (Real.sqrt_pos.mpr (by norm_num))
  field_simp
  ring

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
