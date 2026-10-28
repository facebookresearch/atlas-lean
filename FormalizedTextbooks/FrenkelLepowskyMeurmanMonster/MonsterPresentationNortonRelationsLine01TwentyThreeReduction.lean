/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/- The literal first-line square reduced to twenty-three concrete commutation checks. -/
module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationNortonRelationsLine01TensorSquareFixed
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationNortonRelationsTwentyThreeGlobalIdentity

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
set_option backward.isDefEq.respectTransparency false

private theorem normalized_start :
    monsterNortonLine01TensorStart =
      (1 / Real.sqrt 2 : ℝ) • monsterNortonTwentyThreeTensorVector := by
  have hc : golayLabelCoefficients (0 : Fin 4096) = 0 := by decide +kernel
  rw [monsterNortonLine01TensorStart, monsterNortonIntegralTensorVector_first_column,
    monsterNortonUIntegerEmbed_single, hc, monsterNortonTensorLift_apply]
  rfl

private theorem normalized_fixed (g : G)
    (h : g.val monsterNortonLine01TensorStart = monsterNortonLine01TensorStart) :
    g.val monsterNortonTwentyThreeTensorVector = monsterNortonTwentyThreeTensorVector := by
  rw [normalized_start, map_smul] at h
  have he := congrArg (fun x : GriessSpace => (Real.sqrt 2 : ℝ) • x) h
  rw [smul_smul, smul_smul] at he
  have hc : Real.sqrt 2 * (1 / Real.sqrt 2) = 1 := by
    have hn : Real.sqrt 2 ≠ 0 := by positivity
    field_simp
  rw [hc, one_smul, one_smul] at he
  exact he

/-- The entire normalized delta-zero tensor test for the actual first line-difference square. -/
theorem monsterNortonLineZeroOneSquare_twentyThreeTensor_fixed :
    ((y555NortonLine monsterSourceTriality 0 *
      (y555NortonLine monsterSourceTriality 1)⁻¹) ^ 2).val monsterNortonTwentyThreeTensorVector =
        monsterNortonTwentyThreeTensorVector :=
  normalized_fixed _ monsterNortonLineZeroOneSquare_tensor_fixed

/-- Only the stated twenty-three concrete commutation checks remain for this actual square. -/
theorem monsterNortonLineZeroOneSquare_of_twentyThree
    (hi : ∀ i : Fin 24, i ≠ 23 →
      Commute ((y555NortonLine monsterSourceTriality 0 *
        (y555NortonLine monsterSourceTriality 1)⁻¹) ^ 2)
          (qIntoGenerated (qCoordinateGenerator i))) :
    (y555NortonLine monsterSourceTriality 0 *
      (y555NortonLine monsterSourceTriality 1)⁻¹) ^ 2 = 1 :=
  monsterNortonGenerated_twentyThree_global_identity _ hi
    monsterNortonLineZeroOneSquare_twentyThreeTensor_fixed

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
