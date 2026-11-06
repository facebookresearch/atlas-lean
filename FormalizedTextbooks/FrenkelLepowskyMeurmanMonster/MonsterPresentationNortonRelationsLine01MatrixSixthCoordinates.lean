/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/- Actual matrix and pair-short vanishing at the sixth and seventh first-line steps. -/
module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationNortonRelationsLine01ShortSixthCoordinates
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationNortonRelationsTrialityMatrixZero

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
set_option backward.isDefEq.respectTransparency false

/-- The actual physical matrix-coordinate projection. -/
noncomputable def monsterNortonMatrixProjection :
    GriessSpace →ₗ[ℝ] Matrix (Fin 24) (Fin 24) ℝ where
  toFun x := (griessConwayEncode x).1
  map_add' x y := congrArg (fun r : ConwayRawSpace => r.1)
    (griessConwayEncodeLinear.map_add x y)
  map_smul' c x := congrArg (fun r : ConwayRawSpace => r.1)
    (griessConwayEncodeLinear.map_smul c x)

private theorem matrix_short_zero (X : GriessShortIndex → ℝ) :
    monsterNortonMatrixProjection (griessConwayDecode (0, (X, 0))) = 0 := by
  change (griessConwayEncode (griessConwayDecode (0, (X, 0)))).1 = 0
  rw [griessConwayEncode_decode _ (by intros; rfl)]

private theorem matrix_tensor_zero (T : SpinIndex → Fin 24 → ℝ) :
    monsterNortonMatrixProjection (monsterNortonTensorLift T) = 0 := by
  change (griessConwayEncode (monsterNortonTensorLift T)).1 = 0
  rw [monsterNortonTensorLift_apply, griessConwayEncode_decode _ (by intros; rfl)]

private theorem source_pair_matrix_zero (a : Fin 64) (i : Fin 24) :
    monsterNortonMatrixProjection (monsterNortonLine01SourcePairAfterVInverseUV a i) = 0 := by
  rw [monsterNortonLine01SourcePairAfterVInverseUV, map_add, map_smul,
    matrix_short_zero, smul_zero, map_smul, map_smul, matrix_tensor_zero,
    smul_zero, smul_zero, add_zero]

/-- The complete actual sixth state has no matrix coordinate. -/
theorem monsterNortonLine01MatrixSixth_zero :
    monsterNortonMatrixProjection monsterNortonLine01TensorAfterVUExtraInverseVInverseUV = 0 := by
  rw [monsterNortonLine01TensorAfterVUExtraInverseVInverseUV, map_smul, map_sum]
  simp only [map_smul, map_sum, source_pair_matrix_zero, smul_zero, Finset.sum_const_zero]

private theorem output_not_pair (a : Fin 64) (k : Fin 16) (s : Fin 2) (p : Fin 276) :
    monsterNortonLine01ShortInverseOutput a k ≠ Sum.inl (s, p) := by
  unfold monsterNortonLine01ShortInverseOutput
  split_ifs <;> simp only [ne_eq, reduceCtorEq, not_false_eq_true]

/-- The complete actual sixth state has no pair-short coordinate. -/
theorem monsterNortonLine01PairSixth_zero (s : Fin 2) (p : Fin 276) :
    (griessConwayEncode monsterNortonLine01TensorAfterVUExtraInverseVInverseUV).2.1
      (Sum.inl (s, p)) = 0 := by
  change monsterNortonShortProjection monsterNortonLine01TensorAfterVUExtraInverseVInverseUV
    (Sum.inl (s, p)) = 0
  rw [monsterNortonLine01ShortSixth_coordinates]
  simp only [Pi.smul_apply, Finset.sum_apply, smul_eq_mul, Pi.single_apply,
    Ne.symm (output_not_pair _ _ _ _), ite_false, mul_zero, Finset.sum_const_zero]

/-- The next actual positive triality step has no physical matrix coordinate. -/
theorem monsterNortonLine01MatrixSeventh_zero (i j : Fin 24) :
    (griessConwayEncode (sExtra monsterNortonLine01TensorAfterVUExtraInverseVInverseUV)).1 i j =
      0 := by
  apply monsterNortonTensor_extra_matrix_zero _ _ monsterNortonLine01PairSixth_zero
  intro a b
  have h := congrArg (fun M : Matrix (Fin 24) (Fin 24) ℝ => M a b)
    monsterNortonLine01MatrixSixth_zero
  exact h

/-- The next actual positive triality step has no pair-short coordinate. -/
theorem monsterNortonLine01PairSeventh_zero (s : Fin 2) (p : Fin 276) :
    (griessConwayEncode (sExtra monsterNortonLine01TensorAfterVUExtraInverseVInverseUV)).2.1
      (Sum.inl (s, p)) = 0 := by
  apply monsterNortonTensor_extra_pair_short_zero _ _ monsterNortonLine01PairSixth_zero
  intro a b
  exact congrArg (fun M : Matrix (Fin 24) (Fin 24) ℝ => M a b)
    monsterNortonLine01MatrixSixth_zero

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
