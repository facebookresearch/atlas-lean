/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisRootEightMoverMatePositiveFibers
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.LeechConcreteGeneration

/-! The full original positive mate matrix on every genuine coordinate frame. -/
@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 8000000

/-- The complete literal original mate permutation, in physical coordinate order. -/
def generatedRootEightMateSpatialPermutation : Fin 24 → Fin 24 :=
  ![1, 0, 23, 21, 4, 9, 11, 7, 8, 5, 10, 6, 12, 13, 18, 17, 16, 15, 14, 19, 22, 3, 20, 2]

private theorem mate_permutation_certificate : ∀ j : Fin 24,
    golayGeneratingWordArray leechNormSixHS100MatePermutationWord j =
      generatedRootEightMateSpatialPermutation j := by
  decide +kernel

/-- The literal permutation agrees with the genuine original Golay word at every coordinate. -/
theorem generatedRootEight_mate_spatial_permutation (j : Fin 24) :
    leechNormSixHS100MatePermutation.val j = generatedRootEightMateSpatialPermutation j := by
  simp only [leechNormSixHS100MatePermutation, leechRootedA2GeneratingWord_apply]
  exact mate_permutation_certificate j

/-- All original mate entries have their exact integer numerator over eight. -/
def generatedRootEightMateSpatialNumerator (i j : Fin 24) : ℤ :=
  if i = generatedRootEightMateSpatialPermutation j then -8 else 0

/-- The complete original mate sends each genuine integral coordinate frame to its literal signed frame. -/
theorem generatedRootEight_mate_spatial_frame (j : Fin 24) :
    (leechIntegralAction leechNormSixHS100MateOrientation (leechCoordinateFrameLattice j)).val =
      fun i => generatedRootEightMateSpatialNumerator i j := by
  rw [leechNormSixHS100MateOrientation, map_mul, LinearEquiv.mul_apply,
    leechRootNegationCode_action]
  have hp := leechNormSixHS100Permutation_action leechNormSixHS100MatePermutation
    (leechCoordinateFrameLattice j)
  simp only [Submodule.coe_neg, hp]
  funext i
  have he : leechNormSixHS100MatePermutation.val.symm i = j ↔
      i = generatedRootEightMateSpatialPermutation j := by
    rw [Equiv.symm_apply_eq, generatedRootEight_mate_spatial_permutation]
  change -((Pi.single j 8 : Fin 24 → ℤ) (leechNormSixHS100MatePermutation.val.symm i)) =
    if i = generatedRootEightMateSpatialPermutation j then -8 else 0
  simp only [Pi.single_apply, he]
  split_ifs <;> norm_num


/-- Every actual real mate matrix entry is retained by the complete integer spatial cache. -/
theorem generatedRootEight_mate_spatial_matrix (i j : Fin 24) :
    leechIsomMatrix leechNormSixHS100MateOrientation i j =
      (generatedRootEightMateSpatialNumerator i j : ℝ) / 8 := by
  have h := congrArg leechCoordinateEmbedding (generatedRootEight_mate_spatial_frame j)
  rw [leechIntegralAction_embedding] at h
  have hf : leechCoordinateEmbedding (leechCoordinateFrameLattice j).val =
      (8 / Real.sqrt 8 : ℝ) • Pi.single j 1 := by
    funext l
    by_cases hl : l = j <;>
      simp [leechCoordinateEmbedding, leechCoordinateFrameLattice, leechCoordinateFrameVector, hl]
  rw [hf, map_smul] at h
  have hi := congrFun h i
  change (8 / Real.sqrt 8 : ℝ) * leechIsomMatrix leechNormSixHS100MateOrientation i j =
      (generatedRootEightMateSpatialNumerator i j : ℝ) / Real.sqrt 8 at hi
  have hs : Real.sqrt 8 ≠ 0 := by positivity
  field_simp [hs] at hi
  linarith

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
