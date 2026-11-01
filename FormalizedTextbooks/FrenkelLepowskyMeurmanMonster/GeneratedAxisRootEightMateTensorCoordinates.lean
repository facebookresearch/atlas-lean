/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisRootEightMateTensorActions
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisRootEightMateSpatialAction

/-! Actual mate tensor coordinates and complete integer fixation predicate. -/
@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 100000

/-- The literal spatial inverse retains every original physical coordinate. -/
def generatedRootEightMateTensorSpatialInverse : Fin 24 → Fin 24 :=
  ![1, 0, 23, 21, 4, 9, 11, 7, 8, 5, 10, 6, 12, 13, 18, 17, 16, 15, 14, 19, 22, 3, 20, 2]

/-- Complete finite inverse identity for the actual original spatial permutation. -/
theorem generatedRootEight_mate_tensor_spatial_inverse (i : Fin 24) :
    leechNormSixHS100MatePermutation.val.symm i = generatedRootEightMateTensorSpatialInverse i := by
  apply Equiv.injective leechNormSixHS100MatePermutation.val
  rw [Equiv.apply_symm_apply, generatedRootEight_mate_spatial_permutation]
  have h : ∀ i : Fin 24, generatedRootEightMateSpatialPermutation
    (generatedRootEightMateTensorSpatialInverse i) = i := by decide +kernel
  exact (h i).symm

/-- The actual corrected mate retains its original negative spatial orientation. -/
theorem generatedRootEight_mate_tensor_spatial : generatedRootEightMateCorrectedFiber.val.2 =
    leechNormSixHS100MateOrientation := by
  change generatedRootEightMatePositiveFiber.val.2 = _
  exact generatedRootEight_mate_positive_spatial

/-- Every original physical matrix coefficient is the negative permutation coefficient. -/
theorem generatedRootEight_mate_tensor_spatial_coordinate (i j : Fin 24) :
    generatedRootEightMateCorrectedFiber.val.2.val (Pi.single j 1) i =
      -(Pi.single j 1 : Fin 24 → ℝ) (generatedRootEightMateTensorSpatialInverse i) := by
  rw [generatedRootEight_mate_tensor_spatial]
  change leechIsomMatrix leechNormSixHS100MateOrientation i j = _
  rw [generatedRootEight_mate_spatial_matrix]
  have he : i = generatedRootEightMateSpatialPermutation j ↔
      generatedRootEightMateTensorSpatialInverse i = j := by
    rw [← generatedRootEight_mate_spatial_permutation,
      ← generatedRootEight_mate_tensor_spatial_inverse, Equiv.symm_apply_eq]
  simp only [generatedRootEightMateSpatialNumerator, Pi.single_apply, he]
  split_ifs <;> norm_num

/-- The whole actual tensor action is the signed original spin address and negative physical permutation. -/
theorem generatedRootEight_mate_tensor_coordinate
    (h : ∀ n, generatedRootEightMateTensorAddressCondition n)
    (T : SpinIndex → Fin 24 → ℝ) (t : SpinIndex) (i : Fin 24) :
    localTensorRepresentation generatedRootEightMateCorrectedFiber T t i =
      -(generatedRootEightMateTensorPostSign (nortonUIntegerLabel t) : ℝ) *
      (generatedRootEightMateTensorPreSign
        (generatedRootEightMateTensorPostLabel (nortonUIntegerLabel t)) : ℝ) *
      T (golayLabelCoefficients (generatedRootEightMateTensorPreLabel
        (generatedRootEightMateTensorPostLabel (nortonUIntegerLabel t))))
          (generatedRootEightMateTensorSpatialInverse i) := by
  rw [generatedAxisGlobalTensor_local_coordinate]
  simp_rw [generatedRootEight_mate_tensor_spin_coordinate h,
    generatedRootEight_mate_tensor_spatial_coordinate]
  simp only [Pi.single_apply, mul_neg]
  simp

/-- Complete original cache fixation includes every zero coordinate. -/
def generatedRootEightMateTensorCacheCondition (n : Fin 4096) (i : Fin 24) : Prop :=
  -generatedRootEightMateTensorPostSign n *
    generatedRootEightMateTensorPreSign (generatedRootEightMateTensorPostLabel n) *
    generatedRootEightCanonicalTensorRawCache
      (generatedRootEightMateTensorPreLabel (generatedRootEightMateTensorPostLabel n))
      (generatedRootEightMateTensorSpatialInverse i) = generatedRootEightCanonicalTensorRawCache n i

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
