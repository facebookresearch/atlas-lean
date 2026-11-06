/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisSeventhXiPlaneTensorReturnData
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisSeventhXiPlaneGaussianSupport
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisSeventhXiPlaneTensorSupportParameters

/-! Exhaustive support checks imply equality of the entire original tensor numerator. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open scoped BigOperators

/-- The genuine support coverage and outside vanishing retain every original tensor coordinate. -/
theorem generatedSeventhXiPlaneTensorReturn_of_support_check
    (h : ∀ v : Fin 1024, ∀ j : Fin 24,
      generatedSeventhXiPlaneTensorReturnLeft (generatedSeventhXiTensorSupportLabel v) j =
        generatedSeventhXiPlaneTensorReturnRight (generatedSeventhXiTensorSupportLabel v) j)
    (d : Fin 4096) (j : Fin 24) :
    generatedSeventhXiPlaneTensorReturnLeft d j =
      4 * ∑ i : Fin 24, generatedSeventhXiPlaneTensorSpatialNumerator i j *
        generatedSeventhXiPlaneTensorPacked d i := by
  rw [← generatedSeventhXiPlaneTensorReturnRight_actual]
  by_cases hd : generatedSeventhXiTensorSupported d.val
  · rw [← generatedSeventhXiTensorSupportLabel_complete d hd]
    exact h _ j
  · have hl : generatedSeventhXiPlaneTensorReturnLeft d j = 0 := by
      unfold generatedSeventhXiPlaneTensorReturnLeft
      rw [generatedSeventhXiPlaneGaussianFast_eq]
      exact generatedSeventhXiPlaneGaussianPacked_tensor_zero d j hd
    rw [hl]
    symm
    unfold generatedSeventhXiPlaneTensorReturnRight
    apply mul_eq_zero_of_right
    apply Finset.sum_eq_zero
    intro k _
    rw [generatedSeventhXiPlaneTensorPacked_zero d _ hd, mul_zero]

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Every original integral spatial Gram coefficient is retained in this certificate.
/-- The complete original spatial numerator has Gram matrix four times identity. -/
theorem generatedSeventhXiPlaneTensorSpatialNumerator_gram : ∀ i k : Fin 24,
    (∑ j : Fin 24, generatedSeventhXiPlaneTensorSpatialNumerator i j *
      generatedSeventhXiPlaneTensorSpatialNumerator k j) = (if i = k then 4 else 0) := by
  decide +kernel

/-- Exact original column returns imply fixation of the full integral tensor numerator. -/
theorem generatedSeventhXiPlaneIntegerTensor_eq_sixteen
    (h : ∀ d : Fin 4096, ∀ j : Fin 24,
      generatedSeventhXiPlaneTensorReturnLeft d j =
        4 * ∑ i : Fin 24, generatedSeventhXiPlaneTensorSpatialNumerator i j *
          generatedSeventhXiPlaneTensorPacked d i) :
    generatedSeventhXiPlaneIntegerTensor generatedSeventhXiPlaneTensorPacked =
      fun d i => 16 * generatedSeventhXiPlaneTensorPacked d i := by
  funext d i
  have hs (j : Fin 24) : generatedSeventhXiPlaneIntegerSpin
      (fun x => generatedSeventhXiPlaneTensorPacked x j) d =
      4 * ∑ k : Fin 24, generatedSeventhXiPlaneTensorSpatialNumerator k j *
        generatedSeventhXiPlaneTensorPacked d k := by
    rw [generatedSeventhXiPlaneGaussianFast_actual]
    exact h d j
  change (∑ j : Fin 24, generatedSeventhXiPlaneTensorSpatialNumerator i j *
    generatedSeventhXiPlaneIntegerSpin (fun x => generatedSeventhXiPlaneTensorPacked x j) d) = _
  simp_rw [hs]
  calc
    _ = 4 * ∑ k : Fin 24,
        (∑ j : Fin 24, generatedSeventhXiPlaneTensorSpatialNumerator i j *
          generatedSeventhXiPlaneTensorSpatialNumerator k j) *
            generatedSeventhXiPlaneTensorPacked d k := by
      simp only [Finset.mul_sum, Finset.sum_mul]
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro k _
      apply Finset.sum_congr rfl
      intro j _
      ring
    _ = _ := by
      simp_rw [generatedSeventhXiPlaneTensorSpatialNumerator_gram]
      simp only [ite_mul, zero_mul, Finset.sum_ite_eq,
        Finset.mem_univ, ite_true]
      ring

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
