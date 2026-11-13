/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Probability.Statistics.WithinEstimator

/-!
# Tests for the within estimator and the dummy-variable regression

Four observations in two groups with one regressor, `x = (1, 3, 2, 6)`, `y = (2, 7, 5, 12)`:
the LSDV solution is `α = (7/10, 9/10)`, `β = 19/10`, the within Gram matrix is `10`, and
`lsdv_slope_eq_within_estimator` recovers `β` as the within estimator. A singleton group has a
zero within-demeaned row.
-/

@[expose] public section

open Finset Matrix ProbabilityTheory MathlibExt.Probability.Statistics.WithinEstimator

namespace MathlibExtTest.Probability.Statistics.WithinEstimator

lemma lsdv_hD_aux :
    ((groupDummy (![0, 0, 1, 1] : Fin 4 → Fin 2))ᵀ *ᵥ
      ((![2, 7, 5, 12] : Fin 4 → ℝ) - groupDummy (![0, 0, 1, 1] : Fin 4 → Fin 2) *ᵥ
        (![7/10, 9/10] : Fin 2 → ℝ) -
        (Matrix.of fun i _ => (![1, 3, 2, 6] : Fin 4 → ℝ) i : Matrix (Fin 4) (Fin 1) ℝ) *ᵥ
        (![19/10] : Fin 1 → ℝ))) = 0 := by
  funext g
  fin_cases g
  · simp only [Pi.zero_apply]
    unfold groupDummy
    simp only [Matrix.mulVec, dotProduct, Matrix.transpose_apply, Matrix.of_apply,
      Pi.sub_apply]
    rw [Fin.sum_univ_four]
    norm_num
  · simp only [Pi.zero_apply]
    unfold groupDummy
    simp only [Matrix.mulVec, dotProduct, Matrix.transpose_apply, Matrix.of_apply,
      Pi.sub_apply]
    rw [Fin.sum_univ_four]
    norm_num

lemma lsdv_hX_aux :
    (Matrix.of fun i _ => (![1, 3, 2, 6] : Fin 4 → ℝ) i : Matrix (Fin 4) (Fin 1) ℝ)ᵀ *ᵥ
      ((![2, 7, 5, 12] : Fin 4 → ℝ) - groupDummy (![0, 0, 1, 1] : Fin 4 → Fin 2) *ᵥ
        (![7/10, 9/10] : Fin 2 → ℝ) -
        (Matrix.of fun i _ => (![1, 3, 2, 6] : Fin 4 → ℝ) i : Matrix (Fin 4) (Fin 1) ℝ) *ᵥ
        (![19/10] : Fin 1 → ℝ)) = 0 := by
  funext j
  fin_cases j
  simp only [Pi.zero_apply]
  unfold groupDummy
  simp only [Matrix.mulVec, dotProduct, Matrix.transpose_apply, Matrix.of_apply,
    Pi.sub_apply]
  rw [Fin.sum_univ_four]
  norm_num

-- Test 1: both LSDV normal equations
theorem lsdv_normal_eq_test :
    ((groupDummy (![0, 0, 1, 1] : Fin 4 → Fin 2))ᵀ *ᵥ
      ((![2, 7, 5, 12] : Fin 4 → ℝ) - groupDummy (![0, 0, 1, 1] : Fin 4 → Fin 2) *ᵥ
        (![7/10, 9/10] : Fin 2 → ℝ) -
        (Matrix.of fun i _ => (![1, 3, 2, 6] : Fin 4 → ℝ) i : Matrix (Fin 4) (Fin 1) ℝ) *ᵥ
        (![19/10] : Fin 1 → ℝ))) = 0 ∧
    (Matrix.of fun i _ => (![1, 3, 2, 6] : Fin 4 → ℝ) i : Matrix (Fin 4) (Fin 1) ℝ)ᵀ *ᵥ
      ((![2, 7, 5, 12] : Fin 4 → ℝ) - groupDummy (![0, 0, 1, 1] : Fin 4 → Fin 2) *ᵥ
        (![7/10, 9/10] : Fin 2 → ℝ) -
        (Matrix.of fun i _ => (![1, 3, 2, 6] : Fin 4 → ℝ) i : Matrix (Fin 4) (Fin 1) ℝ) *ᵥ
        (![19/10] : Fin 1 → ℝ)) = 0 :=
  ⟨lsdv_hD_aux, lsdv_hX_aux⟩

-- Test 2 helpers: group means for X column
lemma meanX_g0_aux : groupMean (![0, 0, 1, 1] : Fin 4 → Fin 2)
    (fun k => (![1, 3, 2, 6] : Fin 4 → ℝ) k) 0 = 2 := by
  unfold groupMean
  have hsum : (∑ i with (![0, 0, 1, 1] : Fin 4 → Fin 2) i = 0,
      (![1, 3, 2, 6] : Fin 4 → ℝ) i) = 4 := by
    have h : (∑ i with (![0, 0, 1, 1] : Fin 4 → Fin 2) i = 0,
        (![1, 3, 2, 6] : Fin 4 → ℝ) i) =
        ∑ i ∈ Finset.univ.filter (fun i => (![0, 0, 1, 1] : Fin 4 → Fin 2) i = 0),
          (![1, 3, 2, 6] : Fin 4 → ℝ) i := rfl
    rw [h, Finset.sum_filter, Fin.sum_univ_four]
    simp
    norm_num
  have hcard : (#{i | (![0, 0, 1, 1] : Fin 4 → Fin 2) i = 0} : ℕ) = 2 := rfl
  simp only [] at hsum ⊢
  rw [hsum, hcard]
  norm_num

lemma meanX_g1_aux : groupMean (![0, 0, 1, 1] : Fin 4 → Fin 2)
    (fun k => (![1, 3, 2, 6] : Fin 4 → ℝ) k) 1 = 4 := by
  unfold groupMean
  have hsum : (∑ i with (![0, 0, 1, 1] : Fin 4 → Fin 2) i = 1,
      (![1, 3, 2, 6] : Fin 4 → ℝ) i) = 8 := by
    have h : (∑ i with (![0, 0, 1, 1] : Fin 4 → Fin 2) i = 1,
        (![1, 3, 2, 6] : Fin 4 → ℝ) i) =
        ∑ i ∈ Finset.univ.filter (fun i => (![0, 0, 1, 1] : Fin 4 → Fin 2) i = 1),
          (![1, 3, 2, 6] : Fin 4 → ℝ) i := rfl
    rw [h, Finset.sum_filter, Fin.sum_univ_four]
    simp
    norm_num
  have hcard : (#{i | (![0, 0, 1, 1] : Fin 4 → Fin 2) i = 1} : ℕ) = 2 := rfl
  simp only [] at hsum ⊢
  rw [hsum, hcard]
  norm_num

-- Within matrix entries
lemma withinMat_entry00_aux : (withinMat (![0, 0, 1, 1] : Fin 4 → Fin 2)
    (Matrix.of fun i _ => (![1, 3, 2, 6] : Fin 4 → ℝ) i :
      Matrix (Fin 4) (Fin 1) ℝ)) 0 0 = -1 := by
  unfold withinMat
  simp only [Matrix.of_apply]
  have hx : (![1, 3, 2, 6] : Fin 4 → ℝ) 0 = 1 := rfl
  have hg : (![0, 0, 1, 1] : Fin 4 → Fin 2) 0 = 0 := rfl
  rw [hx, hg, meanX_g0_aux]
  norm_num

lemma withinMat_entry10_aux : (withinMat (![0, 0, 1, 1] : Fin 4 → Fin 2)
    (Matrix.of fun i _ => (![1, 3, 2, 6] : Fin 4 → ℝ) i :
      Matrix (Fin 4) (Fin 1) ℝ)) 1 0 = 1 := by
  unfold withinMat
  simp only [Matrix.of_apply]
  have hx : (![1, 3, 2, 6] : Fin 4 → ℝ) 1 = 3 := rfl
  have hg : (![0, 0, 1, 1] : Fin 4 → Fin 2) 1 = 0 := rfl
  rw [hx, hg, meanX_g0_aux]
  norm_num

lemma withinMat_entry20_aux : (withinMat (![0, 0, 1, 1] : Fin 4 → Fin 2)
    (Matrix.of fun i _ => (![1, 3, 2, 6] : Fin 4 → ℝ) i :
      Matrix (Fin 4) (Fin 1) ℝ)) 2 0 = -2 := by
  unfold withinMat
  simp only [Matrix.of_apply]
  have hx : (![1, 3, 2, 6] : Fin 4 → ℝ) 2 = 2 := rfl
  have hg : (![0, 0, 1, 1] : Fin 4 → Fin 2) 2 = 1 := rfl
  rw [hx, hg, meanX_g1_aux]
  norm_num

lemma withinMat_entry30_aux : (withinMat (![0, 0, 1, 1] : Fin 4 → Fin 2)
    (Matrix.of fun i _ => (![1, 3, 2, 6] : Fin 4 → ℝ) i :
      Matrix (Fin 4) (Fin 1) ℝ)) 3 0 = 2 := by
  unfold withinMat
  simp only [Matrix.of_apply]
  have hx : (![1, 3, 2, 6] : Fin 4 → ℝ) 3 = 6 := rfl
  have hg : (![0, 0, 1, 1] : Fin 4 → Fin 2) 3 = 1 := rfl
  rw [hx, hg, meanX_g1_aux]
  norm_num

-- Gram matrix entry = 10
lemma gram_entry_aux : (((withinMat (![0, 0, 1, 1] : Fin 4 → Fin 2)
    (Matrix.of fun i _ => (![1, 3, 2, 6] : Fin 4 → ℝ) i :
      Matrix (Fin 4) (Fin 1) ℝ))ᵀ *
    withinMat (![0, 0, 1, 1] : Fin 4 → Fin 2)
    (Matrix.of fun i _ => (![1, 3, 2, 6] : Fin 4 → ℝ) i :
      Matrix (Fin 4) (Fin 1) ℝ)) 0 0) = 10 := by
  simp only [Matrix.mul_apply, Matrix.transpose_apply]
  rw [Fin.sum_univ_four]
  rw [withinMat_entry00_aux, withinMat_entry10_aux, withinMat_entry20_aux,
    withinMat_entry30_aux]
  norm_num

lemma gram_det_aux : (((withinMat (![0, 0, 1, 1] : Fin 4 → Fin 2)
    (Matrix.of fun i _ => (![1, 3, 2, 6] : Fin 4 → ℝ) i :
      Matrix (Fin 4) (Fin 1) ℝ))ᵀ *
    withinMat (![0, 0, 1, 1] : Fin 4 → Fin 2)
    (Matrix.of fun i _ => (![1, 3, 2, 6] : Fin 4 → ℝ) i :
      Matrix (Fin 4) (Fin 1) ℝ)).det) = 10 := by
  rw [Matrix.det_fin_one]
  exact gram_entry_aux

lemma gram_isUnit_aux : IsUnit (((withinMat (![0, 0, 1, 1] : Fin 4 → Fin 2)
    (Matrix.of fun i _ => (![1, 3, 2, 6] : Fin 4 → ℝ) i :
      Matrix (Fin 4) (Fin 1) ℝ))ᵀ *
    withinMat (![0, 0, 1, 1] : Fin 4 → Fin 2)
    (Matrix.of fun i _ => (![1, 3, 2, 6] : Fin 4 → ℝ) i :
      Matrix (Fin 4) (Fin 1) ℝ)).det) := by
  rw [gram_det_aux]
  exact isUnit_iff_ne_zero.mpr (by norm_num)

-- Test 2: within estimator equals dummy-variable coefficient
theorem lsdv_within_estimator_test :
    (![19/10] : Fin 1 → ℝ) = (((withinMat (![0, 0, 1, 1] : Fin 4 → Fin 2)
      (Matrix.of fun i _ => (![1, 3, 2, 6] : Fin 4 → ℝ) i :
        Matrix (Fin 4) (Fin 1) ℝ))ᵀ *
      withinMat (![0, 0, 1, 1] : Fin 4 → Fin 2)
      (Matrix.of fun i _ => (![1, 3, 2, 6] : Fin 4 → ℝ) i :
        Matrix (Fin 4) (Fin 1) ℝ))⁻¹ *ᵥ
      (((withinMat (![0, 0, 1, 1] : Fin 4 → Fin 2)
        (Matrix.of fun i _ => (![1, 3, 2, 6] : Fin 4 → ℝ) i :
          Matrix (Fin 4) (Fin 1) ℝ))ᵀ *ᵥ
        withinVec (![0, 0, 1, 1] : Fin 4 → Fin 2) (![2, 7, 5, 12] : Fin 4 → ℝ)))) := by
  exact lsdv_slope_eq_within_estimator _ lsdv_hD_aux lsdv_hX_aux gram_isUnit_aux

-- Test 3: singleton-group probe
theorem singleton_withinVec_test :
    withinVec (![0, 0, 0, 1] : Fin 4 → Fin 2) (![2, 7, 5, 12] : Fin 4 → ℝ) 3 = 0 := by
  unfold withinVec
  have hy : (![2, 7, 5, 12] : Fin 4 → ℝ) 3 = 12 := rfl
  have hg : (![0, 0, 0, 1] : Fin 4 → Fin 2) 3 = 1 := rfl
  rw [hy, hg]
  have hmean : groupMean (![0, 0, 0, 1] : Fin 4 → Fin 2)
      (![2, 7, 5, 12] : Fin 4 → ℝ) 1 = 12 := by
    unfold groupMean
    have hsum : (∑ i with (![0, 0, 0, 1] : Fin 4 → Fin 2) i = 1,
        (![2, 7, 5, 12] : Fin 4 → ℝ) i) = 12 := by
      have h : (∑ i with (![0, 0, 0, 1] : Fin 4 → Fin 2) i = 1,
          (![2, 7, 5, 12] : Fin 4 → ℝ) i) =
          ∑ i ∈ Finset.univ.filter (fun i => (![0, 0, 0, 1] : Fin 4 → Fin 2) i = 1),
            (![2, 7, 5, 12] : Fin 4 → ℝ) i := rfl
      rw [h, Finset.sum_filter, Fin.sum_univ_four]
      simp
    have hcard : (#{i | (![0, 0, 0, 1] : Fin 4 → Fin 2) i = 1} : ℕ) = 1 := rfl
    rw [hsum, hcard]
    norm_num
  rw [hmean]
  norm_num

private def converseGroups : Fin 4 → Fin 3 := ![0, 0, 1, 1]

private def converseDesign : Matrix (Fin 4) (Fin 2) ℝ :=
  !![1, 0; 3, 0; 0, 2; 0, 6]

private def converseResponse : Fin 4 → ℝ := ![7, 11, 13, 25]

/-- Two regressors satisfy the within equations despite an unused third group. -/
private theorem two_regressor_within_normal_eq_test :
    ((withinMat converseGroups converseDesign)ᵀ *
      withinMat converseGroups converseDesign) *ᵥ (![2, 3] : Fin 2 → ℝ) =
      (withinMat converseGroups converseDesign)ᵀ *ᵥ
        withinVec converseGroups converseResponse := by
  have hu4 : (Finset.univ : Finset (Fin 4)) = {0, 1, 2, 3} := by decide
  ext j
  fin_cases j <;>
    norm_num [withinMat, withinVec, groupMean, converseGroups, converseDesign,
      converseResponse, Matrix.mulVec, Matrix.mul_apply, dotProduct,
      hu4, Finset.filter_insert, Finset.filter_singleton, Fin.sum_univ_succ]

/-- The converse chooses zero for the unused group's intercept. -/
private theorem converse_intercepts_test :
    (fun g => groupMean converseGroups converseResponse g -
      ∑ j, groupMean converseGroups (fun k => converseDesign k j) g *
        (![2, 3] : Fin 2 → ℝ) j) = (![5, 7, 0] : Fin 3 → ℝ) := by
  have hu4 : (Finset.univ : Finset (Fin 4)) = {0, 1, 2, 3} := by decide
  ext g
  fin_cases g <;>
    norm_num [groupMean, converseGroups, converseDesign, converseResponse,
      hu4, Finset.filter_insert, Finset.filter_singleton, Fin.sum_univ_succ]

/-- The converse theorem supplies both LSDV blocks for the checked intercepts. -/
private theorem lsdv_converse_unused_group_test :
    (groupDummy converseGroups)ᵀ *ᵥ
      (converseResponse - groupDummy converseGroups *ᵥ ![5, 7, 0] -
        converseDesign *ᵥ (![2, 3] : Fin 2 → ℝ)) = 0 ∧
      converseDesignᵀ *ᵥ
        (converseResponse - groupDummy converseGroups *ᵥ ![5, 7, 0] -
          converseDesign *ᵥ (![2, 3] : Fin 2 → ℝ)) = 0 := by
  have h := lsdv_normal_eq_of_within_normal_eq converseGroups
    two_regressor_within_normal_eq_test
  rwa [converse_intercepts_test] at h

end MathlibExtTest.Probability.Statistics.WithinEstimator
