/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Probability.Statistics.LinearModel.NestedF
import Mathlib.LinearAlgebra.Matrix.Notation

/-! # Tests for the nested-model `F` statistic -/

namespace MathlibExtTest.LinearModelNestedF

open Matrix MeasureTheory ProbabilityTheory MathlibExt.Probability.Statistics.LinearModel

/-- Unrestricted design with columns `![1, 1, 1]` and `![0, 1, 2]`. -/
def Xₙ : Matrix (Fin 3) (Fin 2) ℝ := !![1, 0; 1, 1; 1, 2]

/-- Restricted design: the first column of `Xₙ`. -/
def X₀ₙ : Matrix (Fin 3) (Fin 1) ℝ := !![1; 1; 1]

/-- Response vector. -/
def yₙ : Fin 3 → ℝ := ![0, 0, 1]

theorem hXX : Xₙᵀ * Xₙ = !![3, 3; 3, 5] := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Xₙ, Matrix.mul_apply, Fin.sum_univ_three, Matrix.transpose_apply,
      Matrix.of_apply] <;>
    norm_num

theorem hX0X0 : X₀ₙᵀ * X₀ₙ = !![3] := by
  ext i j
  fin_cases i
  fin_cases j
  simp [X₀ₙ, Matrix.mul_apply, Fin.sum_univ_three, Matrix.transpose_apply,
    Matrix.of_apply]
  norm_num

theorem hBA : !![5/6, -1/2; -1/2, 1/2] * !![3, 3; 3, 5]
    = (1 : Matrix (Fin 2) (Fin 2) ℝ) := by
  ext i j
  by_cases h : i = j
  · rw [h, Matrix.one_apply_eq]
    fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two, Matrix.of_apply] <;>
      norm_num
  · rw [Matrix.one_apply_ne h]
    fin_cases i <;> fin_cases j <;>
      simp_all [Matrix.mul_apply, Fin.sum_univ_two, Matrix.of_apply] <;>
      norm_num

theorem hAB : !![3, 3; 3, 5] * !![5/6, -1/2; -1/2, 1/2]
    = (1 : Matrix (Fin 2) (Fin 2) ℝ) := by
  ext i j
  by_cases h : i = j
  · rw [h, Matrix.one_apply_eq]
    fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two, Matrix.of_apply] <;>
      norm_num
  · rw [Matrix.one_apply_ne h]
    fin_cases i <;> fin_cases j <;>
      simp_all [Matrix.mul_apply, Fin.sum_univ_two, Matrix.of_apply] <;>
      norm_num

theorem hB0A0 : !![1/3] * !![3] = (1 : Matrix (Fin 1) (Fin 1) ℝ) := by
  ext i j
  by_cases h : i = j
  · rw [h, Matrix.one_apply_eq]
    fin_cases j
    simp [Matrix.mul_apply, Matrix.of_apply]
  · rw [Matrix.one_apply_ne h]
    fin_cases i
    fin_cases j
    simp_all

theorem hA0B0 : !![3] * !![1/3] = (1 : Matrix (Fin 1) (Fin 1) ℝ) := by
  ext i j
  by_cases h : i = j
  · rw [h, Matrix.one_apply_eq]
    fin_cases j
    simp [Matrix.mul_apply, Matrix.of_apply]
  · rw [Matrix.one_apply_ne h]
    fin_cases i
    fin_cases j
    simp_all

/-- (a) The unrestricted Gram matrix is a unit. -/
theorem test_isUnit_XX : IsUnit (Xₙᵀ * Xₙ) := by
  rw [hXX]
  exact ⟨⟨!![3, 3; 3, 5], !![5/6, -1/2; -1/2, 1/2], hAB, hBA⟩, rfl⟩

/-- (a) The restricted Gram matrix is a unit. -/
theorem test_isUnit_X0X0 : IsUnit (X₀ₙᵀ * X₀ₙ) := by
  rw [hX0X0]
  exact ⟨⟨!![3], !![1/3], hA0B0, hB0A0⟩, rfl⟩

/-- (b) The restricted column space sits inside the unrestricted one. -/
theorem test_nested : LinearMap.range (Matrix.toEuclideanLin X₀ₙ)
    ≤ LinearMap.range (Matrix.toEuclideanLin Xₙ) := by
  have hX0 : X₀ₙ = Xₙ * (!![1; 0] : Matrix (Fin 2) (Fin 1) ℝ) := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [X₀ₙ, Xₙ, Matrix.mul_apply, Fin.sum_univ_two, Matrix.of_apply]
  have hmap : Matrix.toEuclideanLin X₀ₙ = Matrix.toEuclideanLin Xₙ ∘ₗ
      Matrix.toEuclideanLin (!![1; 0] : Matrix (Fin 2) (Fin 1) ℝ) := by
    rw [hX0]
    exact Matrix.toLpLin_mul_same 2 Xₙ _
  rw [hmap]
  exact LinearMap.range_comp_le_range _ _

theorem hinv : (!![3, 3; 3, 5] : Matrix (Fin 2) (Fin 2) ℝ)⁻¹
    = !![5/6, -1/2; -1/2, 1/2] :=
  Matrix.inv_eq_left_inv hBA

theorem hinv0 : (!![3] : Matrix (Fin 1) (Fin 1) ℝ)⁻¹ = !![1/3] :=
  Matrix.inv_eq_left_inv hB0A0

theorem hols : olsMatrix Xₙ = !![5/6, 1/3, -1/6; -1/2, 0, 1/2] := by
  rw [olsMatrix_eq, hXX, hinv]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Xₙ, Matrix.mul_apply, Fin.sum_univ_two, Matrix.transpose_apply,
      Matrix.of_apply] <;>
    norm_num

theorem hols0 : olsMatrix X₀ₙ = !![1/3, 1/3, 1/3] := by
  rw [olsMatrix_eq, hX0X0, hinv0]
  ext i j
  fin_cases i
  fin_cases j <;>
    simp [X₀ₙ, Matrix.mul_apply, Matrix.transpose_apply, Matrix.of_apply]

theorem hβ : olsEstimator Xₙ yₙ = ![-1/6, 1/2] := by
  show olsMatrix Xₙ *ᵥ yₙ = ![-1/6, 1/2]
  rw [hols]
  funext i
  fin_cases i <;>
    simp [yₙ, Matrix.mulVec_apply_eq_sum, Fin.sum_univ_three, Matrix.of_apply]

theorem hβ0 : olsEstimator X₀ₙ yₙ = ![1/3] := by
  show olsMatrix X₀ₙ *ᵥ yₙ = ![1/3]
  rw [hols0]
  funext i
  fin_cases i
  simp [yₙ, Matrix.mulVec_apply_eq_sum, Fin.sum_univ_three, Matrix.of_apply]

theorem hfit : Xₙ *ᵥ olsEstimator Xₙ yₙ = ![-1/6, 1/3, 5/6] := by
  rw [hβ]
  funext i
  fin_cases i <;>
    simp [Xₙ, Matrix.mulVec_apply_eq_sum, Fin.sum_univ_two, Matrix.of_apply] <;>
    norm_num

theorem hfit0 : X₀ₙ *ᵥ olsEstimator X₀ₙ yₙ = ![1/3, 1/3, 1/3] := by
  rw [hβ0]
  funext i
  fin_cases i <;>
    simp [X₀ₙ, Matrix.mulVec_apply_eq_sum, Matrix.of_apply]

/-- (c) The restricted residual sum of squares is `2 / 3`. -/
theorem test_rss0 : rssDesign X₀ₙ yₙ = 2/3 := by
  unfold rssDesign
  rw [hfit0]
  simp [yₙ, dotProduct, Fin.sum_univ_three, Pi.sub_apply]
  norm_num

/-- (c) The unrestricted residual sum of squares is `1 / 6`. -/
theorem test_rss : rssDesign Xₙ yₙ = 1/6 := by
  unfold rssDesign
  rw [hfit]
  simp [yₙ, dotProduct, Fin.sum_univ_three, Pi.sub_apply]
  norm_num

/-- (c) The nested-model `F` statistic equals `3`. -/
theorem test_nestedF : nestedFStatistic Xₙ X₀ₙ yₙ = 3 := by
  have c1 : Fintype.card (Fin 1) = 1 := by decide
  have c2 : Fintype.card (Fin 2) = 2 := by decide
  have c3 : Fintype.card (Fin 3) = 3 := by decide
  unfold nestedFStatistic
  rw [test_rss0, test_rss, c1, c2, c3]
  norm_num

end MathlibExtTest.LinearModelNestedF
