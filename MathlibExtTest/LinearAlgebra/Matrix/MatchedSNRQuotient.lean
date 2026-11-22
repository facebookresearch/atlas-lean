/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.LinearAlgebra.Matrix.MatchedSNRQuotient
import Mathlib.Data.Matrix.Mul
import Mathlib.Tactic.NormNum

@[expose] public section

open MathlibExt.LinearAlgebra.Matrix.MatchedSNRQuotient
open scoped Matrix

namespace MathlibExtTest.LinearAlgebra.Matrix.MatchedSNRQuotient

/-- Fixture: `R = diag(1, 4)`, non-axis-aligned signal `s = (1, 1)`: the bound
`sᵀR⁻¹s` is `5/4`. -/
theorem diag_one_four_inv_quadForm :
    (![1, 1] : Fin 2 → ℝ) ⬝ᵥ (Matrix.diagonal ![1, 4] : Matrix (Fin 2) (Fin 2) ℝ)⁻¹ *ᵥ
      ![1, 1] = 5 / 4 := by
  have hUdet : IsUnit (Matrix.diagonal ![1, 4] : Matrix (Fin 2) (Fin 2) ℝ).det := by
    simp only [Matrix.det_diagonal, Fin.prod_univ_two, Matrix.cons_val_zero,
      Matrix.cons_val_one, isUnit_iff_ne_zero]
    norm_num
  have hRD : (Matrix.diagonal ![1, 4] : Matrix (Fin 2) (Fin 2) ℝ)
      * Matrix.diagonal ![1, 1 / 4] = 1 := by
    rw [Matrix.diagonal_mul_diagonal]
    have h1 : (fun i : Fin 2 => (![1, 4] : Fin 2 → ℝ) i * (![1, 1 / 4] : Fin 2 → ℝ) i)
        = 1 := by
      funext i
      fin_cases i <;> norm_num [Matrix.cons_val_zero, Matrix.cons_val_one, Pi.one_apply]
    rw [h1, Matrix.diagonal_one']
  have hinv : (Matrix.diagonal ![1, 4] : Matrix (Fin 2) (Fin 2) ℝ)⁻¹
      = Matrix.diagonal ![1, 1 / 4] := by
    calc (Matrix.diagonal ![1, 4] : Matrix (Fin 2) (Fin 2) ℝ)⁻¹
          = (Matrix.diagonal ![1, 4] : Matrix (Fin 2) (Fin 2) ℝ)⁻¹ * 1 :=
            (mul_one _).symm
        _ = (Matrix.diagonal ![1, 4] : Matrix (Fin 2) (Fin 2) ℝ)⁻¹ *
            ((Matrix.diagonal ![1, 4] : Matrix (Fin 2) (Fin 2) ℝ)
              * Matrix.diagonal ![1, 1 / 4]) := by rw [hRD]
        _ = ((Matrix.diagonal ![1, 4] : Matrix (Fin 2) (Fin 2) ℝ)⁻¹ *
            (Matrix.diagonal ![1, 4] : Matrix (Fin 2) (Fin 2) ℝ))
            * Matrix.diagonal ![1, 1 / 4] := by rw [mul_assoc]
        _ = 1 * Matrix.diagonal ![1, 1 / 4] := by rw [Matrix.nonsing_inv_mul _ hUdet]
        _ = Matrix.diagonal ![1, 1 / 4] := one_mul _
  rw [hinv]
  simp only [dotProduct, Matrix.mulVec_diagonal, Fin.sum_univ_two,
    Matrix.cons_val_zero, Matrix.cons_val_one]
  norm_num

/-- Fixture: the non-optimal weight `w = (1, 1)` has SNR `4/5`, strictly below `5/4`. -/
theorem diag_one_four_matchedSNR_ones :
    matchedSNR (Matrix.diagonal ![1, 4] : Matrix (Fin 2) (Fin 2) ℝ) ![1, 1] ![1, 1] =
      4 / 5 := by
  simp only [matchedSNR, dotProduct, Matrix.mulVec_diagonal, Fin.sum_univ_two,
    Matrix.cons_val_zero, Matrix.cons_val_one]
  norm_num

/-- Fixture: the negative multiple `w = -2 • R⁻¹ s = (-2, -1/2)` is also an SNR maximizer,
attaining `5/4`. -/
theorem diag_one_four_matchedSNR_neg_multiple :
    matchedSNR (Matrix.diagonal ![1, 4] : Matrix (Fin 2) (Fin 2) ℝ) ![1, 1] ![-2, -1 / 2] =
      5 / 4 := by
  simp only [matchedSNR, dotProduct, Matrix.mulVec_diagonal, Fin.sum_univ_two,
    Matrix.cons_val_zero, Matrix.cons_val_one]
  norm_num

/-- Fixture: `diag(1, 4)` is positive definite, so the general theorems apply to the
fixtures above. -/
theorem diag_one_four_posDef :
    (Matrix.diagonal ![1, 4] : Matrix (Fin 2) (Fin 2) ℝ).PosDef := by
  apply Matrix.PosDef.diagonal
  intro i
  fin_cases i <;> norm_num [Matrix.cons_val_zero, Matrix.cons_val_one]

/-- Violated premise: for the invertible but indefinite `R = diag(1, -1)`, `s = (0, 1)`
and `w = (1, 1)`, the bound fails (`0 > -1`), so positive definiteness cannot be dropped. -/
theorem not_matchedSNR_le_of_indefinite :
    ¬ matchedSNR (Matrix.diagonal ![1, -1] : Matrix (Fin 2) (Fin 2) ℝ) ![0, 1] ![1, 1] ≤
      (![0, 1] : Fin 2 → ℝ) ⬝ᵥ (Matrix.diagonal ![1, -1] : Matrix (Fin 2) (Fin 2) ℝ)⁻¹ *ᵥ
        ![0, 1] := by
  have hUdet : IsUnit (Matrix.diagonal ![1, -1] : Matrix (Fin 2) (Fin 2) ℝ).det := by
    simp only [Matrix.det_diagonal, Fin.prod_univ_two, Matrix.cons_val_zero,
      Matrix.cons_val_one, isUnit_iff_ne_zero]
    norm_num
  have hRR : (Matrix.diagonal ![1, -1] : Matrix (Fin 2) (Fin 2) ℝ)
      * Matrix.diagonal ![1, -1] = 1 := by
    rw [Matrix.diagonal_mul_diagonal]
    have h1 : (fun i : Fin 2 => (![1, -1] : Fin 2 → ℝ) i * (![1, -1] : Fin 2 → ℝ) i)
        = 1 := by
      funext i
      fin_cases i <;> norm_num [Matrix.cons_val_zero, Matrix.cons_val_one, Pi.one_apply]
    rw [h1, Matrix.diagonal_one']
  have hinv : (Matrix.diagonal ![1, -1] : Matrix (Fin 2) (Fin 2) ℝ)⁻¹
      = Matrix.diagonal ![1, -1] := by
    calc (Matrix.diagonal ![1, -1] : Matrix (Fin 2) (Fin 2) ℝ)⁻¹
          = (Matrix.diagonal ![1, -1] : Matrix (Fin 2) (Fin 2) ℝ)⁻¹ * 1 :=
            (mul_one _).symm
        _ = (Matrix.diagonal ![1, -1] : Matrix (Fin 2) (Fin 2) ℝ)⁻¹ *
            ((Matrix.diagonal ![1, -1] : Matrix (Fin 2) (Fin 2) ℝ)
              * Matrix.diagonal ![1, -1]) := by rw [hRR]
        _ = ((Matrix.diagonal ![1, -1] : Matrix (Fin 2) (Fin 2) ℝ)⁻¹ *
            (Matrix.diagonal ![1, -1] : Matrix (Fin 2) (Fin 2) ℝ))
            * Matrix.diagonal ![1, -1] := by rw [mul_assoc]
        _ = 1 * Matrix.diagonal ![1, -1] := by rw [Matrix.nonsing_inv_mul _ hUdet]
        _ = Matrix.diagonal ![1, -1] := one_mul _
  rw [hinv]
  simp only [matchedSNR, dotProduct, Matrix.mulVec_diagonal, Fin.sum_univ_two,
    Matrix.cons_val_zero, Matrix.cons_val_one]
  norm_num

/-- The leaf's validation case: `R = diag(1, 4)`, `s = w = 1`
gives SNR `4/5`. -/
example : matchedSNR (Matrix.diagonal ![1, 4] : Matrix (Fin 2) (Fin 2) ℝ)
    ![1, 1] ![1, 1] = 4 / 5 :=
  diag_one_four_matchedSNR_ones

/-- Zero signal has zero SNR for a nonzero weight. -/
example : matchedSNR (Matrix.diagonal ![1, 4] : Matrix (Fin 2) (Fin 2) ℝ)
    0 ![1, 0] = 0 :=
  matchedSNR_zero_signal _ _ (by
    intro h
    have h0 := congrFun h 0
    simp at h0)

/-- The headline bound on the validation matrix with the
non-optimal weight `w = (1, 0)`. -/
example : matchedSNR (Matrix.diagonal ![1, 4] : Matrix (Fin 2) (Fin 2) ℝ)
    ![1, 1] ![1, 0]
    ≤ dotProduct ![1, 1] ((Matrix.diagonal ![1, 4] : Matrix (Fin 2) (Fin 2) ℝ)⁻¹
      *ᵥ ![1, 1]) :=
  matchedSNR_le_dotProduct_inv_mulVec _ diag_one_four_posDef _ _
    (by
      intro h
      have h0 := congrFun h 0
      simp at h0)
    (by
      intro h
      have h0 := congrFun h 0
      simp at h0)

/-- Equality characterization, forward direction: the negative
multiple `w = (-2, -1/2)` attains the bound, so it is a nonzero
multiple of the matched weight. -/
example : ∃ c : ℝ, c ≠ 0 ∧ ![-2, -1 / 2]
    = c • (Matrix.diagonal ![1, 4] : Matrix (Fin 2) (Fin 2) ℝ)⁻¹ *ᵥ ![1, 1] := by
  apply (matchedSNR_eq_dotProduct_inv_mulVec_iff _
    diag_one_four_posDef ![1, 1] ![-2, -1 / 2] (by
      intro h
      have h0 := congrFun h 0
      simp at h0) (by
      intro h
      have h0 := congrFun h 0
      simp at h0)).mp
  rw [diag_one_four_matchedSNR_neg_multiple, diag_one_four_inv_quadForm]

/-- Equality characterization, reverse direction: `w = -2 • R⁻¹ s`
attains the bound. -/
example : matchedSNR (Matrix.diagonal ![1, 4] : Matrix (Fin 2) (Fin 2) ℝ)
    ![1, 1] ![-2, -1 / 2]
    = (![1, 1] : Fin 2 → ℝ) ⬝ᵥ (Matrix.diagonal ![1, 4] : Matrix (Fin 2) (Fin 2) ℝ)⁻¹
      *ᵥ ![1, 1] := by
  apply (matchedSNR_eq_dotProduct_inv_mulVec_iff _
    diag_one_four_posDef ![1, 1] ![-2, -1 / 2] (by
      intro h
      have h0 := congrFun h 0
      simp at h0) (by
      intro h
      have h0 := congrFun h 0
      simp at h0)).mpr
  refine ⟨-2, by norm_num, ?_⟩
  rw [show (Matrix.diagonal ![1, 4] : Matrix (Fin 2) (Fin 2) ℝ)⁻¹
      = Matrix.diagonal ![1, 1 / 4] from ?_]
  · ext i
    fin_cases i <;>
      simp [Matrix.mulVec_diagonal, Matrix.cons_val_zero, Matrix.cons_val_one] <;>
      norm_num
  · have hUdet : IsUnit (Matrix.diagonal ![1, 4] : Matrix (Fin 2) (Fin 2) ℝ).det := by
      simp only [Matrix.det_diagonal, Fin.prod_univ_two, Matrix.cons_val_zero,
        Matrix.cons_val_one, isUnit_iff_ne_zero]
      norm_num
    have hRD : (Matrix.diagonal ![1, 4] : Matrix (Fin 2) (Fin 2) ℝ)
        * Matrix.diagonal ![1, 1 / 4] = 1 := by
      rw [Matrix.diagonal_mul_diagonal]
      have h1 : (fun i : Fin 2 => (![1, 4] : Fin 2 → ℝ) i * (![1, 1 / 4] : Fin 2 → ℝ) i)
          = 1 := by
        funext i
        fin_cases i <;> norm_num [Matrix.cons_val_zero, Matrix.cons_val_one, Pi.one_apply]
      rw [h1, Matrix.diagonal_one']
    calc (Matrix.diagonal ![1, 4] : Matrix (Fin 2) (Fin 2) ℝ)⁻¹
          = (Matrix.diagonal ![1, 4] : Matrix (Fin 2) (Fin 2) ℝ)⁻¹ * 1 :=
            (mul_one _).symm
        _ = (Matrix.diagonal ![1, 4] : Matrix (Fin 2) (Fin 2) ℝ)⁻¹ *
            ((Matrix.diagonal ![1, 4] : Matrix (Fin 2) (Fin 2) ℝ)
              * Matrix.diagonal ![1, 1 / 4]) := by rw [hRD]
        _ = ((Matrix.diagonal ![1, 4] : Matrix (Fin 2) (Fin 2) ℝ)⁻¹ *
            (Matrix.diagonal ![1, 4] : Matrix (Fin 2) (Fin 2) ℝ))
            * Matrix.diagonal ![1, 1 / 4] := by rw [mul_assoc]
        _ = 1 * Matrix.diagonal ![1, 1 / 4] := by rw [Matrix.nonsing_inv_mul _ hUdet]
        _ = Matrix.diagonal ![1, 1 / 4] := one_mul _

end MathlibExtTest.LinearAlgebra.Matrix.MatchedSNRQuotient
