/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Probability.Finance.MeanVariancePortfolio
import Mathlib.Algebra.Order.Star.Real
import Mathlib.LinearAlgebra.Matrix.Notation

/-! # Tests for `MathlibExt.Probability.Finance.MeanVariancePortfolio` -/

open Matrix MathlibExt.Probability.Finance.MeanVariancePortfolio

namespace MathlibExtTest.MeanVariancePortfolio

theorem minVariancePortfolio_one_eq_uniform :
    minVariancePortfolio (1 : Matrix (Fin 3) (Fin 3) ℝ) ![0, 1, 2] 1 =
      ![1/3, 1/3, 1/3] := by
  have hS : (1 : Matrix (Fin 3) (Fin 3) ℝ).PosDef := Matrix.PosDef.one
  have hμ : ∃ i j, (![0, 1, 2] : Fin 3 → ℝ) i ≠ ![0, 1, 2] j := by
    refine ⟨0, 1, ?_⟩
    simp [Matrix.cons_val_zero, Matrix.cons_val_one]
  have hu : IsFeasible (![0, 1, 2] : Fin 3 → ℝ) 1 ![1/3, 1/3, 1/3] := by
    constructor
    · rw [Fin.sum_univ_three]
      simp [Matrix.cons_val_zero, Matrix.cons_val_one]
      norm_num
    · rw [Fin.sum_univ_three]
      simp [Matrix.cons_val_zero, Matrix.cons_val_one]
      norm_num
  have hvar_u : portfolioVariance (1 : Matrix (Fin 3) (Fin 3) ℝ) ![1/3, 1/3, 1/3] =
      1/3 := by
    simp only [portfolioVariance, Matrix.one_mulVec, dotProduct, Fin.sum_univ_three]
    simp [Matrix.cons_val_zero, Matrix.cons_val_one]
    norm_num
  have qmam : ∀ v : Fin 3 → ℝ, ∑ i, v i = 1 → (1/3 : ℝ) ≤ v ⬝ᵥ v := by
    intro v hsum
    simp only [dotProduct, Fin.sum_univ_three]
    rw [Fin.sum_univ_three] at hsum
    nlinarith [sq_nonneg (v 0 - v 1), sq_nonneg (v 1 - v 2), sq_nonneg (v 0 - v 2), hsum]
  have hstar := minVariancePortfolio_isFeasible hS hμ 1
  have hge : (1/3 : ℝ) ≤ portfolioVariance (1 : Matrix (Fin 3) (Fin 3) ℝ)
      (minVariancePortfolio 1 ![0, 1, 2] 1) := by
    have h := qmam _ hstar.1
    simpa [portfolioVariance, Matrix.one_mulVec] using h
  have hle : portfolioVariance (1 : Matrix (Fin 3) (Fin 3) ℝ) ![1/3, 1/3, 1/3] ≤
      portfolioVariance 1 (minVariancePortfolio 1 ![0, 1, 2] 1) := by
    rw [hvar_u]
    exact hge
  have heq := eq_minVariancePortfolio_of_portfolioVariance_le hS hμ hu hle
  exact heq.symm

example : minVariancePortfolio (1 : Matrix (Fin 3) (Fin 3) ℝ) ![0, 1, 2] 1 =
    ![1/3, 1/3, 1/3] :=
  minVariancePortfolio_one_eq_uniform

example : portfolioVariance (1 : Matrix (Fin 3) (Fin 3) ℝ)
    (minVariancePortfolio (1 : Matrix (Fin 3) (Fin 3) ℝ) ![0, 1, 2] 1) = 1/3 := by
  rw [minVariancePortfolio_one_eq_uniform]
  simp only [portfolioVariance, Matrix.one_mulVec, dotProduct, Fin.sum_univ_three]
  simp [Matrix.cons_val_zero, Matrix.cons_val_one]
  norm_num

example : ¬ IsUnit ((constraintMatrix (fun _ : Fin 3 => (5 : ℝ)))ᵀ *
    (1 : Matrix (Fin 3) (Fin 3) ℝ)⁻¹ * constraintMatrix (fun _ : Fin 3 => (5 : ℝ))) := by
  have hS : (1 : Matrix (Fin 3) (Fin 3) ℝ).PosDef := Matrix.PosDef.one
  rw [isUnit_gram_iff hS]
  simp

end MathlibExtTest.MeanVariancePortfolio
