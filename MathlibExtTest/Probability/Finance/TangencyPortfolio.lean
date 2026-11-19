/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Probability.Finance.TangencyPortfolio
import Mathlib.Algebra.Order.Star.Real
import Mathlib.LinearAlgebra.Matrix.Notation

/-! # Tests for `MathlibExt.Probability.Finance.TangencyPortfolio` -/

open Matrix MathlibExt.Probability.Finance.TangencyPortfolio

namespace MathlibExtTest.TangencyPortfolio

theorem ex_tangencyPortfolio_eq :
    tangencyPortfolio (1 : Matrix (Fin 2) (Fin 2) ℝ) ![1, 3] 0 = ![1/4, 3/4] := by
  have hz : tangencyDirection (1 : Matrix (Fin 2) (Fin 2) ℝ) ![1, 3] 0 = ![1, 3] := by
    unfold tangencyDirection
    rw [inv_one, one_mulVec]
    simp
  have hsum : (∑ i, tangencyDirection (1 : Matrix (Fin 2) (Fin 2) ℝ) ![1, 3] 0 i) = 4 := by
    rw [hz]
    simp [Fin.sum_univ_two]
    norm_num
  unfold tangencyPortfolio
  rw [hsum, hz]
  funext i
  fin_cases i; simp; norm_num

theorem ex_sharpeRatio_tangency_eq :
    sharpeRatio (1 : Matrix (Fin 2) (Fin 2) ℝ) ![1, 3] 0
      (tangencyPortfolio 1 ![1, 3] 0) = Real.sqrt 10 := by
  have hS : (1 : Matrix (Fin 2) (Fin 2) ℝ).PosDef := Matrix.PosDef.one
  have hA : ((1 : Fin 2 → ℝ) ⬝ᵥ ((1 : Matrix (Fin 2) (Fin 2) ℝ)⁻¹ *ᵥ ![1, 3])) = 4 := by
    rw [inv_one, one_mulVec]
    simp [dotProduct, Fin.sum_univ_two]
    norm_num
  have hC : ((1 : Fin 2 → ℝ) ⬝ᵥ ((1 : Matrix (Fin 2) (Fin 2) ℝ)⁻¹ *ᵥ 1)) = 2 := by
    rw [inv_one, one_mulVec]
    simp [dotProduct]
  have hr : (0 : ℝ) < ((1 : Fin 2 → ℝ) ⬝ᵥ ((1 : Matrix (Fin 2) (Fin 2) ℝ)⁻¹ *ᵥ ![1, 3])) /
      ((1 : Fin 2 → ℝ) ⬝ᵥ ((1 : Matrix (Fin 2) (Fin 2) ℝ)⁻¹ *ᵥ 1)) := by
    rw [hA, hC]
    norm_num
  have hq : MathlibExt.LinearAlgebra.Matrix.QuadraticFormCongruence.quadForm
      (1 : Matrix (Fin 2) (Fin 2) ℝ)⁻¹
      (![1, 3] - (0 : ℝ) • (1 : Fin 2 → ℝ)) = 10 := by
    simp [MathlibExt.LinearAlgebra.Matrix.QuadraticFormCongruence.quadForm]
    norm_num [dotProduct, Fin.sum_univ_two]
  have hth := sharpeRatio_tangencyPortfolio hS ![1, 3] hr
  rw [hq] at hth
  exact hth

theorem ex_sharpeRatio_le :
    sharpeRatio (1 : Matrix (Fin 2) (Fin 2) ℝ) ![1, 3] 0 ![1/2, 1/2] ≤ Real.sqrt 10 := by
  have hS : (1 : Matrix (Fin 2) (Fin 2) ℝ).PosDef := Matrix.PosDef.one
  have hA : ((1 : Fin 2 → ℝ) ⬝ᵥ ((1 : Matrix (Fin 2) (Fin 2) ℝ)⁻¹ *ᵥ ![1, 3])) = 4 := by
    rw [inv_one, one_mulVec]
    simp [dotProduct, Fin.sum_univ_two]
    norm_num
  have hC : ((1 : Fin 2 → ℝ) ⬝ᵥ ((1 : Matrix (Fin 2) (Fin 2) ℝ)⁻¹ *ᵥ 1)) = 2 := by
    rw [inv_one, one_mulVec]
    simp [dotProduct]
  have hr : (0 : ℝ) < ((1 : Fin 2 → ℝ) ⬝ᵥ ((1 : Matrix (Fin 2) (Fin 2) ℝ)⁻¹ *ᵥ ![1, 3])) /
      ((1 : Fin 2 → ℝ) ⬝ᵥ ((1 : Matrix (Fin 2) (Fin 2) ℝ)⁻¹ *ᵥ 1)) := by
    rw [hA, hC]
    norm_num
  have hw : (∑ i, ![1/2, 1/2] i : ℝ) = 1 := by
    simp [Fin.sum_univ_two]
    norm_num
  have hle := sharpeRatio_le_sharpeRatio_tangencyPortfolio hS ![1, 3] hr hw
  rw [ex_sharpeRatio_tangency_eq] at hle
  exact hle

theorem ex_boundary :
    ∑ i, tangencyDirection (1 : Matrix (Fin 2) (Fin 2) ℝ) ![1, 3] 2 i = 0 := by
  have hz : tangencyDirection (1 : Matrix (Fin 2) (Fin 2) ℝ) ![1, 3] 2 = ![-1, 1] := by
    unfold tangencyDirection
    rw [inv_one, one_mulVec]
    funext i
    fin_cases i <;> simp [Pi.sub_apply, Pi.smul_apply, smul_eq_mul] <;> norm_num
  rw [hz]
  simp [Fin.sum_univ_two]

/-- Above the GMV return `2`, the tangency portfolio minimizes Sharpe. -/
theorem ex_negative_branch :
    sharpeRatio (1 : Matrix (Fin 2) (Fin 2) ℝ) ![1, 3] 4
      (tangencyPortfolio 1 ![1, 3] 4) ≤ -1 := by
  have hr : ((1 : Fin 2 → ℝ) ⬝ᵥ ((1 : Matrix (Fin 2) (Fin 2) ℝ)⁻¹ *ᵥ ![1, 3])) /
      ((1 : Fin 2 → ℝ) ⬝ᵥ ((1 : Matrix (Fin 2) (Fin 2) ℝ)⁻¹ *ᵥ 1)) < (4 : ℝ) := by
    norm_num [inv_one, one_mulVec, dotProduct, Fin.sum_univ_two]
  have hw : (∑ i, (![0, 1] : Fin 2 → ℝ) i) = 1 := by
    norm_num [Fin.sum_univ_two]
  have h := sharpeRatio_tangencyPortfolio_le_of_lt
    (S := (1 : Matrix (Fin 2) (Fin 2) ℝ)) Matrix.PosDef.one ![1, 3] hr hw
  have hcomp : sharpeRatio (1 : Matrix (Fin 2) (Fin 2) ℝ) ![1, 3] 4 ![0, 1] = -1 := by
    norm_num [sharpeRatio, MathlibExt.LinearAlgebra.Matrix.QuadraticFormCongruence.quadForm,
      one_mulVec, dotProduct, Fin.sum_univ_two]
  simpa only [hcomp] using h

end MathlibExtTest.TangencyPortfolio
