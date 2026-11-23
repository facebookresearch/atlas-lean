/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Probability.Statistics.LinearModel.ResidualVarianceUnbiased
import Mathlib.LinearAlgebra.Matrix.Notation

/-! # Tests for `MathlibExt.Probability.Statistics.LinearModel.ResidualVarianceUnbiased` -/

open Matrix MeasureTheory ProbabilityTheory MathlibExt.Probability.Statistics.LinearModel

namespace MathlibExtTest.LinearModelResidualVariance

open MathlibExt.Probability.Statistics.LinearModel

def X₀ : Matrix (Fin 3) (Fin 1) ℝ := Matrix.of fun _ _ => 1

example : ((![1, 2, 3] - X₀ *ᵥ olsEstimator X₀ ![1, 2, 3]) ⬝ᵥ
    (![1, 2, 3] - X₀ *ᵥ olsEstimator X₀ ![1, 2, 3])) /
    ((Fintype.card (Fin 3) : ℝ) - (Fintype.card (Fin 1) : ℝ)) = 1 := by
  have hGram : X₀ᵀ * X₀ = !![3] := by
    ext i j
    fin_cases i
    fin_cases j
    simp [X₀, Matrix.mul_apply]
  have hInv : (X₀ᵀ * X₀)⁻¹ = !![(1/3 : ℝ)] := by
    rw [hGram]
    apply Matrix.inv_eq_right_inv
    ext i j
    fin_cases i
    fin_cases j
    simp [Matrix.mul_apply]
  have hEst : olsEstimator X₀ ![1, 2, 3] = ![2] := by
    simp only [olsEstimator, olsMatrix_eq, hInv]
    ext i
    fin_cases i
    simp only [X₀, Matrix.mulVec_apply_eq_sum, Matrix.mul_apply,
      Matrix.transpose_apply, Matrix.of_apply, Fin.sum_univ_three]
    norm_num
  rw [hEst]
  simp only [X₀, dotProduct, Fin.sum_univ_three, Fintype.card_fin]
  norm_num

end MathlibExtTest.LinearModelResidualVariance
