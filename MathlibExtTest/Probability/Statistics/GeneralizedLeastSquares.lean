/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Probability.Statistics.GeneralizedLeastSquares
import Mathlib.Algebra.Order.Star.Real
import Mathlib.LinearAlgebra.Matrix.Notation

/-! # Tests for `MathlibExt.Probability.Statistics.GeneralizedLeastSquares` -/

open Matrix MathlibExt.Probability.Statistics.GeneralizedLeastSquares

namespace MathlibExtTest.GeneralizedLeastSquares

/-- With unit noise covariance the GLS matrix is the ordinary least-squares matrix. -/
example {m k : ℕ} (X : Matrix (Fin m) (Fin k) ℝ) : glsMatrix X 1 = (Xᵀ * X)⁻¹ * Xᵀ := by
  simp [glsMatrix]

/-- One observation of one parameter with noise variance `v > 0`: the GLS matrix is `1`
(the estimate is the observation) and its variance is `v`. -/
example {v : ℝ} (hv : 0 < v) :
    glsMatrix (1 : Matrix (Fin 1) (Fin 1) ℝ) (v • 1) = 1 ∧
      glsMatrix (1 : Matrix (Fin 1) (Fin 1) ℝ) (v • 1) * (v • 1) *
        (glsMatrix (1 : Matrix (Fin 1) (Fin 1) ℝ) (v • 1))ᵀ = v • 1 := by
  have hV : (v • (1 : Matrix (Fin 1) (Fin 1) ℝ)).PosDef := Matrix.PosDef.one.smul hv
  have hX : IsUnit ((1 : Matrix (Fin 1) (Fin 1) ℝ)ᵀ * (v • 1)⁻¹ * 1) := by
    simpa using (hV.inv).isUnit
  have h1 := glsMatrix_mul_self hX
  rw [Matrix.mul_one] at h1
  refine ⟨h1, ?_⟩
  rw [glsMatrix_mul_mul_transpose hV hX]
  ext i j
  fin_cases i; fin_cases j
  simp

/-- Noise covariance `diag(1, 2)`. -/
abbrev V2 : Matrix (Fin 2) (Fin 2) ℝ := Matrix.diagonal ![1, 2]

/-- Two observations of one mean. -/
abbrev X2 : Matrix (Fin 2) (Fin 1) ℝ := Matrix.of fun _ _ => 1

/-- The equal-weight estimator `(y₁ + y₂) / 2`. -/
noncomputable abbrev A2 : Matrix (Fin 1) (Fin 2) ℝ := Matrix.of fun _ _ => 1 / 2

/-- Aitken's theorem for two observations of one mean with variances `1` and `2`: the
equal-weight estimator is unbiased, so its variance is at least the GLS variance. -/
example : (A2 * V2 * A2ᵀ - glsMatrix X2 V2 * V2 * (glsMatrix X2 V2)ᵀ).PosSemidef := by
  have hV : V2.PosDef := Matrix.PosDef.diagonal (by intro i; fin_cases i <;> norm_num)
  have hX : IsUnit (X2ᵀ * V2⁻¹ * X2) := by
    have hVinv : V2⁻¹ = Matrix.diagonal ![1, 1 / 2] := Matrix.inv_eq_left_inv (by
      ext i j; fin_cases i <;> fin_cases j <;> simp)
    rw [Matrix.isUnit_iff_isUnit_det, hVinv]
    simp [Matrix.det_unique, Matrix.mul_apply, Fin.sum_univ_two]
    norm_num
  refine aitken hV hX _ ?_
  ext i j
  fin_cases i; fin_cases j
  simp [Matrix.mul_apply]

end MathlibExtTest.GeneralizedLeastSquares
