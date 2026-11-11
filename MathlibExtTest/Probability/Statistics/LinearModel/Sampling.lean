/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Probability.Statistics.LinearModel.Sampling
import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.Probability.Distributions.Gaussian.Multivariate

/-! # Tests for `MathlibExt.Probability.Statistics.LinearModel.Sampling` -/

open Matrix MeasureTheory ProbabilityTheory MathlibExt.Probability.Statistics.LinearModel

namespace MathlibExtTest.LinearModelSampling

/-- Intercept-only design with three observations. -/
noncomputable def X₀ : Matrix (Fin 3) (Fin 1) ℝ := Matrix.of fun _ _ => 1

theorem gram_X₀ : X₀ᵀ * X₀ = Matrix.of fun _ _ => 3 := by
  ext i j
  simp [X₀, Matrix.mul_apply]

theorem isUnit_gram_X₀ : IsUnit (X₀ᵀ * X₀) := by
  rw [Matrix.isUnit_iff_isUnit_det, gram_X₀, Matrix.det_unique]
  simp

theorem gram_X₀_inv : (X₀ᵀ * X₀)⁻¹ = Matrix.of fun _ _ => 1 / 3 := by
  refine Matrix.inv_eq_left_inv ?_
  rw [gram_X₀]
  ext i j
  fin_cases i; fin_cases j
  simp [Matrix.mul_apply]

/-- The OLS matrix of the intercept-only design averages the observations. -/
theorem olsMatrix_X₀ : olsMatrix X₀ = Matrix.of fun _ _ => 1 / 3 := by
  rw [olsMatrix_eq, gram_X₀_inv]
  ext i j
  simp [X₀, Matrix.mul_apply]

/-- The OLS estimate of the intercept is the sample mean. -/
example (y : Fin 3 → ℝ) : olsEstimator X₀ y 0 = (y 0 + y 1 + y 2) / 3 := by
  simp only [olsEstimator, olsMatrix_X₀, mulVec, dotProduct, Fin.sum_univ_three, of_apply]
  ring

/-- `B X = 1` on the fixture. -/
example : olsMatrix X₀ * X₀ = 1 := olsMatrix_mul_self isUnit_gram_X₀

/-! ### A concrete error law: `ε ~ N(0, σ² I₃)` -/

variable (σ : ℝ)

/-- Isotropic covariance `σ² I₃`. -/
noncomputable abbrev S₀ : Matrix (Fin 3) (Fin 3) ℝ := (σ ^ 2) • 1

theorem posSemidef_S₀ : (S₀ σ).PosSemidef :=
  Matrix.PosSemidef.one.smul (sq_nonneg σ)

/-- The errors are the coordinates of a draw from `N(0, σ² I₃)`. -/
noncomputable abbrev P₀ : Measure (EuclideanSpace ℝ (Fin 3)) := multivariateGaussian 0 (S₀ σ)

theorem memLp_coord (i : Fin 3) : MemLp (fun x : EuclideanSpace ℝ (Fin 3) => x i) 2 (P₀ σ) := by
  simpa using IsGaussian.memLp_dual (P₀ σ) (EuclideanSpace.proj i) 2 (by simp)

theorem cov_coord (i j : Fin 3) :
    cov[fun x : EuclideanSpace ℝ (Fin 3) => x i, fun x => x j; P₀ σ] =
      if i = j then σ ^ 2 else 0 := by
  rw [covariance_eval_multivariateGaussian (posSemidef_S₀ σ)]
  simp [Matrix.one_apply]

theorem integral_coord (i : Fin 3) : ∫ x, (x : EuclideanSpace ℝ (Fin 3)) i ∂(P₀ σ) = 0 := by
  rw [← eval_integral_piLp fun j => (memLp_coord σ j).integrable (by norm_num)]
  simp

/-- Unbiasedness on the Gaussian fixture: the intercept estimate has mean `β`. -/
example (β : Fin 1 → ℝ) :
    ∫ x, olsEstimator X₀ (X₀ *ᵥ β + fun i => (x : EuclideanSpace ℝ (Fin 3)) i) 0 ∂(P₀ σ) =
      β 0 :=
  integral_olsEstimator_apply isUnit_gram_X₀ β
    (fun i => (memLp_coord σ i).integrable (by norm_num)) (integral_coord σ) 0

/-- Covariance on the Gaussian fixture: the sample mean of three `N(·, σ²)` errors has
variance `σ² / 3`. -/
example (β : Fin 1 → ℝ) :
    cov[fun x => olsEstimator X₀ (X₀ *ᵥ β + fun i => (x : EuclideanSpace ℝ (Fin 3)) i) 0,
      fun x => olsEstimator X₀ (X₀ *ᵥ β + fun i => (x : EuclideanSpace ℝ (Fin 3)) i) 0;
      P₀ σ] = σ ^ 2 / 3 := by
  rw [covariance_olsEstimator isUnit_gram_X₀ β σ (memLp_coord σ) (cov_coord σ), gram_X₀_inv]
  simp [div_eq_mul_inv]

/-! ### Residual-maker matrix on the fixture -/

theorem residualMatrix_X₀ : residualMatrix X₀ =
    !![2 / 3, -1 / 3, -1 / 3; -1 / 3, 2 / 3, -1 / 3; -1 / 3, -1 / 3, 2 / 3] := by
  rw [residualMatrix, olsMatrix_X₀]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [X₀, Matrix.mul_apply] <;> norm_num

/-- Idempotence of the residual-maker matrix, checked numerically on the fixture. -/
example : !![(2 : ℝ) / 3, -1 / 3, -1 / 3; -1 / 3, 2 / 3, -1 / 3; -1 / 3, -1 / 3, 2 / 3] *
      !![2 / 3, -1 / 3, -1 / 3; -1 / 3, 2 / 3, -1 / 3; -1 / 3, -1 / 3, 2 / 3] =
    !![2 / 3, -1 / 3, -1 / 3; -1 / 3, 2 / 3, -1 / 3; -1 / 3, -1 / 3, 2 / 3] := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_three] <;> norm_num

example : residualMatrix X₀ * residualMatrix X₀ = residualMatrix X₀ :=
  residualMatrix_mul_self isUnit_gram_X₀

example : (residualMatrix X₀).rank = 2 := rank_residualMatrix isUnit_gram_X₀

example : (residualMatrix X₀).trace = 2 := by
  rw [residualMatrix_X₀]
  simp [Matrix.trace, Fin.sum_univ_three]
  norm_num

/-- The residuals of the intercept-only model are the deviations from the sample mean. -/
example (y : Fin 3 → ℝ) : (y - X₀ *ᵥ olsEstimator X₀ y) 0 = y 0 - (y 0 + y 1 + y 2) / 3 := by
  rw [olsEstimator, olsMatrix_X₀]
  simp only [Pi.sub_apply, mulVec, dotProduct, Fin.sum_univ_one, Fin.sum_univ_three, of_apply, X₀]
  ring

/-- With i.i.d. standard normal errors on three observations, the residual sum of squares of the
intercept-only model, `∑ (yᵢ - ȳ)²`, is `χ²₂`. -/
example (β : Fin 1 → ℝ) :
    HasLaw (fun ε : Fin 3 → ℝ => (X₀ *ᵥ β + ε - X₀ *ᵥ olsEstimator X₀ (X₀ *ᵥ β + ε)) ⬝ᵥ
        (X₀ *ᵥ β + ε - X₀ *ᵥ olsEstimator X₀ (X₀ *ᵥ β + ε)))
      (chiSquareMeasure 2) (Measure.pi fun _ : Fin 3 => gaussianReal 0 1) := by
  simpa using hasLaw_rss isUnit_gram_X₀ (by simp) β (HasLaw.id)

/-- For every positive scale, scaling three standard normal errors by `σ` gives
an intercept-only residual sum of squares whose ratio to `σ²` has law `χ²₂`. -/
theorem hasLaw_scaled_rss (hσ : 0 < σ) (β : Fin 1 → ℝ) :
    HasLaw (fun z : Fin 3 → ℝ =>
        (X₀ *ᵥ β + σ • z - X₀ *ᵥ olsEstimator X₀ (X₀ *ᵥ β + σ • z)) ⬝ᵥ
          (X₀ *ᵥ β + σ • z - X₀ *ᵥ olsEstimator X₀ (X₀ *ᵥ β + σ • z)) / σ ^ 2)
      (chiSquareMeasure 2) (Measure.pi fun _ : Fin 3 => gaussianReal 0 1) := by
  have hε : HasLaw (fun z : Fin 3 → ℝ => σ⁻¹ • (σ • z))
      (Measure.pi fun _ : Fin 3 => gaussianReal 0 1)
      (Measure.pi fun _ : Fin 3 => gaussianReal 0 1) := by
    simp only [smul_smul, inv_mul_cancel₀ (ne_of_gt hσ), one_smul]
    exact HasLaw.id
  simpa using hasLaw_rss_div_sq isUnit_gram_X₀ (by simp) β σ hσ hε

end MathlibExtTest.LinearModelSampling
