/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.MachineLearning.Regression.LeastSquares
public import CSLibExt.MachineLearning.Regression.BiasVariance

/-!
# Tests for least squares, ridge, lasso and the bias-variance decomposition

* Two examples with one constant feature and responses `1, 3`: the least-squares estimate is the
  mean `2`, which solves the normal equations, has residual sum of squares `2`, and maximizes
  the Gaussian likelihood; `θ = 0` does not solve the normal equations.
* A rank-deficient design (two equal columns, singular `Xᵀ X`) still has least-squares and
  maximum likelihood estimates.
* Ridge with `λ = 2` on the same data: the estimate is `1`.
* Soft thresholding at `1`: `3 ↦ 2`, `-3 ↦ -2`, `1/2 ↦ 0`; for the identity design with responses
  `3, 1/2` and `λ = 2`, the lasso minimizer is `(2, 0)`.
* Bias-variance with no noise and a constant predictor: the expected squared error is the squared
  bias.
-/

@[expose] public section

namespace Cslib.MachineLearning.LeastSquaresTests

open Cslib.MachineLearning LeastSquares Matrix

/-- One constant feature, two examples. -/
def X1 : Matrix (Fin 2) (Fin 1) ℝ := fun _ _ => 1

/-- Responses `1, 3`. -/
def y1 : Fin 2 → ℝ := ![1, 3]

example : rss X1 y1 (fun _ => 2) = 2 := by
  simp [rss, X1, y1, dotProduct, mulVec, Fin.sum_univ_two]
  norm_num

theorem normal_two : X1ᵀ *ᵥ (X1 *ᵥ fun _ => 2) = X1ᵀ *ᵥ y1 := by
  funext i
  simp [X1, y1, mulVec, dotProduct, Fin.sum_univ_two]
  norm_num

example : X1ᵀ *ᵥ (X1 *ᵥ fun _ => 0) ≠ X1ᵀ *ᵥ y1 := by
  intro h
  have := congrFun h 0
  simp [X1, y1, mulVec, dotProduct, Fin.sum_univ_two] at this
  norm_num at this

example (θ : Fin 1 → ℝ) : rss X1 y1 (fun _ => 2) ≤ rss X1 y1 θ :=
  rss_le_of_normal normal_two θ

example : IsMaxOn (gaussLikelihood X1 y1 1) Set.univ (fun _ => 2) :=
  (isMaxOn_gaussLikelihood_iff one_ne_zero _).2 normal_two

/-- A rank-deficient design: two identical columns. Least-squares estimates still exist. -/
def X2 : Matrix (Fin 2) (Fin 2) ℝ := fun _ _ => 1

example : ¬ IsUnit (X2ᵀ * X2).det := by
  simp [X2, Matrix.det_fin_two]

example : ∃ θ₀, ∀ θ, rss X2 y1 θ₀ ≤ rss X2 y1 θ :=
  exists_rss_le X2 y1

example : ∃ θ₀, IsMaxOn (gaussLikelihood X2 y1 1) Set.univ θ₀ :=
  exists_isMaxOn_gaussLikelihood X2 y1 one_ne_zero

theorem ridge_normal_one : (X1ᵀ * X1 + (2 : ℝ) • 1) *ᵥ (fun _ => 1) = X1ᵀ *ᵥ y1 := by
  funext i
  fin_cases i
  simp [X1, y1, mulVec, dotProduct, Fin.sum_univ_two, Matrix.mul_apply, Matrix.add_apply]
  norm_num

example : ridgeEstimate X1 y1 2 = fun _ => 1 :=
  (eq_ridgeEstimate_of_ridge_le X1 y1 two_pos
    (ridge_le_of_normal zero_le_two ridge_normal_one _)).symm

example : softThreshold 1 3 = 2 := by norm_num [softThreshold]

example : softThreshold 1 (-3) = -2 := by norm_num [softThreshold]

example : softThreshold 1 (1 / 2) = 0 := by norm_num [softThreshold]

example (θ : Fin 2 → ℝ) :
    lasso (1 : Matrix (Fin 2) (Fin 2) ℝ) ![3, 1 / 2] 2 ![2, 0] ≤
      lasso (1 : Matrix (Fin 2) (Fin 2) ℝ) ![3, 1 / 2] 2 θ := by
  have h := lasso_softThreshold_le (X := (1 : Matrix (Fin 2) (Fin 2) ℝ)) (by simp) ![3, 1 / 2]
    zero_le_two θ
  convert h using 2
  funext i
  fin_cases i <;> norm_num [softThreshold]

open MeasureTheory ProbabilityTheory in
/-- No noise and a constant prediction `d`: the decomposition, whose terms are zero noise, the
squared bias `(f - d)²`, and zero variance. -/
example (f d : ℝ) :
    (Measure.dirac ())[fun _ : Unit => ((0 : ℝ) + f - d) ^ 2] =
      variance (fun _ : Unit => (0 : ℝ)) (Measure.dirac ()) +
        (f - (Measure.dirac ())[fun _ : Unit => d]) ^ 2 +
        variance (fun _ : Unit => d) (Measure.dirac ()) :=
  BiasVariance.integral_sq_noise_sub (μ := Measure.dirac ()) (ε := fun _ => 0)
    (Yhat := fun _ => d) f (memLp_const 0) (by simp) (memLp_const d) (indepFun_const_left 0 _)

open MeasureTheory ProbabilityTheory in
example (f d : ℝ) :
    variance (fun _ : Unit => (0 : ℝ)) (Measure.dirac ()) +
        (f - (Measure.dirac ())[fun _ : Unit => d]) ^ 2 +
        variance (fun _ : Unit => d) (Measure.dirac ()) = (f - d) ^ 2 := by
  simp

end Cslib.MachineLearning.LeastSquaresTests
