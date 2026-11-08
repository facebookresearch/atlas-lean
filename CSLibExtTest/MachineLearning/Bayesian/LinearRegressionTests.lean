/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.MachineLearning.Bayesian.LinearRegression

@[expose] public section

/-!
# Tests for Bayesian linear regression
-/

set_option autoImplicit false

open MeasureTheory ProbabilityTheory Cslib.MachineLearning.Bayesian
open scoped NNReal

namespace CSLibExtTest.MachineLearning.Bayesian.LinearRegression

/-- Two unit inputs, a `N(0, 1)` prior and unit noise: the posterior variance is `1 / 3`. -/
example : linRegPostVar 1 1 ![1, 1] = 1 / 3 := by
  rw [← NNReal.coe_inj, coe_linRegPostVar]
  norm_num [Fin.sum_univ_two]

example (y : Fin 2 → ℝ) : linRegPostMean 0 1 1 ![1, 1] y = (y 0 + y 1) / 3 := by
  norm_num [linRegPostMean, Fin.sum_univ_two]

/-- The posterior after two unit-input responses is `N((y₀ + y₁) / 3, 1 / 3)`. -/
example : ∀ᵐ y, ((linRegLikelihood 1 ![1, 1])†(gaussianReal 0 1)) y =
    gaussianReal ((y 0 + y 1) / 3) (1 / 3) := by
  filter_upwards [posterior_linRegLikelihood_gaussianReal 0 (s₀ := 1) (σ2 := 1) ![1, 1]]
    with y hy
  rw [hy]
  congr 1
  · norm_num [linRegPostMean, Fin.sum_univ_two]
  · rw [← NNReal.coe_inj, coe_linRegPostVar]
    norm_num [Fin.sum_univ_two]

/-- At the new input `x' = 2` the response is then `N(2 (y₀ + y₁) / 3, 4 / 3 + 1)`. -/
example : ∀ᵐ y, linRegPredictive 1 2 ∘ₘ ((linRegLikelihood 1 ![1, 1])†(gaussianReal 0 1)) y =
    gaussianReal (2 * ((y 0 + y 1) / 3)) (7 / 3) := by
  filter_upwards [linRegPredictive_comp_posterior 0 (s₀ := 1) (σ2 := 1) ![1, 1] 2]
    with y hy
  rw [hy]
  congr 1
  · norm_num [linRegPostMean, Fin.sum_univ_two]
  · rw [← NNReal.coe_inj]
    push_cast
    rw [coe_linRegPostVar]
    norm_num [Fin.sum_univ_two]

/-- With no data the posterior is the prior. -/
example (m₀ : ℝ) : ∀ᵐ y, ((linRegLikelihood 1 (Fin.elim0 : Fin 0 → ℝ))†(gaussianReal m₀ 2)) y =
    gaussianReal m₀ 2 := by
  filter_upwards [posterior_linRegLikelihood_gaussianReal m₀ (s₀ := 2) (σ2 := 1) Fin.elim0]
    with y hy
  rw [hy]
  congr 1
  · simp [linRegPostMean]
  · rw [← NNReal.coe_inj, coe_linRegPostVar]
    simp

/-- The likelihood is the product of the responses' Gaussian laws. -/
example (w : ℝ) : linRegLikelihood 1 ![1, 3] w =
    Measure.pi ![gaussianReal w 1, gaussianReal (3 * w) 1] := by
  rw [linRegLikelihood_apply one_ne_zero]
  congr 1
  funext i
  fin_cases i <;> simp [mul_comm]

/-- Precisions add: `1 / s₀ + ∑ xᵢ² / σ² = 1 / 2 + (1 + 9) / 5 = 5 / 2`. -/
example : ((linRegPostVar 2 5 ![1, 3] : ℝ))⁻¹ = 5 / 2 := by
  rw [inv_linRegPostVar (by norm_num) (by norm_num)]
  norm_num [Fin.sum_univ_two]

/-- Zero noise: the responses are exactly `w xᵢ`, not the zero measure. -/
example (w : ℝ) : linRegLikelihood 0 ![1, 3] w = Measure.dirac ![w, w * 3] := by
  rw [linRegLikelihood_zero_apply]
  congr 1
  funext i
  fin_cases i <;> simp

/-- Zero noise at a new input: the response is the point mass at `w x'`. -/
example (w x' : ℝ) : linRegPredictive 0 x' w = Measure.dirac (w * x') := by
  rw [linRegPredictive, Kernel.comap_apply, gaussianLikelihood_zero_apply, gaussianReal_zero_var]

/-- At the input `x' = 0` the prediction is pure noise, `N(0, σ²)`, whatever the data. -/
example : ∀ᵐ y, linRegPredictive 1 0 ∘ₘ ((linRegLikelihood 1 ![1, 1])†(gaussianReal 0 1)) y =
    gaussianReal 0 1 := by
  filter_upwards [linRegPredictive_comp_posterior 0 (s₀ := 1) (σ2 := 1) ![1, 1] 0] with y hy
  rw [hy]
  congr 1
  · simp
  · ext
    simp

/-- With no data the likelihood density is the empty product `1`, even for zero noise. -/
example (w : ℝ) (y : Fin 0 → ℝ) : linRegLikelihoodPDFReal 0 Fin.elim0 w y = 1 := by
  simp [linRegLikelihoodPDFReal]

/-- With zero noise and at least one response, the density formula is `0`. -/
example (w : ℝ) (y : Fin 1 → ℝ) : linRegLikelihoodPDFReal 0 ![1] w y = 0 := by
  simp [linRegLikelihoodPDFReal, gaussianPDFReal]

end CSLibExtTest.MachineLearning.Bayesian.LinearRegression
