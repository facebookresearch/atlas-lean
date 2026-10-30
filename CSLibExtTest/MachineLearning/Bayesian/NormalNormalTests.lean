/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.MachineLearning.Bayesian.NormalNormal

@[expose] public section

/-!
# Tests for Normal–Normal conjugacy
-/

set_option autoImplicit false

open MeasureTheory ProbabilityTheory Cslib.MachineLearning.Bayesian
open scoped NNReal

namespace CSLibExtTest.MachineLearning.Bayesian.NormalNormal

/-- Equal prior and noise variances split the difference: the posterior variance halves. -/
example : normalPostVar 1 1 = 1 / 2 := by
  norm_num [normalPostVar]

example (x : ℝ) : normalPostMean 0 1 1 x = x / 2 := by
  norm_num [normalPostMean]

/-- A `N(0, 1)` prior and one observation `x ~ N(θ, 1)` give the posterior `N(x / 2, 1 / 2)`. -/
example : ∀ᵐ x, ((gaussianLikelihood 1)†(gaussianReal 0 1)) x = gaussianReal (x / 2) (1 / 2) := by
  filter_upwards [posterior_gaussianLikelihood_gaussianReal 0 (v₀ := 1) (v := 1)] with x hx
  rw [hx]
  norm_num [normalPostMean, normalPostVar]

/-- The next observation is then `N(x / 2, 3 / 2)`. -/
example : ∀ᵐ x, gaussianLikelihood 1 ∘ₘ ((gaussianLikelihood 1)†(gaussianReal 0 1)) x =
    gaussianReal (x / 2) (3 / 2) := by
  filter_upwards [gaussianLikelihood_comp_posterior 0 (v₀ := 1) (v := 1)] with x hx
  rw [hx]
  congr 1
  · norm_num [normalPostMean]
  · norm_num [normalPostVar]

/-- The marginal of the observation under a `N(3, 2)` prior with noise variance `5`. -/
example : gaussianLikelihood 5 ∘ₘ gaussianReal 3 2 = gaussianReal 3 7 := by
  rw [gaussianLikelihood_comp_gaussianReal 3 (by norm_num) (by norm_num)]
  norm_num

/-- A precise prior barely moves: with `v₀ = 1` and `v = 99` the gain is `1 / 100`. -/
example (x : ℝ) : normalPostMean 0 1 99 x = x / 100 := by
  rw [normalPostMean_eq 0 one_ne_zero x]
  norm_num
  ring

/-- Precisions add: `1 / (4 · 4 / 8) = 1 / 4 + 1 / 4`. -/
example : (normalPostVar 4 4)⁻¹ = 4⁻¹ + 4⁻¹ := inv_normalPostVar (by norm_num) (by norm_num)

/-- With zero noise the observation is the parameter itself. -/
example (θ : ℝ) : gaussianLikelihood 0 θ = Measure.dirac θ := by
  rw [gaussianLikelihood_zero_apply, gaussianReal_zero_var]

/-- The candidate posterior kernel and its disintegration remain available. -/
example : (gaussianLikelihood 1 ∘ₘ gaussianReal 0 1) ⊗ₘ normalPosteriorKernel 0 1 1 =
    (gaussianReal 0 1 ⊗ₘ gaussianLikelihood 1).map Prod.swap :=
  compProd_normalPosteriorKernel 0

end CSLibExtTest.MachineLearning.Bayesian.NormalNormal
