/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.MachineLearning.Bayesian.StatisticsInterop

@[expose] public section

namespace CSLibExtTest.MachineLearning.Bayesian.StatisticsInteropNormal

open MeasureTheory ProbabilityTheory Real
open Cslib.MachineLearning.Bayesian
open scoped ENNReal NNReal

/-- Use case: standard prior `N(0, 1)`, unit noise. The marginal-law posterior is almost
everywhere the candidate kernel, i.e. `N(x / 2, 1 / 2)`. -/
example :
    ∀ᵐ x ∂(gaussianLikelihood 1 ∘ₘ gaussianReal 0 1),
      ((gaussianLikelihood 1)†(gaussianReal 0 1)) x =
        gaussianReal (x / 2) (1 / 2) := by
  have h := posterior_gaussianMarginalLaw_one (0 : ℝ) (v₀ := (1 : ℝ≥0)) (v := (1 : ℝ≥0))
  filter_upwards [h] with x hx
  rw [hx, normalPosteriorKernel_apply 0 (by positivity) (by positivity) x]
  unfold normalPostMean normalPostVar
  norm_num

/-- Boundary: singletons have zero evidence, so no pointwise posterior formula fires. -/
example : (gaussianLikelihood 1 ∘ₘ gaussianReal 0 1) {(0 : ℝ)} = 0 := by
  rw [gaussianLikelihood_comp_gaussianReal 0 (by positivity) (by positivity)]
  exact gaussianReal_absolutelyContinuous 0 (by positivity) Real.volume_singleton

/-- Zero noise: the one-draw projection is the Dirac mass at the parameter. -/
example : (Measure.pi fun _ : Fin 1 => gaussianReal (0 : ℝ) 0).map (fun s => s 0) =
    Measure.dirac (0 : ℝ) := by
  rw [gaussianMarginalLaw_one_eq_gaussianLikelihood,
    gaussianLikelihood_zero_apply, gaussianReal_zero_var]

end CSLibExtTest.MachineLearning.Bayesian.StatisticsInteropNormal
