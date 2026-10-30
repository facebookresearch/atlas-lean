/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.MachineLearning.Regression.OptimalPredictors

/-!
# Tests for Bayes-optimal point predictions

* Loss values: `sqLoss 3 1 = 4`, `absLoss 3 1 = 2`.
* The mean of `δ₃` is `3` and minimizes the expected squared loss; the median `3` of `δ₃`
  minimizes the expected absolute loss.
* The posterior mean of a real-parameter model is a Bayes estimator for squared loss, and a
  measurable choice of posterior medians is one for absolute loss.
-/

@[expose] public section

namespace Cslib.MachineLearning.OptimalPredictorsTests

open Cslib.MachineLearning OptimalPredictors MeasureTheory ProbabilityTheory Set
open scoped ENNReal

example : sqLoss 3 1 = 4 := by norm_num [sqLoss]

example : absLoss 3 1 = 2 := by norm_num [absLoss]

example : ∫ t, t ∂(Measure.dirac (3 : ℝ)) = 3 := by simp

example (y : ℝ) :
    ∫⁻ θ, sqLoss θ 3 ∂(Measure.dirac (3 : ℝ)) ≤ ∫⁻ θ, sqLoss θ y ∂(Measure.dirac (3 : ℝ)) := by
  simpa using lintegral_sqLoss_integral_le (Measure.dirac (3 : ℝ)) y

example {𝓧 : Type*} [MeasurableSpace 𝓧] (P : Kernel ℝ 𝓧) [IsMarkovKernel P] (π : Measure ℝ)
    [IsProbabilityMeasure π] :
    IsBayesEstimator sqLoss P (Kernel.deterministic _ (measurable_posteriorMean P π)) π :=
  isBayesEstimator_posteriorMean P π

theorem isMedian_dirac_three : IsMedian (Measure.dirac (3 : ℝ)) 3 := by
  constructor <;> norm_num [measureReal_def]

example (y : ℝ) :
    ∫⁻ θ, absLoss θ 3 ∂(Measure.dirac (3 : ℝ)) ≤ ∫⁻ θ, absLoss θ y ∂(Measure.dirac (3 : ℝ)) :=
  lintegral_absLoss_le_of_isMedian _ isMedian_dirac_three y

example {𝓧 : Type*} [MeasurableSpace 𝓧] (P : Kernel ℝ 𝓧) [IsMarkovKernel P] (π : Measure ℝ)
    [IsProbabilityMeasure π] (f : 𝓧 → ℝ) (hf : IsPosteriorMedian P π f) :
    IsBayesEstimator absLoss P (Kernel.deterministic f hf.measurable) π :=
  hf.isBayesEstimator

end Cslib.MachineLearning.OptimalPredictorsTests
