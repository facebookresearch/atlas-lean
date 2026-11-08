/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.MachineLearning.Bayesian.BetaBinomial

@[expose] public section

/-!
# Tests for the beta-binomial model
-/

set_option autoImplicit false

open MeasureTheory ProbabilityTheory Cslib.MachineLearning.Bayesian
open scoped ENNReal

namespace CSLibExtTest.MachineLearning.Bayesian.BetaBinomial

instance : IsProbabilityMeasure (betaMeasure 2 2) :=
  isProbabilityMeasureBeta (by norm_num) (by norm_num)

instance : IsProbabilityMeasure (betaMeasure 1 1) :=
  isProbabilityMeasureBeta (by norm_num) (by norm_num)

/-- After 7 successes in 10 trials, a `Beta(2, 2)` prior becomes `Beta(9, 5)`. -/
example : ((binomialKernel 10)†(betaMeasure 2 2)) 7 = betaMeasure 9 5 := by
  rw [posterior_binomialKernel_betaMeasure (by norm_num) (by norm_num) (by norm_num)]
  norm_num

/-- A single success updates `Beta(a, b)` to `Beta(a + 1, b)`. -/
example {a b : ℝ} (ha : 0 < a) (hb : 0 < b) :
    haveI := isProbabilityMeasureBeta ha hb
    ((binomialKernel 1)†(betaMeasure a b)) 1 = betaMeasure (a + 1) b := by
  rw [posterior_binomialKernel_betaMeasure ha hb le_rfl]
  norm_num

/-- **Laplace's rule of succession**: under a uniform prior, after 7 successes in 10 trials the next
trial succeeds with probability `8 / 12 = 2 / 3`. -/
example : (binomialKernel 1 ∘ₘ ((binomialKernel 10)†(betaMeasure 1 1)) 7) {1} =
    ENNReal.ofReal (2 / 3) := by
  rw [posterior_predictive_betaMeasure (by norm_num) (by norm_num) (by norm_num)]
  norm_num

/-- The prior predictive probability of a success under `Beta(2, 2)` is `1 / 2`. -/
example : (binomialKernel 1 ∘ₘ betaMeasure 2 2) {1} = ENNReal.ofReal (1 / 2) := by
  rw [binomialKernel_one_comp_betaMeasure (by norm_num) (by norm_num)]
  norm_num

/-- Under a uniform prior, one success in two trials has evidence `1 / 3`: every count is equally
likely. -/
example : (binomialKernel 2 ∘ₘ betaMeasure 1 1) {1} = ENNReal.ofReal (1 / 3) := by
  rw [binomialKernel_comp_betaMeasure (by norm_num) (by norm_num)]
  congr 1
  have h4 : Real.Gamma 4 = 6 := by
    have := Real.Gamma_nat_eq_factorial 3
    norm_num [Nat.factorial] at this ⊢
  simp only [beta, Nat.cast_one, Real.Gamma_one]
  norm_num [h4]

end CSLibExtTest.MachineLearning.Bayesian.BetaBinomial
