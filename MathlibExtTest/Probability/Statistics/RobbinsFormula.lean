/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Probability.Statistics.RobbinsFormula

/-!
# Tests for Robbins' formula

For a point-mass prior at the rate `2`, the posterior mean is `2`, and Robbins' formula
recovers it from the marginal probabilities of the counts `0` and `1`.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory
open scoped NNReal

namespace MathlibExtTest.Probability.Statistics.RobbinsFormula

/-- With the prior `δ₂`, Robbins' formula at `x = 0` gives `1 · f(1) / f(0) = 2`. -/
example : poissonPosteriorMean (Measure.dirac (2 : ℝ≥0)) 0 = 2 := by
  rw [poissonPosteriorMean_eq]
  simp only [poissonMixtureMass, integral_dirac, poissonMeasure_real_singleton]
  have h : Real.exp (-((2 : ℝ≥0) : ℝ)) ≠ 0 := (Real.exp_pos _).ne'
  field_simp
  norm_num

end MathlibExtTest.Probability.Statistics.RobbinsFormula
