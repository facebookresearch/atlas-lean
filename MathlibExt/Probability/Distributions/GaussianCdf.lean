/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Probability.CdfContinuityPoints
public import Mathlib.Probability.CDF
public import Mathlib.Probability.Distributions.Gaussian.Real

/-!
# Continuity of the Gaussian cdf

For every real mean and every nonzero variance, the cumulative distribution
function of the Gaussian law is continuous. The degenerate zero-variance case
is a Dirac mass whose cdf jumps, so the nonzero hypothesis cannot be dropped.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory

namespace ProbabilityTheory

/-- The cdf of a Gaussian law with nonzero variance is continuous. -/
theorem continuous_cdf_gaussianReal (μ : ℝ) {v : NNReal} (hv : v ≠ 0) :
    Continuous (cdf (gaussianReal μ v)) := by
  have hnull := nullSingletonClass_gaussianReal (μ := μ) hv
  rw [continuous_iff_continuousAt]
  intro x
  rw [MathlibExt.Probability.CdfContinuityPoints.continuousAt_cdf_iff_measure_singleton_eq_zero]
  exact @measure_singleton _ _ _ hnull x

end ProbabilityTheory
