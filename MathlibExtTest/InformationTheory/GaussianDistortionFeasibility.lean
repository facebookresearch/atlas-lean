/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.InformationTheory.GaussianDistortionFeasibility

@[expose] public section

open MathlibExt.InformationTheory.GaussianDistortionFeasibility MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal

namespace MathlibExtTest.InformationTheory.GaussianDistortionFeasibility

/-- The square-error expectation/lower-integral agreement is the public
conversion used by the feasibility characterization. -/
example (μ : ProbabilityMeasure (ℝ × ℝ))
    (hint : Integrable (fun z : ℝ × ℝ => (z.1 - z.2) ^ 2) (μ : Measure (ℝ × ℝ))) :
    ENNReal.ofReal (∫ z, (z.1 - z.2) ^ 2 ∂(μ : Measure (ℝ × ℝ))) =
      ∫⁻ z, ENNReal.ofReal ((z.1 - z.2) ^ 2) ∂(μ : Measure (ℝ × ℝ)) :=
  ofReal_integral_sq_error_eq_lintegral μ hint

end MathlibExtTest.InformationTheory.GaussianDistortionFeasibility
