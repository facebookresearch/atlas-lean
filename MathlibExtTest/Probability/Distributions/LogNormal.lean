/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Probability.Distributions.LogNormal

/-!
# Tests for the log-normal law

The probability instance, no mass on `(-∞, 0]`, the CDF identity at the median point
`t = exp μ`, the degenerate case `v = 0` as a Dirac mass at `exp μ`, and the mean at concrete
parameters, cross-checked against the Dirac mass when `v = 0`.
-/

open MeasureTheory ProbabilityTheory Real Set

open scoped NNReal

namespace MathlibExtTest.Probability.Distributions.LogNormal

/-- The log-normal law is a probability measure (found by instance search). -/
example (μ : ℝ) (v : ℝ≥0) : logNormalMeasure μ v univ = 1 := measure_univ

/-- No mass on `(-∞, 0]`. -/
example : logNormalMeasure 1 2 (Iic 0) = 0 := logNormalMeasure_Iic_zero 1 2

/-- The CDF at `t = exp μ` is the Gaussian CDF at its mean. -/
example (μ : ℝ) (v : ℝ≥0) :
    (logNormalMeasure μ v).real (Iic (exp μ)) = (gaussianReal μ v).real (Iic μ) := by
  rw [logNormalMeasure_real_Iic μ v (exp_pos μ), log_exp]

/-- Zero log-variance: the law is the Dirac mass at `exp μ`. -/
example (μ : ℝ) : logNormalMeasure μ 0 = Measure.dirac (exp μ) := by
  simp [logNormalMeasure, Measure.map_dirac' measurable_exp]

/-- Mean at `μ = 0`, `v = 2`: `exp 1`. -/
example : ∫ x, x ∂(logNormalMeasure 0 2) = exp 1 := by
  rw [integral_id_logNormalMeasure]
  norm_num

/-- With `v = 0` the mean formula agrees with the Dirac mass at `exp μ`. -/
example (μ : ℝ) : ∫ x, x ∂(logNormalMeasure μ 0) = ∫ x, x ∂(Measure.dirac (exp μ)) := by
  rw [integral_id_logNormalMeasure, integral_dirac]
  simp

end MathlibExtTest.Probability.Distributions.LogNormal
