/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Probability.Distributions.ZeroInflatedPoisson

/-! # Regressions for the zero-inflated Poisson distribution -/

set_option autoImplicit false

open MeasureTheory ProbabilityTheory
open scoped NNReal unitInterval

-- At either mixing endpoint the entire measure is the corresponding component.
example (μ : ℝ≥0) : zipMeasure (0 : I) μ = poissonMeasure μ := by
  simp [zipMeasure]

example (μ : ℝ≥0) : zipMeasure (1 : I) μ = Measure.dirac 0 := by
  simp [zipMeasure]
