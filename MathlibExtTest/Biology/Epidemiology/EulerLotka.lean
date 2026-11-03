/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Biology.Epidemiology.EulerLotka

/-!
# Tests for the Euler–Lotka equation

Non-vacuity witness: a fixed generation interval `T = 2` and growth rate `r = 1/2` solve the
renewal equation with `R = e`. Concrete values: exponential interval with mean `2` and
`r = 1/2` gives `R = 2`; gamma shape `2`, rate `1`, `r = 1` gives `R = 4`. The two closed forms
compare as `1 + r T ≤ e^{r T}` (the exponential law is more spread than the fixed interval).
Boundary case: `r = 0` gives `R = 1` for every generation-interval law.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Real

namespace MathlibExtTest.Biology.Epidemiology.EulerLotka

open MathlibExt.Biology.Epidemiology.EulerLotka

-- Non-vacuity witness: exponential growth `e^{t/2}` with a fixed interval `2` solves the
-- renewal equation with `R = e`.
example : ∀ t, 1 * exp (1 / 2 * t) =
    exp 1 * ∫ a, 1 * exp (1 / 2 * (t - a)) ∂(Measure.dirac (2 : ℝ)) := by
  rw [renewal_exp_iff_reproductionNumber _ _ one_ne_zero (integrable_dirac enorm_lt_top),
    reproductionNumber_dirac]
  norm_num

-- Fixed interval: `R = e^{r T}`.
example : reproductionNumber (Measure.dirac (2 : ℝ)) (1 / 2) = exp 1 := by
  rw [reproductionNumber_dirac]; norm_num

-- Exponential interval with mean `2` at `r = 1/2`: `R = 1 + 1 = 2`.
example : reproductionNumber (expMeasure (2 : ℝ)⁻¹) (1 / 2) = 2 := by
  rw [reproductionNumber_expMeasure (by norm_num) (by norm_num)]; norm_num

-- Gamma interval, shape `2`, rate `1`, at `r = 1`: `R = (1 + 1)^2 = 4`.
example : reproductionNumber (gammaMeasure 2 1) 1 = 4 := by
  rw [reproductionNumber_gammaMeasure (by norm_num) (by norm_num) (by norm_num)]
  norm_num

-- The exponential interval gives a smaller `R` than the fixed interval of the same mean.
example : reproductionNumber (expMeasure (2 : ℝ)⁻¹) (1 / 2) ≤
    reproductionNumber (Measure.dirac (2 : ℝ)) (1 / 2) := by
  rw [reproductionNumber_expMeasure (by norm_num) (by norm_num), reproductionNumber_dirac]
  have := add_one_le_exp (1 / 2 * 2 : ℝ)
  linarith

-- Boundary: zero growth rate gives `R = 1` for every probability law.
example (g : Measure ℝ) [IsProbabilityMeasure g] : reproductionNumber g 0 = 1 := by
  simp [reproductionNumber, mgf]

end MathlibExtTest.Biology.Epidemiology.EulerLotka
