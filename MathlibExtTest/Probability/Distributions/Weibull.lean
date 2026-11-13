/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Probability.Distributions.Weibull

/-!
# Tests for the Weibull law

The probability instance, survival `1` at `t = 0`, a concrete survival value, the cumulative
hazard, the zero measure outside `k, l > 0`, no mass on `(-∞, 0]`, the density at shape `1`, and
the shape-`1` survival checked against Mathlib's exponential CDF at a concrete point.
-/

open MeasureTheory ProbabilityTheory Real Set

namespace MathlibExtTest.Probability.Distributions.Weibull

/-- Weibull with shape `2` and scale `3` is a probability measure. -/
example : IsProbabilityMeasure (weibullMeasure 2 3) :=
  isProbabilityMeasure_weibullMeasure (by norm_num) (by norm_num)

/-- Survival at `t = 0` is `1`. -/
example : (weibullMeasure 2 3).real (Ioi 0) = 1 := by
  rw [weibullMeasure_real_Ioi (by norm_num) (by norm_num) le_rfl]
  norm_num

/-- Concrete survival: shape `2`, scale `2`, `t = 2` gives `exp (-1)`. -/
example : (weibullMeasure 2 2).real (Ioi 2) = exp (-1) := by
  rw [weibullMeasure_real_Ioi (by norm_num) (by norm_num) (by norm_num)]
  norm_num

/-- Concrete cumulative hazard: shape `3`, scale `1`, `t = 2` gives `8`. -/
example : -log ((weibullMeasure 3 1).real (Ioi 2)) = 8 := by
  rw [neg_log_weibullMeasure_real_Ioi (by norm_num) (by norm_num) (by norm_num)]
  norm_num

/-- Nonpositive shape gives the zero measure. -/
example (l : ℝ) : weibullMeasure 0 l = 0 := weibullMeasure_of_nonpos_left le_rfl l

/-- Nonpositive scale gives the zero measure. -/
example (k : ℝ) : weibullMeasure k (-1) = 0 := weibullMeasure_of_nonpos_right k (by norm_num)

/-- No mass on `(-∞, 0]`. -/
example : weibullMeasure 2 3 (Iic 0) = 0 := weibullMeasure_Iic_zero 2 3

/-- The density vanishes at `0` and below. -/
example (k l : ℝ) : weibullPDFReal k l 0 = 0 := by simp [weibullPDFReal]

/-- Nonpositive shape: the density is `0` even at a positive point. -/
example : weibullPDFReal 0 1 1 = 0 := weibullPDFReal_of_nonpos_left le_rfl 1 1

/-- Negative scale: the density is `0` at a positive point (it would be `2 e⁻¹` unguarded). -/
example : weibullPDFReal 2 (-1) 1 = 0 := weibullPDFReal_of_nonpos_right 2 (by norm_num) 1

/-- The same, by unfolding the definition. -/
example : weibullPDFReal (-1) 2 3 = 0 := by norm_num [weibullPDFReal]

/-- At shape `1` and scale `1` the density is `exp (-x)` on `x > 0`. -/
example {x : ℝ} (hx : 0 < x) : weibullPDFReal 1 1 x = exp (-x) := by
  simp [weibullPDFReal, hx]

/-- Shape-`1` Weibull survival agrees with Mathlib's exponential CDF at scale `2`, `t = 3`. -/
example : (weibullMeasure 1 2).real (Ioi 3) = exp (-(3 / 2)) ∧
    (expMeasure 2⁻¹).real (Ioi 3) = exp (-(3 / 2)) := by
  constructor
  · rw [weibullMeasure_real_Ioi one_pos (by norm_num) (by norm_num), rpow_one]
  · have := isProbabilityMeasure_expMeasure (r := 2⁻¹) (by norm_num)
    rw [← compl_Iic, probReal_compl_eq_one_sub measurableSet_Iic, ← cdf_eq_real,
      cdf_expMeasure_eq (by norm_num), ite_eq_left (by norm_num)]
    ring_nf

/-- The shape-`1` measure equality, instantiated. -/
example : weibullMeasure 1 2 = expMeasure 2⁻¹ := weibullMeasure_one (by norm_num)

end MathlibExtTest.Probability.Distributions.Weibull
