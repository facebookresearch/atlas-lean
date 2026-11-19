/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Probability.Finance.BlackScholes

/-! # Tests for `MathlibExt.Probability.Finance.BlackScholes` -/

open MeasureTheory ProbabilityTheory Real MathlibExt.Probability.Finance.BlackScholes
open scoped NNReal

namespace MathlibExtTest.BlackScholes

example : ∫ x, x ∂(riskNeutralLaw 1 0 1 1) = 1 := by
  have h : ∫ x, x ∂(riskNeutralLaw 1 0 1 1) = 1 * exp ((0 : ℝ) * 1) :=
    integral_id_riskNeutralLaw (by norm_num) (by norm_num)
  simpa using h

example : ∫ z in Set.Ioi (0 : ℝ), exp (0 * z) ∂(gaussianReal 0 1)
    = cdf (gaussianReal 0 1) 0 := by
  have h := setIntegral_Ioi_exp_mul_gaussianReal (0 : ℝ) (0 : ℝ)
  simpa using h

example : exp (-(0 * 1)) * ∫ x, max (x - 1) 0 ∂(riskNeutralLaw 1 0 1 1)
    = cdf (gaussianReal 0 1) (1 / 2) - cdf (gaussianReal 0 1) (-1 / 2) := by
  have h : exp (-((0 : ℝ) * 1)) * ∫ x, max (x - 1) 0 ∂(riskNeutralLaw 1 0 1 1)
      = blackScholesCall 1 1 0 1 1 :=
    discounted_integral_call_riskNeutralLaw (by norm_num) (by norm_num)
      (by norm_num) (by norm_num)
  have hd1 : d1 1 1 0 1 1 = 1 / 2 := by
    unfold d1
    simp [Real.log_one, Real.sqrt_one, div_one]
  have hd2 : d2 1 1 0 1 1 = -1 / 2 := by
    unfold d2
    rw [hd1]
    simp [Real.sqrt_one]
    norm_num
  have hbs : blackScholesCall 1 1 0 1 1
      = cdf (gaussianReal 0 1) (1 / 2) - cdf (gaussianReal 0 1) (-1 / 2) := by
    unfold blackScholesCall
    rw [hd1, hd2]
    simp
  exact h.trans hbs

example : blackScholesCall 1 1 (-1 / 100) 1 1
    = exp (-((-1 / 100 : ℝ) * 1)) * ∫ x, max (x - 1) 0
      ∂(riskNeutralLaw 1 (-1 / 100) 1 1) := by
  have h : exp (-(((-1 / 100 : ℝ)) * 1)) * ∫ x, max (x - 1) 0
        ∂(riskNeutralLaw 1 (-1 / 100) 1 1)
      = blackScholesCall 1 1 (-1 / 100) 1 1 :=
    discounted_integral_call_riskNeutralLaw (by norm_num) (by norm_num)
      (by norm_num) (by norm_num)
  exact h.symm

end MathlibExtTest.BlackScholes
