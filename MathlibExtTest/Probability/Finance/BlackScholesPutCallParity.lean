/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Probability.Finance.BlackScholesPutCallParity

/-! # Tests for `MathlibExt.Probability.Finance.BlackScholesPutCallParity` -/

open MeasureTheory ProbabilityTheory Real MathlibExt.Probability.Finance.BlackScholes
open MathlibExt.Probability.Finance.BlackScholesPutCallParity

namespace MathlibExtTest.BlackScholesPutCallParity

section Examples
example : blackScholesCall 100 100 0 1 1 - blackScholesPut 100 100 0 1 1 = 0 := by
  have h := blackScholes_putCallParity 100 100 0 1 1
  simpa using h

example : 0 ≤ blackScholesCall 100 100 0 1 1 ∧
    blackScholesCall 100 100 0 1 1 ≤ 100 := by
  have h := blackScholesCall_bounds (S0 := (100 : ℝ)) (K := (100 : ℝ))
    (r := (0 : ℝ)) (σ := (1 : ℝ)) (T := (1 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  simpa using h

example : 0 ≤ blackScholesPut 100 100 0 1 1 ∧
    blackScholesPut 100 100 0 1 1 ≤ 100 := by
  have h := blackScholesPut_bounds (S0 := (100 : ℝ)) (K := (100 : ℝ))
    (r := (0 : ℝ)) (σ := (1 : ℝ)) (T := (1 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  simpa using h

example : d1 100 100 0 1 1 = 1 / 2 := by
  have h100 : (100 : ℝ) / 100 = 1 := by norm_num
  simp only [d1]
  rw [h100, Real.log_one, Real.sqrt_one]
  norm_num

example : d2 100 100 0 1 1 = -1 / 2 := by
  have h100 : (100 : ℝ) / 100 = 1 := by norm_num
  have hd1 : d1 100 100 0 1 1 = 1 / 2 := by
    simp only [d1]
    rw [h100, Real.log_one, Real.sqrt_one]
    norm_num
  simp only [d2, hd1, Real.sqrt_one]
  norm_num

example : blackScholesCall 100 100 0 1 1
    = 100 * cdf (gaussianReal 0 1) (1 / 2)
      - 100 * cdf (gaussianReal 0 1) (-1 / 2) := by
  have h100 : (100 : ℝ) / 100 = 1 := by norm_num
  have hd1 : d1 100 100 0 1 1 = 1 / 2 := by
    simp only [d1]
    rw [h100, Real.log_one, Real.sqrt_one]
    norm_num
  have hd2 : d2 100 100 0 1 1 = -1 / 2 := by
    simp only [d2, hd1, Real.sqrt_one]
    norm_num
  have hexp : exp (-((0 : ℝ) * 1)) = 1 := by
    rw [zero_mul, neg_zero, Real.exp_zero]
  simp only [blackScholesCall, hd1, hd2]
  rw [hexp, mul_one]

end Examples

end MathlibExtTest.BlackScholesPutCallParity
