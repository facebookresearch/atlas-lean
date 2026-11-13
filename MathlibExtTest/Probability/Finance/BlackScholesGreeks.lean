/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Probability.Finance.BlackScholesGreeks

/-! # Tests for `MathlibExt.Probability.Finance.BlackScholesGreeks` -/

open MeasureTheory ProbabilityTheory Real MathlibExt.Probability.Finance.BlackScholes
open MathlibExt.Probability.Finance.BlackScholesGreeks

namespace MathlibExtTest.BlackScholesGreeks

section Examples
example : blackScholesDelta 100 100 0 1 1
    = cdf (gaussianReal 0 1) (1 / 2) := by
  unfold blackScholesDelta
  have h : d1 100 100 0 1 1 = 1 / 2 := by
    unfold d1
    simp [Real.sqrt_one]
  rw [h]

example : blackScholesVega 100 100 0 1 1
    = 100 * gaussianPDFReal 0 1 (1 / 2) * 1 := by
  unfold blackScholesVega
  have h : d1 100 100 0 1 1 = 1 / 2 := by
    unfold d1
    simp [Real.sqrt_one]
  rw [h]
  simp [Real.sqrt_one]

example : 0 < blackScholesVega 100 100 0 1 1 :=
  blackScholes_vega_pos (by norm_num) (by norm_num) (by norm_num) (by norm_num)

example : 100 * gaussianPDFReal 0 1 (1 / 2)
    = 100 * gaussianPDFReal 0 1 (-1 / 2) := by
  have h1 : d1 100 100 (0:ℝ) 1 1 = 1 / 2 := by
    unfold d1
    simp [Real.sqrt_one]
  have h2 : d2 100 100 (0:ℝ) 1 1 = -1 / 2 := by
    unfold d2
    rw [h1]
    simp [Real.sqrt_one]
    ring
  have hident := blackScholes_phi_identity (S0 := 100) (K := 100) (r := 0) (σ := 1) (T := 1)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  rw [h1, h2] at hident
  simpa using hident

end Examples

end MathlibExtTest.BlackScholesGreeks
