/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Probability.Finance.BlackScholesZeroVolatility

/-! # Tests for `MathlibExt.Probability.Finance.BlackScholesZeroVolatility` -/

open MeasureTheory ProbabilityTheory Real MathlibExt.Probability.Finance.BlackScholes
open MathlibExt.Probability.Finance.BlackScholesZeroVolatility
open Filter Topology

namespace MathlibExtTest.BlackScholesZeroVolatility

section Examples
example : Tendsto (fun σ => blackScholesCall 100 100 0 σ 1) (𝓝[>] 0) (𝓝 0) := by
  have h := tendsto_blackScholesCall_zeroVol (S0 := (100 : ℝ)) (K := (100 : ℝ))
    (r := (0 : ℝ)) (T := (1 : ℝ)) (by norm_num) (by norm_num) (by norm_num)
  have hlim : max ((100 : ℝ) - 100 * exp (-((0 : ℝ) * 1))) 0 = 0 := by
    have hexp : exp (-((0 : ℝ) * 1)) = 1 := by simp
    rw [hexp]
    norm_num
  rwa [hlim] at h

example : Tendsto (fun σ => blackScholesCall 120 100 0 σ 1) (𝓝[>] 0) (𝓝 20) := by
  have h := tendsto_blackScholesCall_zeroVol (S0 := (120 : ℝ)) (K := (100 : ℝ))
    (r := (0 : ℝ)) (T := (1 : ℝ)) (by norm_num) (by norm_num) (by norm_num)
  have hlim : max ((120 : ℝ) - 100 * exp (-((0 : ℝ) * 1))) 0 = 20 := by
    have hexp : exp (-((0 : ℝ) * 1)) = 1 := by simp
    rw [hexp]
    norm_num
  rwa [hlim] at h

end Examples

end MathlibExtTest.BlackScholesZeroVolatility
