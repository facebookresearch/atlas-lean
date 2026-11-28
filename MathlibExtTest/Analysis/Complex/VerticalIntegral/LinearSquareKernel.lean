/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Analysis.Complex.VerticalIntegral.LinearSquareKernel

/-!
# Tests for the vertical integral of `y^s / (α s + β)²`
-/

open Complex

@[expose] public section

/-- `y = 2`, `α = 1`, `β = 0`: the Perron kernel `2^s / s²` integrates to `log 2`. -/
example : HasVerticalIntegral 1 (fun s => ((2 : ℝ) : ℂ) ^ s / (((1 : ℝ) : ℂ) * s + (0 : ℝ)) ^ 2)
    (Real.log 2) := by
  have := hasVerticalIntegral_cpow_div_mul_add_sq (c := 1) (α := 1) (β := 0) one_pos one_pos
    le_rfl (y := 2) (by norm_num)
  simpa using this

/-- `y = 1` (boundary): the integral is `0`. -/
example (c α β : ℝ) (hc : 0 < c) (hα : 0 < α) (hβ : 0 ≤ β) :
    HasVerticalIntegral c (fun s => ((1 : ℝ) : ℂ) ^ s / ((α : ℂ) * s + β) ^ 2) 0 := by
  simpa using hasVerticalIntegral_cpow_div_mul_add_sq hc hα hβ zero_le_one

/-- `y = 0`: the integral is `0`. -/
example (c α β : ℝ) (hc : 0 < c) (hα : 0 < α) (hβ : 0 ≤ β) :
    HasVerticalIntegral c (fun s => ((0 : ℝ) : ℂ) ^ s / ((α : ℂ) * s + β) ^ 2) 0 := by
  simpa using hasVerticalIntegral_cpow_div_mul_add_sq hc hα hβ le_rfl
