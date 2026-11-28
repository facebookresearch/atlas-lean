/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Analysis.Complex.VerticalIntegral.Integrable
public import MathlibExt.Analysis.Complex.VerticalIntegral.CauchyKernel

/-!
# Tests for integrability on a vertical line
-/

@[expose] public section

open Complex MeasureTheory

example (t : ℝ) : (2 : ℝ) ≤ ‖((2 : ℝ) : ℂ) + t * I‖ := le_norm_ofReal_add_mul_I two_pos t

/-- `1 / s²` is integrable on the line `re s = 1`. -/
example : VerticalIntegrable (fun s : ℂ => 1 / s ^ 2) 1 :=
  verticalIntegrable_of_norm_le_div_pow (n := 0) (M := 1) one_pos zero_le_one
    (by
      refine Continuous.div continuous_const (by fun_prop) fun t => ?_
      exact pow_ne_zero 2 (ofReal_add_mul_I_ne_zero (Or.inl one_ne_zero)))
    (fun t => by simp)

/-- The uniform truncated `L¹` bound for `1 / (1 + it)²`: at most `π`. -/
example {R : ℝ} (hR : 0 ≤ R) :
    ∫ t in (-R)..R, ‖1 / (((1 : ℝ) : ℂ) + t * I) ^ 2‖ ≤ 1 / 1 ^ (0 + 1) * Real.pi :=
  intervalIntegral_norm_le_of_norm_le_div_pow one_pos zero_le_one
    (by
      refine Continuous.div continuous_const (by fun_prop) fun t => ?_
      exact pow_ne_zero 2 (ofReal_add_mul_I_ne_zero (Or.inl one_ne_zero)))
    (fun t => by simp) hR
