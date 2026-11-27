/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.MeasureTheory.Integral.ImproperIntegralComparison
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic

/-! # Tests for `MathlibExt.MeasureTheory.Integral.ImproperIntegralComparison` -/

namespace MathlibExtTest.ImproperIntegralComparison

open MathlibExt.MeasureTheory.Integral.ImproperIntegralComparisonWanted MeasureTheory Filter

/-- A continuous function is interval integrable on every `[0, b]`. -/
lemma intervalIntegrable_of_continuous {f : ℝ → ℝ} (hf : Continuous f) (b : ℝ) :
    IntervalIntegrable f volume 0 b :=
  hf.intervalIntegrable _ _

/-- `∫_0^∞ e^{-x}` converges. -/
lemma exists_tendsto_integral_exp_neg :
    ∃ L : ℝ, Tendsto (fun b ↦ ∫ x in (0 : ℝ)..b, Real.exp (-x)) atTop (nhds L) :=
  ⟨_, intervalIntegral_tendsto_integral_Ioi 0 (integrableOn_exp_neg_Ioi 0) tendsto_id⟩

-- Test section: comparison test. `0 ≤ e^{-x} sin² x ≤ e^{-x}`, so `∫_0^∞ e^{-x} sin² x`
-- converges.
example : ∃ L : ℝ,
    Tendsto (fun b ↦ ∫ x in (0 : ℝ)..b, Real.exp (-x) * Real.sin x ^ 2) atTop (nhds L) := by
  refine improper_integral_comparison_test (g := fun x ↦ Real.exp (-x))
    (fun x _ ↦ ⟨by positivity, ?_⟩)
    (fun b _ ↦ intervalIntegrable_of_continuous (by fun_prop) b)
    (fun b _ ↦ intervalIntegrable_of_continuous (by fun_prop) b)
    exists_tendsto_integral_exp_neg
  exact mul_le_of_le_one_right (Real.exp_pos _).le (Real.sin_sq_le_one x)

-- Test section: limit comparison test. `3 e^{-x} / e^{-x} → 3 ≠ 0`, so `∫_0^∞ 3 e^{-x}`
-- converges together with `∫_0^∞ e^{-x}`.
example : ∃ L : ℝ,
    Tendsto (fun b ↦ ∫ x in (0 : ℝ)..b, 3 * Real.exp (-x)) atTop (nhds L) := by
  refine (improper_integral_limit_comparison_test (L := 3) (g := fun x ↦ Real.exp (-x))
    (fun x _ ↦ by positivity) (fun x _ ↦ by positivity)
    (fun b _ ↦ intervalIntegrable_of_continuous (by fun_prop) b)
    (fun b _ ↦ intervalIntegrable_of_continuous (by fun_prop) b)
    (by norm_num) ?_).2 exists_tendsto_integral_exp_neg
  refine tendsto_const_nhds.congr fun x ↦ ?_
  rw [mul_div_assoc, div_self (Real.exp_pos _).ne', mul_one]

-- Test section: limit comparison test, forward direction, at an arbitrary lower endpoint `a` and
-- with a ratio `e^{-x} / (e^{-x} (1 + e^{-x})) = 1 / (1 + e^{-x})` that tends to `1` without being
-- constant. Since `∫_a^∞ e^{-x}` converges, so does `∫_a^∞ e^{-x} (1 + e^{-x})`.
example (a : ℝ) : ∃ L : ℝ,
    Tendsto (fun b ↦ ∫ x in a..b, Real.exp (-x) * (1 + Real.exp (-x))) atTop (nhds L) := by
  have hr : Tendsto (fun x ↦ Real.exp (-x) / (Real.exp (-x) * (1 + Real.exp (-x)))) atTop
      (nhds 1) := by
    have h := (tendsto_const_nhds (x := (1 : ℝ))).div
      (tendsto_const_nhds.add Real.tendsto_exp_neg_atTop_nhds_zero)
      (by norm_num : (1 : ℝ) + 0 ≠ 0)
    rw [add_zero, div_one] at h
    refine h.congr fun x ↦ ?_
    rw [Pi.div_apply, div_mul_eq_div_div, div_self (Real.exp_pos _).ne']
  exact (improper_integral_limit_comparison_test (L := 1) (f := fun x ↦ Real.exp (-x))
    (g := fun x ↦ Real.exp (-x) * (1 + Real.exp (-x)))
    (fun x _ ↦ by positivity) (fun x _ ↦ by positivity)
    (fun b _ ↦ (by fun_prop : Continuous fun x ↦ Real.exp (-x)).intervalIntegrable a b)
    (fun b _ ↦ (by fun_prop : Continuous fun x ↦ Real.exp (-x) * (1 + Real.exp (-x))
      ).intervalIntegrable a b)
    one_ne_zero hr).1
    ⟨_, intervalIntegral_tendsto_integral_Ioi a (integrableOn_exp_neg_Ioi a) tendsto_id⟩

end MathlibExtTest.ImproperIntegralComparison
