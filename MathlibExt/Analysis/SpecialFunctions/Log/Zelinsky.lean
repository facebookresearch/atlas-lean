/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp

/-! # Zelinsky's upper bound for the logarithm of a ratio of consecutive integers -/

namespace MetaMathlibExt

/-- **Upper bound for $\log(1 + 1/(x-1))$.** For every integer $x \ge 2$,
$\log(1 + 1/(x-1)) \le 1/x + 25/(32x^2)$, where $\log$ is the natural logarithm.

Source: Joshua Zelinsky, *The Sum of the Reciprocals of the Prime Divisors of an Odd
Perfect or Odd Primitive Non-deficient Number*, INTEGERS 25 (2025), Article A59,
Lemma 8 (`integers-2025-A59-lem-8`). -/
public theorem log_one_add_one_div_sub_one_le
    (x : ℕ) (hx : 2 ≤ x) :
    Real.log (1 + 1 / ((x : ℝ) - 1)) ≤ 1 / (x : ℝ) + 25 / (32 * (x : ℝ) ^ 2) := by
  rcases (show x = 2 ∨ 3 ≤ x by omega) with rfl | hx₃
  · norm_num
    linarith [Real.log_two_lt_d9]
  have hx₃' : (3 : ℝ) ≤ x := by exact_mod_cast hx₃
  have hx₀ : 0 < (x : ℝ) := by linarith
  have hx₁ : 0 < (x : ℝ) - 1 := by linarith
  rw [show 1 + 1 / ((x : ℝ) - 1) = x / ((x : ℝ) - 1) by field_simp; ring]
  -- For r = x / (x - 1), log r ≤ sinh (log r) = (r - 1/r) / 2.
  have hr : 1 ≤ (x : ℝ) / (x - 1) := (one_le_div hx₁).mpr (by linarith)
  have hlog := Real.self_le_sinh_iff.mpr (Real.log_nonneg hr)
  rw [Real.sinh_log (div_pos hx₀ hx₁), inv_div] at hlog
  refine hlog.trans ?_
  field_simp
  nlinarith

end MetaMathlibExt
