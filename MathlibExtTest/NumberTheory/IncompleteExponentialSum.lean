/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.NumberTheory.IncompleteExponentialSum
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity

/-! # Tests for `MathlibExt.NumberTheory.IncompleteExponentialSum` -/

namespace MathlibExtTest.IncompleteExponentialSum

open MetaMathlibExt

-- Test section: special values. At `x = 1/2`, where `sin(π/2) = 1`, the bound reads
-- `1 < 10 / (3π)`, that is `π < 10/3`.
example : Real.pi < 10 / 3 := by
  have h := one_div_sin_pi_lt (1 / 2) (by norm_num) (by norm_num)
  have hpi := Real.pi_pos
  rw [show Real.pi * (1 / 2) = Real.pi / 2 by ring, Real.sin_pi_div_two,
    show (1 : ℝ) / Real.pi * (1 / (1 / 2) + 2 * (1 / 2) / (1 - (1 / 2) ^ 2)) =
      10 / 3 / Real.pi by field_simp; norm_num,
    div_one, lt_div_iff₀ hpi] at h
  linarith

-- At `x = 1/6`, where `sin(π/6) = 1/2`, the bound is nearly sharp: it reads
-- `2 < 222 / (35π)`, that is `π < 111/35 ≈ 3.171`.
example : Real.pi < 111 / 35 := by
  have h := one_div_sin_pi_lt (1 / 6) (by norm_num) (by norm_num)
  have hpi := Real.pi_pos
  rw [show Real.pi * (1 / 6) = Real.pi / 6 by ring, Real.sin_pi_div_six,
    show (1 : ℝ) / Real.pi * (1 / (1 / 6) + 2 * (1 / 6) / (1 - (1 / 6) ^ 2)) =
      222 / 35 / Real.pi by field_simp; norm_num,
    lt_div_iff₀ hpi] at h
  linarith

-- Test section: the equivalent lower bound `π x (1 - x²) / (1 + x²) < sin(πx)` on `(0, 1)`,
-- using `1/x + 2x/(1 - x²) = (1 + x²) / (x (1 - x²))`.
example (x : ℝ) (hx₀ : 0 < x) (hx₁ : x < 1) :
    Real.pi * x * (1 - x ^ 2) / (1 + x ^ 2) < Real.sin (Real.pi * x) := by
  have hpi := Real.pi_pos
  have hx2 : 0 < 1 - x ^ 2 := by nlinarith
  have hs : 0 < Real.sin (Real.pi * x) :=
    Real.sin_pos_of_pos_of_lt_pi (by positivity) (by nlinarith)
  have hc : 0 < Real.pi * x * (1 - x ^ 2) / (1 + x ^ 2) := by positivity
  have h := one_div_sin_pi_lt x hx₀ hx₁
  rw [show 1 / Real.pi * (1 / x + 2 * x / (1 - x ^ 2)) =
    1 / (Real.pi * x * (1 - x ^ 2) / (1 + x ^ 2)) by field_simp; ring] at h
  exact (one_div_lt_one_div hs hc).1 h

-- Test section: both hypotheses are needed. At `x = 0` both sides are `0`, by the junk value
-- `1 / 0 = 0`.
example : ¬ 1 / Real.sin (Real.pi * 0) < (1 / Real.pi) * (1 / 0 + 2 * 0 / (1 - 0 ^ 2)) := by
  simp

-- At `x = 2`, the left side is `1 / sin(2π) = 0` but the right side is `-5 / (6π) < 0`.
example : ¬ 1 / Real.sin (Real.pi * 2) < (1 / Real.pi) * (1 / 2 + 2 * 2 / (1 - 2 ^ 2)) := by
  have hpi := Real.pi_pos
  rw [show Real.pi * 2 = 2 * Real.pi by ring, Real.sin_two_pi, div_zero, not_lt,
    show (1 : ℝ) / 2 + 2 * 2 / (1 - 2 ^ 2) = -(5 / 6) by norm_num, mul_neg, neg_nonpos]
  positivity

end MathlibExtTest.IncompleteExponentialSum
