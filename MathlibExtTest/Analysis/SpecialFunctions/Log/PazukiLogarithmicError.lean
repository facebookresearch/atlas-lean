/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Analysis.SpecialFunctions.Log.PazukiLogarithmicError
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.Complex.ExponentialBounds

open Real

-- The step `log (2y + d) ≤ (log (6 + d) / log 3) log y`, in general.
example {y d : ℝ} (hy : 3 ≤ y) (hd : 0 ≤ d) :
    log (2 * y + d) ≤ log (6 + d) / log 3 * log y :=
  Pazuki.log_two_mul_add_le hy hd

-- At `y = 3`, `d = 0` the step is an equality: `log 6 = (log 6 / log 3) log 3`.
example : log (2 * 3 + 0) = log (6 + 0) / log 3 * log 3 := by
  have : log 3 ≠ 0 := (log_pos (by norm_num)).ne'
  field_simp
  norm_num

-- Pazuki's Lemma 5.7 in general.
example {a b c : ℝ} (hb : 1 ≤ b) (hc : 2 ≤ c) (h : |a - b| ≤ c * log (2 + a)) :
    |a - b| ≤ Pazuki.lemma57Constant c * log (2 + min a b) :=
  Pazuki.abs_sub_le_mul_log_two_add_min hb hc h

-- `a = 0 < 1`, outside Pazuki's range `a ≥ 1`: with `b = 1` and `c = 2`, the hypothesis
-- `1 ≤ 2 log 2` holds, and the lemma bounds `|0 - 1|` by `c̃ log 2`.
example : |(0 : ℝ) - 1| ≤ Pazuki.lemma57Constant 2 * log (2 + min 0 1) := by
  refine Pazuki.abs_sub_le_mul_log_two_add_min le_rfl le_rfl ?_
  rw [show (0 : ℝ) - 1 = -1 by norm_num, abs_neg, abs_one, add_zero]
  linarith [log_two_gt_d9]

-- `a = 10`, `b = 4`, `c = 3`: the hypothesis `6 ≤ 3 log 12` holds (`log 12 > 2`), and the lemma
-- gives `6 ≤ c̃ log 6` with `min 10 4 = 4`.
example : |(10 : ℝ) - 4| ≤ Pazuki.lemma57Constant 3 * log (2 + min 10 4) := by
  refine Pazuki.abs_sub_le_mul_log_two_add_min (by norm_num) (by norm_num) ?_
  rw [show (10 : ℝ) - 4 = 6 by norm_num, abs_of_pos (by norm_num : (0 : ℝ) < 6)]
  have h12 : 2 < log (2 + 10) := by
    rw [lt_log_iff_exp_lt (by norm_num)]
    have := exp_one_lt_d9
    calc exp 2 = exp 1 * exp 1 := by rw [← exp_add]; norm_num
      _ < 2.7182818286 * 2.7182818286 := by gcongr
      _ < 2 + 10 := by norm_num
  linarith
