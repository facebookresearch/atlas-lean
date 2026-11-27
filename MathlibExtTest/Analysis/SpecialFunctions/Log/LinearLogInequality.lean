/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Analysis.SpecialFunctions.Log.LinearLogInequality

open Real

-- Lemme 8.5 in its general form.
example {u v x : ℝ} (hu : √(exp 1) ≤ u) (hv : 0 ≤ v) (hx : 0 < x)
    (h : x ≤ u * (v + log x)) : x ≤ 2 * u * (log u + v) :=
  le_two_mul_mul_log_add_of_le_mul_add_log hu hv hx h

-- The endpoint `u = √e`, with `v = 1/2` and `x = √e`: the hypothesis holds with equality, as
-- `log √e = 1/2`, and the conclusion is `√e ≤ 2√e`.
example : √(exp 1) ≤ 2 * √(exp 1) * (log √(exp 1) + 1 / 2) := by
  have hlog : log √(exp 1) = 1 / 2 := by
    rw [← exp_half, log_exp]
  have hx : 0 < √(exp 1) := sqrt_pos.mpr (exp_pos 1)
  refine le_two_mul_mul_log_add_of_le_mul_add_log le_rfl (by norm_num) hx ?_
  rw [hlog]
  norm_num
