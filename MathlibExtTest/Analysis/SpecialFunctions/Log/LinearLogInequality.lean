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

-- The boundary case `u = √e`, `v = 0`: every `x > 0` with `x ≤ √e log x` is at most `√e`.
example {x : ℝ} (hx : 0 < x) (h : x ≤ √(exp 1) * (0 + log x)) : x ≤ √(exp 1) := by
  have := le_two_mul_mul_log_add_of_le_mul_add_log le_rfl le_rfl hx h
  have hlog : log √(exp 1) = 1 / 2 := by
    rw [← exp_half, log_exp]
  rw [hlog] at this
  linarith
