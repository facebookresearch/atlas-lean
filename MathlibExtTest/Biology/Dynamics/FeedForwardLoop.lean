/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Biology.Dynamics.FeedForwardLoop

/-! Tests for the coherent feed-forward loop: the ON delay for concrete rates, a gate shut by
`X* = 0`, and instances of the ON-delay, delayed-rise and no-OFF-delay theorems. -/

open Real

namespace MathlibExtTest.Biology.Dynamics.FeedForwardLoop

open MathlibExt.Biology.Dynamics.FeedForwardLoop

/-- `α_y = 1`, `β_y = 2` (`Y_st = 2`), `K_yz = 1`: `T_on = log 2`. -/
example : onDelay 1 2 1 = log 2 := by norm_num [onDelay]

example : yOn 1 2 0 = 0 := by simp [yOn]

/-- `Y` reaches the threshold exactly at `T_on`. -/
example : yOn 1 2 (log 2) = 1 := by
  simp [yOn, exp_neg, exp_log two_pos]; norm_num

/-- The AND gate is shut when `X* = 0`, whatever `Y` is. -/
example (y : ℝ) : andGate (1 / 2) 1 3 0 y = 0 := by norm_num [andGate]

example : andGate (1 / 2) 1 3 1 2 = 3 := by norm_num [andGate]

example : 0 < onDelay 1 2 1 := onDelay_pos one_pos two_pos one_pos (by norm_num)

/-- The FFL target is still `0` at `t = 0`. -/
example : fflOn 1 2 1 1 (1 / 2) 1 0 = 0 :=
  ffl_on_eq_zero one_pos two_pos (by norm_num) le_rfl (onDelay_pos one_pos two_pos one_pos
    (by norm_num)).le

example : fflOn 1 2 1 1 (1 / 2) 1 (log 2 + 1) = 1 - exp (-1) := by
  rw [ffl_on_eq one_pos two_pos one_pos (by norm_num) one_pos (by norm_num) (by
    rw [show onDelay 1 2 1 = log 2 by norm_num [onDelay]]; linarith)]
  rw [show onDelay 1 2 1 = log 2 by norm_num [onDelay]]; ring_nf

example : 0 < simpleOn 1 1 (1 / 2) 1 := simple_on_pos one_pos one_pos (by norm_num) one_pos

/-- No OFF delay, for an arbitrary trajectory of `Y`. -/
example (Y : ℝ → ℝ) (t : ℝ) : fflOff 1 1 (1 / 2) 1 1 Y t = exp (-t) := by
  obtain ⟨h1, h2⟩ := ffl_off_eq_simple_off (αz := 1) (βz := 1) (Kyz := 1) (z₀ := 1)
    (by norm_num : (0 : ℝ) ≤ 1 / 2) Y t
  rw [h1, h2]; simp

end MathlibExtTest.Biology.Dynamics.FeedForwardLoop
