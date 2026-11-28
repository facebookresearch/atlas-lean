/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Combinatorics.Enumerative.AlzerRichardsReciprocalSum
import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.NormNum

open Finset MetaMathlibExt

-- At p = 1 the derivative is 1 and the only binomial summand vanishes.
example {z : ℂ} (hz : z ≠ 0) : 1 - z * (1 / z) = 0 := by
  simpa [sum_range_succ] using mul_pow_pred_sub_pow_mul_sum_inv_eq_sum_choose
    (p := 1) (by decide) (z := z) (by simpa using hz)

-- A negative half-integer gives two nonzero summands of opposite signs.
example :
    ∑ k ∈ range 3, (-1 : ℂ) ^ (3 - k) * (k : ℂ) ^ 3 / (-1 / 2 - k) *
        Ring.choose (-1 / 2 : ℂ) k * Ring.choose (-1 / 2 - (k : ℂ) - 1) (3 - k - 1) =
      11 / 30 := by
  rw [← mul_pow_pred_sub_pow_mul_sum_inv_eq_sum_choose (by decide)]
  · norm_num [sum_range_succ]
  · intro k hk
    interval_cases k <;> norm_num
