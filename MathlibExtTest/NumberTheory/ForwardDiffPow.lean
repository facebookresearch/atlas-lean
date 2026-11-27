/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

import MathlibExt.NumberTheory.ForwardDiffPow
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

namespace MathlibExt.NumberTheory.FiniteSumsFibLucasWanted

-- At order zero the sum gives back the original power for every step.
example (r x : ℝ) (n : ℕ) :
    ∑ j ∈ Finset.range 1, (-1 : ℝ) ^ (0 - j) * (Nat.choose 0 j : ℝ) * (x + r * j) ^ n =
      x ^ n :=
  (iterate_forwardDiff_pow_eq_sum r x 0 n).symm

-- With zero step, every positive order gives cancellation.
example (x : ℝ) (k n : ℕ) :
    ∑ j ∈ Finset.range (k + 2), (-1 : ℝ) ^ (k + 1 - j) * (Nat.choose (k + 1) j : ℝ) * x ^ n =
      0 := by
  simpa [Function.iterate_succ_apply'] using (iterate_forwardDiff_pow_eq_sum 0 x (k + 1) n).symm

-- The second difference of a square is independent of the evaluation point.
example (r x : ℝ) : (fwdDiff r)^[2] (fun y : ℝ => y ^ 2) x = 2 * r ^ 2 := by
  calc
    _ = _ := iterate_forwardDiff_pow_eq_sum r x 2 2
    _ = _ := by
      norm_num [Finset.sum_range_succ, Nat.choose]
      ring

-- One order above the exponent, the alternating sum cancels for every step.
example (r x : ℝ) (n : ℕ) :
    ∑ j ∈ Finset.range (n + 2), (-1 : ℝ) ^ (n + 1 - j) * (Nat.choose (n + 1) j : ℝ) *
        (x + r * j) ^ n = 0 := by
  rw [← iterate_forwardDiff_pow_eq_sum]
  exact congrFun (iterate_forwardDiff_pow_eq_zero_of_lt r (Nat.lt_succ_self n)) x

end MathlibExt.NumberTheory.FiniteSumsFibLucasWanted
