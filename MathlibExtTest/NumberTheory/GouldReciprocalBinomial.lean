/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.NumberTheory.GouldReciprocalBinomial
import Mathlib.Tactic.NormNum

open MathlibExt.NumberTheory.RamanujanHarmonicIdentityWanted

-- The singleton sum uses the empty generalized binomial coefficient.
example (x : ℝ) (hx : x ≠ 0) :
    ∑ ν ∈ Finset.Icc (0 : ℕ) 0,
      ((-1 : ℝ) ^ ν / (x - (ν : ℝ))) * (Nat.choose 0 ν : ℝ) = 1 / x := by
  simpa only [Nat.cast_zero, sub_zero, Ring.choose_zero_right, mul_one, pow_zero] using
    sum_neg_one_pow_div_mul_choose_eq (N := 0) (x := x) (hx := by simpa using hx)

-- The real argument may lie between two excluded integers.
example :
    ∑ ν ∈ Finset.Icc (0 : ℕ) 1,
      ((-1 : ℝ) ^ ν / (1 / 2 - (ν : ℝ))) * (Nat.choose 1 ν : ℝ) = 4 := by
  have h := sum_neg_one_pow_div_mul_choose_eq (N := 1) (x := 1 / 2) (hx := by
    intro ν hν
    have hle := (Finset.mem_Icc.mp hν).2
    have hcases : ν = 0 ∨ ν = 1 := by omega
    rcases hcases with rfl | rfl <;> norm_num)
  rw [h]
  norm_num [Ring.choose_one_right]

-- A negative integer is allowed, even though every descending factor is negative.
example :
    ∑ ν ∈ Finset.Icc (0 : ℕ) 2,
      ((-1 : ℝ) ^ ν / (-1 - (ν : ℝ))) * (Nat.choose 2 ν : ℝ) = -1 / 3 := by
  have h := sum_neg_one_pow_div_mul_choose_eq (N := 2) (x := -1) (hx := by
    intro ν _
    exact ne_of_lt (lt_of_lt_of_le (by norm_num) (Nat.cast_nonneg ν)))
  rw [h]
  norm_num [Ring.choose_neg', Ring.multichoose_one, show Int.negOnePow 2 = 1 by decide]
