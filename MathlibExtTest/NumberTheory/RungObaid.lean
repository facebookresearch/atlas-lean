/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.NumberTheory.RungObaid
import Mathlib.Tactic.NormNum

open MathlibExt.NumberTheory.RamanujanHarmonicIdentityWanted

-- On the diagonal the multiple angle on the right is zero.
example (n : ℕ) (hn : 1 ≤ n) (θ : ℝ) :
    ∑ i ∈ Finset.Icc 1 n,
        (2 : ℝ) ^ i *
          ((Nat.choose (n + n - i - 1) (n - 1) : ℝ) - (Nat.choose (n + n - i - 1) (n - 1) : ℝ)) *
          Real.cos θ ^ i * Real.sin ((i : ℝ) * θ) = 0 := by
  simpa only [sub_self (n : ℝ), zero_mul, Real.sin_zero, mul_zero] using
    sum_two_pow_choose_sub_mul_cos_pow_sin n n hn le_rfl θ

-- For k = 1 and n = 3 the term at i = 1 cancels and the two upper terms survive.
example (θ : ℝ) :
    4 * Real.cos θ ^ 2 * Real.sin (2 * θ) + 8 * Real.cos θ ^ 3 * Real.sin (3 * θ) =
      16 * Real.cos θ ^ 4 * Real.sin (2 * θ) := by
  have h := sum_two_pow_choose_sub_mul_cos_pow_sin 1 3 (by decide) (by decide) θ
  norm_num [Finset.sum_Icc_succ_top, Nat.choose] at h
  exact h
