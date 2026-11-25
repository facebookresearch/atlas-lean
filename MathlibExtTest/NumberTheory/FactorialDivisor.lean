/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.NumberTheory.FactorialDivisor

/-!
# Tests for the exponential bound on factorial divisors

The unit divisor gives equality, and the two distinct prime factors of `12 ∣ 4!`
have exponents two and one.
-/

open MetaMathlibExt

example {n : ℕ} (hn : 0 < n) : (1 : ℝ) ≤ Real.exp 0 := by
  simpa only [Nat.primeFactors_one, Finset.sup_empty, Nat.bot_eq_zero, Nat.cast_zero,
    Nat.cast_one, mul_zero, zero_div] using
    le_exp_of_dvd_factorial hn (Nat.zero_lt_one) (one_dvd n.factorial)

example : (12 : ℝ) ≤ Real.exp 12 := by
  have hK : (12 : ℕ).primeFactors.sup (12 : ℕ).factorization = 2 := by decide +kernel
  have h := le_exp_of_dvd_factorial (n := 4) (x := 12) (by decide) (by decide) (by decide)
  norm_num [hK] at h ⊢
  exact h
