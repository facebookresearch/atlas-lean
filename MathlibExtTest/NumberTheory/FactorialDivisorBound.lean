/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.NumberTheory.FactorialDivisorBound
import Mathlib.Tactic.Simproc.Factors

open MetaMathlibExt

-- The unit divisor has no prime factors, so the natural power contributes one.
example {n a : ℕ} (hn : 0 < n) (ha : 0 < a) : 1 ≤ (n : ℝ) ^ ((n : ℝ) / a) := by
  simpa using le_rpow_mul_pow_of_dvd_factorial hn Nat.zero_lt_one (one_dvd _) ha

-- The divisor 12 of 4! has two distinct prime factors, although 2 occurs twice.
example : (12 : ℝ) ≤ (4 : ℝ) ^ ((4 : ℝ) / 3) * 7 ^ (8 : ℕ) := by
  have hcard : (12 : ℕ).primeFactors.card = 2 := by norm_num [Nat.primeFactors]
  simpa [hcard] using le_rpow_mul_pow_of_dvd_factorial
    (n := 4) (x := 12) (a := 3) (by decide) (by decide) (by decide) (by decide)
