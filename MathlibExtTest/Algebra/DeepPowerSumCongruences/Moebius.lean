/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Algebra.DeepPowerSumCongruences.Moebius

/-! # Tests for Möbius sums over divisors prime to a given prime -/

open MetaMathlibExt

-- Every prime power gives 1, including the zeroth power.
example {p : ℕ} (hp : p.Prime) (k : ℕ) :
    ∑ d ∈ (p ^ k).divisors with ¬ p ∣ d, ArithmeticFunction.moebius d = 1 := by
  rw [sum_moebius_divisors_not_dvd_prime hp (pow_ne_zero k hp.ne_zero), Nat.log_pow hp.one_lt,
    ite_eq_left rfl]

-- Removing the factors of 2 from 12 leaves the divisors 1 and 3, whose values cancel.
example : ∑ d ∈ (12 : ℕ).divisors with ¬ 2 ∣ d, ArithmeticFunction.moebius d = 0 := by
  rw [sum_moebius_divisors_not_dvd_prime Nat.prime_two (by decide)]
  decide
