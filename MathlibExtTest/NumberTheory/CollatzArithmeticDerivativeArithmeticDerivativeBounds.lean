/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.NumberTheory.CollatzArithmeticDerivativeArithmeticDerivativeBounds

/-!
# Tests for bounds on the arithmetic derivative

These tests apply the bounds to a prime and a prime power and derive strict bounds
for numbers that are not prime powers.
-/

namespace MathlibExtTest.NumberTheory.CollatzArithmeticDerivativeArithmeticDerivativeBounds

open MetaMathlibExt

example : (arithmeticDerivative 2 : ℝ) = 2 * Real.logb 2 2 / 2 := by
  exact (arithmeticDerivative_bounds 2 (by decide)).2.2.2.mpr Nat.prime_two.isPrimePow

example : (arithmeticDerivative 8 : ℝ) = 8 * Real.logb 2 8 / 2 := by
  exact (arithmeticDerivative_bounds 8 (by decide)).2.2.2.mpr (by decide)

example (n : ℕ) (hn : 2 ≤ n) (hpow : ¬ IsPrimePow n) :
    (n.primeFactorsList.length : ℝ) *
        (n : ℝ) ^ (((n.primeFactorsList.length : ℝ) - 1) / n.primeFactorsList.length) <
      arithmeticDerivative n := by
  have h := arithmeticDerivative_bounds n hn
  exact lt_of_le_of_ne h.1 (fun he => hpow (h.2.2.1.mp he))

example (n : ℕ) (hn : 2 ≤ n) (hpow : ¬ IsPrimePow n) :
    (arithmeticDerivative n : ℝ) < (n : ℝ) * Real.logb n.minFac n / n.minFac := by
  have h := arithmeticDerivative_bounds n hn
  exact lt_of_le_of_ne h.2.1 (fun he => hpow (h.2.2.2.mp he))

end MathlibExtTest.NumberTheory.CollatzArithmeticDerivativeArithmeticDerivativeBounds
