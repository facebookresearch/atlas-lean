/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.NumberTheory.Recurrences.FibonacciSumDivisibilitySumFibModPrimeEqAndNotDvd

/-! # Tests for the sum of the first `p` Fibonacci numbers modulo a prime `p` -/

namespace MathlibExtTest.NumberTheory.Recurrences.FibonacciSumDivisibilitySumFibModPrimeEqAndNotDvd

example : (∑ i ∈ Finset.Icc 1 7, Nat.fib i) % 7 = 5 := by
  have h :=
    (MathlibExt.NumberTheory.Recurrences.FibonacciSumDivisibilityWanted.sum_fib_mod_prime_eq_and_not_dvd
      7 (by decide) (by decide)).2.1 (Or.inl rfl)
  exact h

example : ¬ 7 ∣ (∑ i ∈ Finset.Icc 1 7, Nat.fib i) :=
  (MathlibExt.NumberTheory.Recurrences.FibonacciSumDivisibilityWanted.sum_fib_mod_prime_eq_and_not_dvd
    7 (by decide) (by decide)).2.2

example : (∑ i ∈ Finset.Icc 1 11, Nat.fib i) % 11 = 1 := by
  have h :=
    (MathlibExt.NumberTheory.Recurrences.FibonacciSumDivisibilityWanted.sum_fib_mod_prime_eq_and_not_dvd
      11 (by decide) (by decide)).1 (Or.inl rfl)
  exact h

example : ¬ 11 ∣ (∑ i ∈ Finset.Icc 1 11, Nat.fib i) :=
  (MathlibExt.NumberTheory.Recurrences.FibonacciSumDivisibilityWanted.sum_fib_mod_prime_eq_and_not_dvd
    11 (by decide) (by decide)).2.2

end MathlibExtTest.NumberTheory.Recurrences.FibonacciSumDivisibilitySumFibModPrimeEqAndNotDvd
