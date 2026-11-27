/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.NumberTheory.Recurrences.FibonacciSumDivisibilityPrimeIndices

/-!
# Tests for Fibonacci sum divisibility at prime-based indices

Only the hypotheses are decided computationally; the conclusions use the theorem.
-/

open MathlibExt.NumberTheory.Recurrences.FibonacciSumDivisibilityWanted

example : Nat.fib 34 % 2 = 1 ∧ Nat.fib (Nat.fib 34 + 2) % Nat.fib 34 = 1 :=
  fib_two_mul_prime_odd_and_fib_fib_add_two_mod 17 34 (by decide) (by decide)
    (by decide) (Or.inl (by decide)) (Or.inl rfl)

example : Nat.fib 68 % 2 = 1 ∧ Nat.fib (Nat.fib 68 + 2) % Nat.fib 68 = 1 :=
  fib_two_mul_prime_odd_and_fib_fib_add_two_mod 17 68 (by decide) (by decide)
    (by decide) (Or.inl (by decide)) (Or.inr rfl)

example : Nat.fib 46 % 2 = 1 ∧ Nat.fib (Nat.fib 46 + 2) % Nat.fib 46 = 1 :=
  fib_two_mul_prime_odd_and_fib_fib_add_two_mod 23 46 (by decide) (by decide)
    (by decide) (Or.inr (by decide)) (Or.inl rfl)

example : Nat.fib 92 % 2 = 1 ∧ Nat.fib (Nat.fib 92 + 2) % Nat.fib 92 = 1 :=
  fib_two_mul_prime_odd_and_fib_fib_add_two_mod 23 92 (by decide) (by decide)
    (by decide) (Or.inr (by decide)) (Or.inr rfl)
