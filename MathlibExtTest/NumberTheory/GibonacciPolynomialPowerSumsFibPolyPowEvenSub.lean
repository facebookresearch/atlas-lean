/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.NumberTheory.GibonacciPolynomialPowerSumsFibPolyPowEvenSub
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

/-!
# Tests for even powers of Fibonacci polynomials

These examples apply the finite power-sum identity at its boundary cases and at
indices giving each sign in the second summand.

Source: Yinqi Lin and Bo Zhou, *Infinite Sums Involving Powers of Gibonacci Polynomials*,
The Fibonacci Quarterly 62 (2024), no. 2, 147–156, Lemma 3.1.
-/

namespace MathlibExtTest.NumberTheory.GibonacciPolynomialPowerSumsFibPolyPowEvenSub

open MetaMathlibExt Polynomial

local notation "𝔣" => generalizedFibonacciPolynomial 0 1 X 1

example : (X ^ 2 + 4) ^ (0 - 1) * (𝔣 4 ^ (2 * 0) - 𝔣 2 ^ (2 * 0)) = 0 := by
  exact (fibPoly_pow_even_sub (n := 3) (k := 1) (by decide) 0).trans (by simp)

example (n m : ℕ) :
    (X ^ 2 + 4) ^ (m - 1) * (𝔣 n ^ (2 * m) - 𝔣 n ^ (2 * m)) = 0 := by
  have h := fibPoly_pow_even_sub (n := n) (k := 0) (Nat.zero_le n) m
  simpa only [Nat.add_zero, Nat.sub_zero] using h.trans (by simp)

example {n k : ℕ} (hk : k ≤ n) :
    𝔣 (n + k) ^ 2 - 𝔣 (n - k) ^ 2 = 𝔣 (2 * k) * 𝔣 (2 * n) := by
  simpa using fibPoly_pow_even_sub hk 1

example : (X ^ 2 + 4) * 𝔣 2 ^ 4 = 𝔣 4 ^ 2 - 4 * 𝔣 2 ^ 2 := by
  have h := fibPoly_pow_even_sub (n := 1) (k := 1) (by decide) 2
  convert h using 1 <;> norm_num [Finset.sum_range_succ, generalizedFibonacciPolynomial]
  ring

example : (X ^ 2 + 4) * (𝔣 3 ^ 4 - 1) = 𝔣 4 * 𝔣 8 + 4 * 𝔣 2 * 𝔣 4 := by
  have h := fibPoly_pow_even_sub (n := 2) (k := 1) (by decide) 2
  convert h using 1 <;> norm_num [Finset.sum_range_succ, generalizedFibonacciPolynomial]

end MathlibExtTest.NumberTheory.GibonacciPolynomialPowerSumsFibPolyPowEvenSub
