/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.NormNum
import MathlibExt.NumberTheory.FibonacciPolynomialOddPowerSub

open MetaMathlibExt Polynomial

local notation "𝔣" => generalizedFibonacciPolynomial 0 1 X 1
local notation "𝔩" => generalizedFibonacciPolynomial 2 X X 1

-- With an odd shift, the j = 1 term of the cubic expansion is negative when n is odd.
example : (X ^ 2 + 4) * (𝔣 4 ^ 3 - 𝔣 2 ^ 3) = 𝔣 9 * 𝔩 3 - 3 * 𝔣 3 * 𝔩 1 := by
  have h := (fibPoly_pow_odd_sub (n := 3) (k := 1) (by decide) 1).1 (by decide)
  norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.choose] at h
  linear_combination h

-- With an even shift, the j = 1 term is negative when n is even; here the lower index is zero.
example : (X ^ 2 + 4) * (𝔣 4 ^ 3 - 𝔣 0 ^ 3) = 𝔩 6 * 𝔣 6 - 3 * 𝔩 2 * 𝔣 2 := by
  have h := (fibPoly_pow_odd_sub (n := 2) (k := 2) (by decide) 1).2 (by decide)
  norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.choose] at h
  linear_combination h

-- At m = 0 the expansion has just one term and no discriminant factor.
example {n k : ℕ} (hk : k ≤ n) (ho : Odd k) : 𝔣 (n + k) - 𝔣 (n - k) = 𝔣 n * 𝔩 k := by
  simpa only [Nat.mul_zero, Nat.zero_add, pow_zero, pow_one, one_mul, Finset.sum_range_one,
    Nat.choose_zero_right, Nat.cast_one, Nat.sub_zero, Nat.mul_one] using
    (fibPoly_pow_odd_sub hk 0).1 ho

-- The even-shift formula includes the zero shift for every odd power.
example (n m : ℕ) :
    (X ^ 2 + 4) ^ m * (𝔣 n ^ (2 * m + 1) - 𝔣 n ^ (2 * m + 1)) = 0 := by
  simpa only [Nat.add_zero, Nat.sub_zero, Nat.zero_mul, generalizedFibonacciPolynomial_zero,
    mul_zero, Finset.sum_const_zero] using
    (fibPoly_pow_odd_sub (n := n) (k := 0) (Nat.zero_le n) m).2 (by decide)
