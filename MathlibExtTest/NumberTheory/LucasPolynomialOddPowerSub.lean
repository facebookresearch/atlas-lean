/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import Mathlib.Data.Nat.Choose.Sum
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import MathlibExt.NumberTheory.LucasPolynomialOddPowerSub

/-!
# Tests for odd powers of Lucas polynomials

Compute both cubic identities directly from the polynomial recurrences. The two cases exercise
negative second summands in the odd- and even-shift formulas, respectively. A zero-shift example
checks the extra boundary case. The client example uses the public theorem at `m = 0` and
`n = k = 2`.
-/

namespace MathlibExtTest.NumberTheory.LucasPolynomialOddPowerSub

open MetaMathlibExt Polynomial

local notation "𝔣" => generalizedFibonacciPolynomial 0 1 X 1
local notation "𝔩" => generalizedFibonacciPolynomial 2 X X 1

-- Odd shift: n = 2, k = 1, m = 1.
example : 𝔩 3 ^ 3 - 𝔩 1 ^ 3 =
    ∑ j ∈ Finset.range 2, ((3 : ℕ).choose j : ℤ[X]) * (-1) ^ (3 * j) *
      𝔩 (2 * (3 - 2 * j)) * 𝔩 (1 * (3 - 2 * j)) := by
  norm_num [Finset.sum_range_succ, generalizedFibonacciPolynomial_add_two]
  ring

-- Even shift: n = 3, k = 2, m = 1.
example : 𝔩 5 ^ 3 - 𝔩 1 ^ 3 = (X ^ 2 + 4) *
    ∑ j ∈ Finset.range 2, ((3 : ℕ).choose j : ℤ[X]) * (-1) ^ (3 * j) *
      𝔣 (3 * (3 - 2 * j)) * 𝔣 (2 * (3 - 2 * j)) := by
  norm_num [Finset.sum_range_succ, generalizedFibonacciPolynomial_add_two]
  ring

-- Zero shift: n = 1, k = 0, m = 1. Every term contains f₀.
example : 𝔩 1 ^ 3 - 𝔩 1 ^ 3 = (X ^ 2 + 4) *
    ∑ j ∈ Finset.range 2, ((3 : ℕ).choose j : ℤ[X]) * (-1) ^ j *
      𝔣 (3 - 2 * j) * 𝔣 (0 * (3 - 2 * j)) := by
  simp

-- At n = k the lower Lucas index is zero; m = 0 gives a one-term sum.
example : 𝔩 4 - 𝔩 0 = (X ^ 2 + 4) * 𝔣 2 ^ 2 := by
  simpa only [Nat.reduceAdd, Nat.reduceSub, Nat.reduceMul, pow_one, Finset.sum_range_one,
    Nat.choose_zero_right, Nat.cast_one, Nat.mul_zero, pow_zero, one_mul, pow_two] using
    (lucasPoly_pow_odd_sub (n := 2) (k := 2) (by decide) 0).2 (by decide)

end MathlibExtTest.NumberTheory.LucasPolynomialOddPowerSub
