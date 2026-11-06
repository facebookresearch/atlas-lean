/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.NumberTheory.ArithmeticFunction.SigmaZeroSqDivTotient

/-!
# Tests for `∑ d(n²) / φ(n)`
-/

@[expose] public section

open Finset ArithmeticFunction

-- Boundary `u = 1`: `|1 - 0| ≤ 2`.
example : |∑ n ∈ Icc 1 ⌊(1 : ℝ)⌋₊, (n.divisors.card : ℝ) / n - 1 / 2 * Real.log 1 ^ 2| ≤
    2 * (1 + Real.log 1) :=
  abs_sum_divisors_div_sub_le le_rfl

example : |∑ n ∈ Icc 1 ⌊(1 : ℝ)⌋₊, (n.divisors.card : ℝ) / n - 1 / 2 * Real.log 1 ^ 2| = 1 := by
  simp

-- `d(n²) / φ(n)` at small `n`: `d(4) / φ(2) = 3`, `d(36) / φ(6) = 9 / 2`.
example : (sigma 0 (2 ^ 2) : ℝ) / (Nat.totient 2 : ℝ) = 3 := by
  rw [show sigma 0 (2 ^ 2) = 3 by decide, show Nat.totient 2 = 1 by decide]; norm_num
example : (sigma 0 (6 ^ 2) : ℝ) / (Nat.totient 6 : ℝ) = 9 / 2 := by
  rw [show sigma 0 (6 ^ 2) = 9 by decide, show Nat.totient 6 = 2 by decide]; norm_num

example : ∃ c : ℝ, 0 < c ∧ ∃ C : ℝ, ∀ x : ℝ, 2 ≤ x →
    |∑ n ∈ Icc 1 ⌊x⌋₊, (sigma 0 (n ^ 2) : ℝ) / (Nat.totient n : ℝ) - c * Real.log x ^ 3| ≤
      C * Real.log x ^ 2 :=
  exists_abs_sum_sigma_zero_sq_div_totient_sub_le
