/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import MathlibExt.NumberTheory.GibonacciPolynomialPowerSumsCubeEvenIndex

/-!
# Tests for cubic series at even Fibonacci polynomial indices

At `x = 1`, independently compute the first two terms of each series from the polynomial
recurrence and check that their sum is the stated total minus the two uncanceled tail terms
(with only one tail term for shift `1`). The client examples recover the totals in
Corollary 4.4 of Lin and Zhou.
-/

namespace MathlibExtTest.NumberTheory.GibonacciPolynomialPowerSumsCubeEvenIndex

open MetaMathlibExt Polynomial

local notation "F" => fun n : ℕ ↦ aeval (1 : ℝ) (generalizedFibonacciPolynomial 0 1 X 1 n)
local notation "L" => fun n : ℕ ↦ aeval (1 : ℝ) (generalizedFibonacciPolynomial 2 X X 1 n)

-- The plus numerator and the starting center 2 leave only the odd tail at index 5.
example : (4 * F 6 + 3 * F 2) / (F 2 ^ 2 + 1) ^ 3 +
    (4 * F 12 + 3 * F 4) / (F 4 ^ 2 + 1) ^ 3 = 5 * (1 - 1 / F 5 ^ 3) := by
  norm_num [generalizedFibonacciPolynomial_add_two]

-- The minus numerator and the starting center 4 leave the even tail at indices 6 and 8.
example : (8 * L 12 - 3 * L 4) / (F 4 ^ 2 - 1) ^ 3 +
    (8 * L 18 - 3 * L 6) / (F 6 ^ 2 - 1) ^ 3 =
      5 * (1 + 1 / F 4 ^ 3 - 1 / F 6 ^ 3 - 1 / F 8 ^ 3) := by
  norm_num [generalizedFibonacciPolynomial_add_two, map_ofNat]

-- The denominator base vanishes at center 2; the next two bases are nonzero.
example : F 2 ^ 2 - 1 = 0 ∧ F 4 ^ 2 - 1 = 8 ∧ F 6 ^ 2 - 1 = 63 := by
  norm_num [generalizedFibonacciPolynomial_add_two]

-- Independently check positivity for a sequence with unequal seeds and a nonintegral coefficient.
example (n : ℕ) : (2 : ℝ) ^ (n + 2) = (3 / 2) * 2 ^ (n + 1) + 2 ^ n ∧
    0 < (2 : ℝ) ^ n := by
  constructor
  · rw [pow_add, pow_succ (2 : ℝ) n]
    ring
  · exact pow_pos (by norm_num) n

example : ∑' n : ℕ, (4 * F (6 * (n + 1)) + 3 * F (2 * (n + 1))) /
    (F (2 * (n + 1)) ^ 2 + 1) ^ 3 = 5 := by
  have h := (tsum_fibPoly_cube_even_index (by norm_num : 0 < (1 : ℝ))).1
  norm_num at h ⊢
  exact h

example : ∑' n : ℕ, (8 * L (6 * (n + 2)) - 3 * L (2 * (n + 2))) /
    (F (2 * (n + 2)) ^ 2 - 1) ^ 3 = 140 / 27 := by
  have h := (tsum_fibPoly_cube_even_index (by norm_num : 0 < (1 : ℝ))).2
  norm_num at h ⊢
  exact h

end MathlibExtTest.NumberTheory.GibonacciPolynomialPowerSumsCubeEvenIndex
