/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.NumberTheory.ArithmeticFunction.HBCHalfPrimeProductBounds
import Mathlib.Tactic.NormNum

/-! # Tests for the product bounds for prime tuples at $1/2$ -/

open MetaMathlibExt Finset

namespace HBCHalfPrimeProductBoundsTest

/-- The primes from `5` to `23`, indexed from `1`. -/
private def primesFrom5 (i : ℕ) : ℕ := ([0, 5, 7, 11, 13, 17, 19, 23] : List ℕ).getD i 0

-- The primes from 5 to 23 take the product of `1 - 1/p` below 1/2 exactly at 23,
-- so the first bound applies to their product.
example : ∏ i ∈ Icc 1 7, (primesFrom5 i : ℝ) ≤
    Real.sqrt (8 / (3 : ℝ) ^ ((7 : ℝ) / 8)) ^ 2 ^ 7 -
      Real.sqrt (8 / (3 : ℝ) ^ ((7 : ℝ) / 8)) ^ 2 ^ (7 - 1) :=
  (hbcAdmissible_half_prime_prod_le_of_five_le 7 primesFrom5 (by decide) (by decide +kernel)
    (by rw [show Icc 1 7 = {1, 2, 3, 4, 5, 6, 7} by decide]; norm_num [primesFrom5])
    (by rw [show Icc 1 (7 - 1) = {1, 2, 3, 4, 5, 6} by decide]; norm_num [primesFrom5])
    (by decide)).1

/-- The primes from `7` to `61`, indexed from `1`. -/
private def primesFrom7 (i : ℕ) : ℕ :=
  ([0, 7, 11, 13, 17, 19, 23, 29, 31, 37, 41, 43, 47, 53, 59, 61] : List ℕ).getD i 0

-- The primes from 7 to 61 cross 1/2 at 61; a first prime in [6, 18) gives the second bound.
example : ∏ i ∈ Icc 1 15, (primesFrom7 i : ℝ) ≤
    Real.sqrt (12 / (5 : ℝ) ^ ((15 : ℝ) / 16)) ^ 2 ^ 15 -
      Real.sqrt (12 / (5 : ℝ) ^ ((15 : ℝ) / 16)) ^ 2 ^ (15 - 1) :=
  (hbcAdmissible_half_prime_prod_le_of_five_le 15 primesFrom7 (by decide) (by decide +kernel)
    (by
      rw [show Icc 1 15 = {1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15} by decide]
      norm_num [primesFrom7])
    (by
      rw [show Icc 1 (15 - 1) = {1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14} by decide]
      norm_num [primesFrom7])
    (by decide)).2.1 (by decide) (by decide)

end HBCHalfPrimeProductBoundsTest
