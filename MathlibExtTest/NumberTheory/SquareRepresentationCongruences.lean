/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.NumberTheory.SquareRepresentationCongruences

/-!
# Tests for prime congruences of square representation counts
-/

open MetaMathlibExt

-- The smallest prime is allowed, and the shift can take the exponent below zero.
example : (2 : ℤ) ∣ sumOfSquaresRepCount (-1) 1 := by
  have h : (2 : ℤ) ∣ sumOfSquaresRepCount 1 1 := by
    simp only [sumOfSquaresRepCount_one, coeff_squareThetaSeries_small.2.1, dvd_refl]
  exact sumOfSquaresRepCount_add_mul_prime (n := 1) (k := 1) (p := 2)
    (hn := by decide) (hk := by decide) (by decide) (by decide) h (-1)

-- At the boundary p = n + 1, a positive shift takes one square to four squares.
example : (3 : ℤ) ∣ sumOfSquaresRepCount 4 2 := by
  have h : (3 : ℤ) ∣ sumOfSquaresRepCount 1 2 := by
    simp only [sumOfSquaresRepCount_one, coeff_squareThetaSeries_small.2.2.1, dvd_zero]
  exact sumOfSquaresRepCount_add_mul_prime (n := 2) (k := 1) (p := 3)
    (hn := by decide) (hk := by decide) (by decide) (by decide) h 1
