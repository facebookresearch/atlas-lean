/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.NumberTheory.HeightOneMultipleZetaMulNegNat

open MetaMathlibExt

-- At the smallest admissible weight, only the term with base 1 survives.
example (s : ℂ) (hs : 2 < s.re) :
    ∑' j : ℕ, heightOneMultipleZeta s j * (-1 : ℂ) ^ j = 1 := by
  simpa using (tsum_heightOneMultipleZeta_mul_neg_nat_pow 1 (by decide)).1 s (by norm_num; exact hs)

-- At weight −2 the second term of the finite complex sum has a minus sign.
example (s : ℂ) (hs : 3 < s.re) :
    ∑' j : ℕ, heightOneMultipleZeta s j * (-2 : ℂ) ^ j = 1 - (2 : ℂ) ^ (-s) := by
  have h := (tsum_heightOneMultipleZeta_mul_neg_nat_pow 2 (by decide)).1 s (by norm_num; exact hs)
  simpa [Finset.sum_range_succ, sub_eq_add_neg, one_add_one_eq_two] using h

-- The integer specialization includes the division by r and the exponent k - 1.
example : ∑' j : ℕ, heightOneMultipleZeta 4 j * (-2 : ℂ) ^ j = (15 / 16 : ℂ) := by
  rw [show (4 : ℂ) = ((4 : ℕ) : ℂ) by norm_num, show (-2 : ℂ) = -((2 : ℕ) : ℂ) by norm_num,
    (tsum_heightOneMultipleZeta_mul_neg_nat_pow 2 (by decide)).2 4 (by decide)]
  rw [show Finset.Icc 1 2 = ({1, 2} : Finset ℕ) by decide]
  norm_num [Nat.choose, Finset.sum_insert, Finset.sum_singleton]
