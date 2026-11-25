/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.NumberTheory.Digits.NegTwoCubeDvd

open MetaMathlibExt

-- With a negative divisor parameter, the extra factor of three is still obtained.
example : (27 : ℤ) ∣ 1 - (-2) ^ (3 * 3 : ℕ) := by
  have h := three_mul_dvd_one_sub_neg_two_pow_cube (-3) 3 (by decide)
  exact Int.neg_dvd.mp h

-- At exponent zero the theorem includes the zero divisor parameter.
example : (0 : ℤ) ∣ 1 - (-2) ^ (3 * 0 : ℕ) :=
  three_mul_dvd_one_sub_neg_two_pow_cube 0 0 (by decide)
