/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.NumberTheory.Digits.ThreeDigitPalindromeTwoPow

open MetaMathlibExt

-- 16 has digits [1, 2, 1] in base three.
example : (Nat.digits 3 (2 ^ 4)).Palindrome ∧ (Nat.digits 3 (2 ^ 4)).length = 3 :=
  (three_digit_palindrome_two_pow_iff 4 3 (by decide)).mpr (by decide +kernel)

-- In base four, 16 is at the excluded lower boundary and its first digit is zero.
example : ¬ ((Nat.digits 4 (2 ^ 4)).Palindrome ∧ (Nat.digits 4 (2 ^ 4)).length = 3) := by
  rw [three_digit_palindrome_two_pow_iff 4 4 (by decide)]
  decide
