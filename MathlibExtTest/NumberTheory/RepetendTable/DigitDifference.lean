/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.NumberTheory.RepetendTable.DigitDifference

/-! # Tests for differences of repetend digits -/

open MetaMathlibExt

-- Modulo 7, the rows indexed by the residues of 3² and 3 have bases 2 and 3.
-- Their digits at position 1 differ by −1.
example : (7 : ℤ) * (((2 ^ 2 / 7 % 2 : ℕ) : ℤ) - (3 ^ 2 / 7 % 3 : ℕ)) = -7 :=
  repetend_digit_sub_eq 7 3 1 2 1 1 (by decide) (by decide)

-- Modulo 1 every residue base is zero, even at exponent zero.
example (b y m d e : ℕ) :
    let r (x j : ℕ) := (b ^ x % 1) ^ (j + 1) / 1 % (b ^ x % 1)
    (r (y * m) e : ℤ) - r y d = 0 := by
  simpa only [Nat.mod_one, Int.natCast_one, Int.natCast_zero, Int.one_mul, Int.zero_mul,
    Int.sub_zero, Int.add_zero] using repetend_digit_sub_eq 1 b y m d e (by decide) (by simp)
