/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.NumberTheory.Digits.BinomialDigits

/-! # Tests for scaled binomial coefficients as digits -/

open MetaMathlibExt

-- The single-digit case needs no positive-exponent hypothesis.
example : Nat.digits 3 (2 * (1 + 3) ^ 0) = [2] :=
  digits_mul_one_add_pow 2 0 3 (by decide) (by decide)

-- Both central coefficients reach the largest allowed digit in base 7.
example : Nat.digits 7 (2 * (1 + 7) ^ 3) = [2, 6, 6, 2] :=
  digits_mul_one_add_pow 2 3 7 (by decide) (by decide)
