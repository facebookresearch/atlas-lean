/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.NumberTheory.Digits.DigitsPowAndPowAddOne

/-! # Tests for the digits of powers and their successors -/

open MetaMathlibExt

example (z : ℕ) (hz : 2 ≤ z) : Nat.digits z 1 = [1] :=
  (digits_pow_and_pow_add_one z 0 hz).1

example : Nat.digits 2 3 = [1, 1] :=
  (digits_pow_and_pow_add_one 2 1 (by decide)).2 (by decide)

example : Nat.digits 10 1000 = [0, 0, 0, 1] :=
  (digits_pow_and_pow_add_one 10 3 (by decide)).1

example : Nat.digits 10 1001 = [1, 0, 0, 1] :=
  (digits_pow_and_pow_add_one 10 3 (by decide)).2 (by decide)
