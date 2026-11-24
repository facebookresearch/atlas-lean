/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.NumberTheory.TwoPowAddFifteenPow

/-! # Tests for the natural solutions of `2^x + 15^y = z^2` -/

open MathlibExt.NumberTheory.PowAddPowEqSqWanted

example (y z : ℕ) : 1 + 15 ^ y = z ^ 2 ↔ y = 1 ∧ z = 4 := by
  simpa using two_pow_add_fifteen_pow 0 y z

example (x z : ℕ) : 2 ^ x + 1 = z ^ 2 ↔ x = 3 ∧ z = 3 := by
  simpa using two_pow_add_fifteen_pow x 0 z

example {x y z : ℕ} (hx : 0 < x) (hy : 0 < y) :
    2 ^ x + 15 ^ y = z ^ 2 ↔ x = 6 ∧ y = 2 ∧ z = 17 := by
  simpa [Nat.ne_of_gt hx, Nat.ne_of_gt hy] using two_pow_add_fifteen_pow x y z
