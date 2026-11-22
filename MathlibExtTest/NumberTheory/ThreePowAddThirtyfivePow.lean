/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.NumberTheory.ThreePowAddThirtyfivePow

/-! # Tests for the solutions of `3^x + 35^y = z^2` -/

open MathlibExt.NumberTheory.PowAddPowEqSqWanted

example (x z : ℕ) : 3 ^ x + 1 = z ^ 2 ↔ x = 1 ∧ z = 2 := by
  simpa using three_pow_add_thirtyfive_pow x 0 z

example (y z : ℕ) : 1 + 35 ^ y = z ^ 2 ↔ y = 1 ∧ z = 6 := by
  simpa using three_pow_add_thirtyfive_pow 0 y z

example {x y z : ℕ} (hx : 0 < x) (hy : 0 < y) : 3 ^ x + 35 ^ y ≠ z ^ 2 := by
  intro h
  rcases (three_pow_add_thirtyfive_pow x y z).mp h with h | h <;> omega
