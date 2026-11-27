/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.NumberTheory.OresmePellCongruence

/-! # Tests for the Oresme–Pell congruence -/

open MetaMathlibExt

example : 2 ^ (0 : ℕ) * (5 * (pellNumber 1 : ℤ) - 4 * pellNumber 0) ≡ 5 [ZMOD 49] :=
  two_pow_mul_pellNumber_combination_modEq (n := 0)

example : 2 ^ (1 : ℕ) * (5 * (pellNumber 2 : ℤ) - 4 * pellNumber 1) ≡ 12 [ZMOD 49] :=
  two_pow_mul_pellNumber_combination_modEq (n := 1)

example : 2 ^ (2 : ℕ) * (5 * (pellNumber 3 : ℤ) - 4 * pellNumber 2) ≡ 19 [ZMOD 49] :=
  two_pow_mul_pellNumber_combination_modEq (n := 2)

-- At index eight the linear target is 61, whose least nonnegative residue is 12.
example : 2 ^ (8 : ℕ) * (5 * (pellNumber 9 : ℤ) - 4 * pellNumber 8) ≡ 12 [ZMOD 49] :=
  (two_pow_mul_pellNumber_combination_modEq (n := 8)).trans (by decide)
