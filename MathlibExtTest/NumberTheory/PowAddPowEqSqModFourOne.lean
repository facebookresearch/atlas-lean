/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.NumberTheory.PowAddPowEqSqModFourOne

/-! # Tests for `n^x + (5p)^y = z^2` with `n ≡ p ≡ 1 (mod 4)` -/

namespace MathlibExt.NumberTheory.PowAddPowEqSqWanted

/-- Both exponents zero: `n^0 + (5p)^0 = 2` is not a square. -/
example (z : ℕ) : 2 ≠ z ^ 2 := fun h =>
  no_solution_mod_four_one 1 5 (by decide) rfl rfl ⟨0, 0, z, h⟩

/-- `n = 1`, `p = 5`: `1 + 25^y` is never a square. -/
example (y z : ℕ) : 1 + 25 ^ y ≠ z ^ 2 := fun h =>
  no_solution_mod_four_one 1 5 (by decide) rfl rfl ⟨0, y, z, h⟩

/-- `n = 9`, `p = 13`: `9^x + 65^y` is never a square, although `9 = 3^2` is one. -/
example (x y z : ℕ) : 9 ^ x + 65 ^ y ≠ z ^ 2 := fun h =>
  no_solution_mod_four_one 9 13 (by decide) rfl rfl ⟨x, y, z, h⟩

/-- The condition `n ≡ 1 (mod 4)` is needed: with `n = 3` and `p = 5`, `3^1 + 25^0 = 2^2`. -/
example : ∃ x y z : ℕ, 3 ^ x + (5 * 5) ^ y = z ^ 2 := ⟨1, 0, 2, rfl⟩

/-- The condition `p ≡ 1 (mod 4)` is needed: with `n = 1` and `p = 3`, `1^0 + 15^1 = 4^2`. -/
example : ∃ x y z : ℕ, 1 ^ x + (5 * 3) ^ y = z ^ 2 := ⟨0, 1, 4, rfl⟩

-- A nonprime parameter is allowed, even at the minimum positive modulus exponent.
example (x y z : ℕ) : 5 ^ x + 17 ^ y ≠ z ^ 2 :=
  five_pow_add_four_pow_mul_add_one_ne_sq 4 1 1 x y z (by decide)

-- The parameters and both outer exponents can be zero.
example (z : ℕ) : 2 ≠ z ^ 2 :=
  five_pow_add_four_pow_mul_add_one_ne_sq 0 1 0 0 0 z (by decide)

-- Without the positive modulus exponent, the obstruction fails.
example : (5 ^ 1 : ℕ) ^ 1 + (4 ^ 0 * 3 + 1) ^ 1 = 3 ^ 2 := by
  decide +kernel

end MathlibExt.NumberTheory.PowAddPowEqSqWanted
