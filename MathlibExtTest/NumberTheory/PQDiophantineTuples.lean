/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.NumberTheory.PQDiophantineTuples

namespace MetaMathlibExt

/-- `(a, b, c) = (1, 3, 8)`: `9` does not divide `25`. -/
example : ¬(1 * 8 + 1 ∣ 3 * 8 + 1) :=
  not_mul_add_one_dvd_mul_add_one (by decide) (by decide) (by decide)

#print axioms not_mul_add_one_dvd_mul_add_one

/-- The descending tuple gives negative differences. For the entry `4`, the difference
`9 - 21` reduces by a gcd of `3`. For the entry `0`, all three differences vanish. -/
example : (5 : ℤ) ∣ 10 ∧ (4 : ℤ) ∣ 4 ∧ (2 : ℤ) ∣ 2 ∧ (0 : ℤ) ∣ 0 :=
  dvd_gcd_sub_div_gcd 5 4 2 0

#print axioms dvd_gcd_sub_div_gcd

end MetaMathlibExt
