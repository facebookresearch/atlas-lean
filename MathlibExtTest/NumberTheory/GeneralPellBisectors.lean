/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.NumberTheory.GeneralPellBisectors

namespace MetaMathlibExt

/-- `d = 5`, `z = 2`: `x² - 5 y² = ±2` has no integral solution. -/
example (x y : ℤ) : |x ^ 2 - 5 * y ^ 2| ≠ 2 :=
  abs_sq_sub_mul_sq_ne_of_two_mod_four 5 2 rfl rfl x y

#print axioms abs_sq_sub_mul_sq_ne_of_two_mod_four

end MetaMathlibExt
