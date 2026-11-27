/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.NumberTheory.Digits.NineDvdExponent

/-! # Tests for divisibility of the exponent by nine -/

-- At the first admissible solution, 2 ^ 9 + 1 = 27 * 19.
example : 9 ∣ 9 :=
  MetaMathlibExt.nine_dvd_of_three_mul_dvd_two_pow_add_one 9 (by decide) (by decide)

-- At the excluded endpoint the divisibility hypothesis holds and the conclusion fails.
example : 3 * 3 ∣ 2 ^ 3 + 1 ∧ ¬ 9 ∣ 3 := by decide
