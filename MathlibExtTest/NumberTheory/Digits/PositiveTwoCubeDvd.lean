/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.NumberTheory.Digits.PositiveTwoCubeDvd

namespace MetaMathlibExt

example : 9 ∣ (2 : ℕ) ^ 3 + 1 :=
  three_mul_dvd_two_pow_add_one_cube (n := 1) (h := by decide)

example : 27 ∣ (2 : ℕ) ^ 9 + 1 :=
  three_mul_dvd_two_pow_add_one_cube (n := 3) (h := by decide)

example : ¬ 3 * 0 ∣ (2 : ℕ) ^ 0 + 1 := by decide

end MetaMathlibExt
