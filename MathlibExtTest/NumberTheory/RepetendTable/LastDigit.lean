/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.NumberTheory.RepetendTable.LastDigit

/-! # Tests for the last repetend digit -/

open MetaMathlibExt

-- The smallest allowed modulus gives order one for the base 3.
example : 3 ^ (orderOf (3 : ZMod 2) - 1 + 1) / 2 % 3 ≠ 0 :=
  repetend_last_digit_ne_zero 2 3 (by decide) (by decide) (by decide)

-- The base-3 repetend of 1/8 is 01: an initial zero does not force a final zero.
example : 3 ^ (orderOf (3 : ZMod 8) - 1 + 1) / 8 % 3 = 1 := by
  have horder : orderOf (3 : ZMod 8) = 2 := by
    rw [orderOf_eq_iff (by decide : 0 < 2)]
    decide
  rw [horder]
  decide

-- The base-10 repetend of 1/7 ends in 7 even though the base exceeds the modulus.
example : 10 ^ (orderOf (10 : ZMod 7) - 1 + 1) / 7 % 10 = 7 := by
  have horder : orderOf (10 : ZMod 7) = 6 := by
    rw [orderOf_eq_iff (by decide : 0 < 6)]
    decide
  rw [horder]
  decide
