/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.NumberTheory.RepetendTable.PrimePowerValuation

/-! # Tests for the prime-power valuation of a repetend base -/

open MetaMathlibExt

-- Booth–Horton, Example 11: base 3 has order 42 modulo 49, and `3 ^ 2 - 3 + 1 = 7`.
example : padicValNat 7 (3 ^ 2 - 3 + 1) = 1 := by
  have horder : orderOf ((3 : ℕ) : ZMod (7 ^ 2)) = 6 * 7 ^ 1 := by
    rw [orderOf_eq_iff (by decide : 0 < 6 * 7 ^ 1)]
    decide
  exact padicValNat_sq_sub_add_one_of_orderOf_eq 7 2 1 3
    (by decide) (by decide) (by decide) (by decide) horder
