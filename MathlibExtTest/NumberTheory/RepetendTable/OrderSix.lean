/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.NumberTheory.RepetendTable.OrderSix

/-! # Tests for small residues excluded by order six -/

open MetaMathlibExt

-- Modulo 7, both 2 and 3 have sixth power one, but only 3 has order six.
example : orderOf (2 : ZMod 7) = 3 := by
  rw [orderOf_eq_iff (by decide : 0 < 3)]
  decide

example : let b : ZMod 7 := 3
    b ≠ 0 ∧ 2 * b ≠ 1 ∧ b ≠ 1 ∧ b ≠ -1 ∧ b ≠ 2 := by
  apply orderOf_eq_six_ne_small_residues 7 1 (by decide) (by decide) (by decide)
  rw [orderOf_eq_iff (by decide : 0 < 6)]
  decide

-- The exclusions also apply to an order-six residue in the non-field case.
example : let b : ZMod 49 := 19
    b ≠ 0 ∧ 2 * b ≠ 1 ∧ b ≠ 1 ∧ b ≠ -1 ∧ b ≠ 2 := by
  apply orderOf_eq_six_ne_small_residues 7 2 (by decide) (by decide) (by decide)
  rw [orderOf_eq_iff (by decide : 0 < 6)]
  decide

-- At the excluded prime 3, the residue 2 itself has order six modulo 9.
example : orderOf (2 : ZMod 9) = 6 := by
  rw [orderOf_eq_iff (by decide : 0 < 6)]
  decide
