/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.NumberTheory.RepetendTable.HalfPeriod
import Mathlib.FieldTheory.Finite.Basic

/-! # Tests for half-period symmetry of repetends -/

open MetaMathlibExt

-- In base 3, the six digits of 1/7 are 010212. The paired remainders at positions 1 and 4
-- are 3 and 4, and the two nonzero digits sum to the digit 2 at the half-period.
example : 3 ^ (1 + 6 / 2) % 7 = 7 - 3 ^ 1 % 7 ∧
    3 ^ (1 + 1) / 7 % 3 + 3 ^ (1 + 6 / 2 + 1) / 7 % 3 = 3 ^ (6 / 2 + 1) / 7 % 3 := by
  have horder : orderOf ((3 : ℕ) : ZMod 7) = 6 := by
    rw [orderOf_eq_iff (by decide : 0 < 6)]
    refine ⟨by decide, ?_⟩
    intro m hm hm₀
    interval_cases m <;> decide
  have : Fact (Nat.Prime 7) := ⟨by decide⟩
  exact pow_add_half_mod_eq_and_digit_add (n := 7) (L := 6) (b := 3) (j := 1)
    (hL := ⟨3, rfl⟩) (hL0 := by decide) (hbn := by decide) (hb := horder)
