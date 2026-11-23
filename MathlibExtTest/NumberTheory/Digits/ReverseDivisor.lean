/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.NumberTheory.Digits.ReverseDivisor

open MathlibExt.NumberTheory.Digits.ReverseDivisorWanted

-- Both possibilities at the upper endpoint occur.
example : IsReverseDivisor 1099989 := ⟨by decide, 9, by decide, by decide⟩

example : IsReverseDivisor 2199978 := ⟨by decide, 4, by decide, by decide⟩

example {n : ℕ} (h : IsReverseDivisor n) (hl : (Nat.digits 10 n).length = 7) :
    n = 1099989 ∨ n = 2199978 := by
  simpa [hl] using eq_basic_of_length_le_seven n h hl.le

-- Concatenating two copies of 1089 gives an eight-digit exception to the formulas.
example : IsReverseDivisor 10891089 ∧ (Nat.digits 10 10891089).length = 8 ∧
    10891089 ≠ 11 * (10 ^ (8 - 2) - 1) ∧ 10891089 ≠ 22 * (10 ^ (8 - 2) - 1) :=
  ⟨⟨by decide, 9, by decide, by decide⟩, by decide, by decide, by decide⟩

example : HasPropertyPStar 1 := fun _ _ => one_dvd _
