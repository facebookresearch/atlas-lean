/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.NumberTheory.Digits.ThreeDigitBinomialForm

/-! # Tests for three-digit binomial forms of powers of two -/

open MetaMathlibExt

-- The first example with outer digit greater than one is 128 in base seven.
example : Nat.digits 7 (2 ^ 7) = [2, 4, 2] :=
  (three_digit_binomialForm_two_pow_iff 7 7 2 (by decide) (by decide)).2
    ⟨1, by decide, by decide, rfl, rfl⟩

-- At n = 3i + 2 with i = 1, the proposed middle digit overflows base three.
example : Nat.digits 3 (2 ^ 5) ≠ [2, 4, 2] := by
  intro h
  obtain ⟨i, hbound, hparity, _, _⟩ :=
    (three_digit_binomialForm_two_pow_iff 5 3 2 (by decide) (by decide)).1 h
  omega

-- With the wrong parity the same base and digits no longer represent the power.
example : Nat.digits 7 (2 ^ 8) ≠ [2, 4, 2] := by
  intro h
  obtain ⟨i, _, hparity, hi, _⟩ :=
    (three_digit_binomialForm_two_pow_iff 8 7 2 (by decide) (by decide)).1 h
  have : 1 = i := Nat.pow_right_injective (by decide : 2 ≤ 2) hi
  omega
