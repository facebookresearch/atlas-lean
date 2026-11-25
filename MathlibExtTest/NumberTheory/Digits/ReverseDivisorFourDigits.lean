/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.NumberTheory.Digits.ReverseDivisorFourDigits

open MathlibExt.NumberTheory.Digits.ReverseDivisorWanted

-- The bound is attained with both quotients: `1089` (quotient 9) and `2178` (quotient 4).
example : IsReverseDivisor 1089 ∧ (Nat.digits 10 1089).length = 4 :=
  ⟨⟨by decide, 9, by decide, by decide⟩, by decide⟩

example : IsReverseDivisor 2178 ∧ (Nat.digits 10 2178).length = 4 :=
  ⟨⟨by decide, 4, by decide, by decide⟩, by decide⟩

-- Hence every reverse divisor is at least `1000`.
example {n : ℕ} (h : IsReverseDivisor n) : 1000 ≤ n :=
  (Nat.lt_digits_length_iff (by decide) n).mp (four_le_length_digits n h)

-- The three-digit value `198 = 22 * (10 ^ 1 - 1)` of the basic formula is not a reverse divisor.
example : ¬ IsReverseDivisor 198 := fun h => by
  simpa using four_le_length_digits 198 h
