/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.NumberTheory.Digits.ReverseDivisorCoprime

open MathlibExt.NumberTheory.Digits.ReverseDivisorWanted

-- Both palindromes divide their own reversals, but each shares a prime factor with ten.
example : Nat.reverseDigits 10 22 = 22 ∧ ¬ HasPropertyPStar 22 :=
  ⟨by decide, not_hasPropertyPStar_of_not_coprime 22 (by decide) (by decide)⟩

example : Nat.reverseDigits 10 55 = 55 ∧ ¬ HasPropertyPStar 55 :=
  ⟨by decide, not_hasPropertyPStar_of_not_coprime 55 (by decide) (by decide)⟩

-- Positivity is necessary since the only multiple of zero is zero.
example : HasPropertyPStar 0 := by
  intro m hm
  obtain rfl := Nat.zero_dvd.mp hm
  decide
