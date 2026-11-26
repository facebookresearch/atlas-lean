/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.NumberTheory.Digits.ReverseDivisorExistsDvdReverseDigitsMul

/-! # Tests for `MathlibExt.NumberTheory.Digits.ReverseDivisorExistsDvdReverseDigitsMul` -/

namespace MathlibExtTest.NumberTheory.Digits.ReverseDivisorExistsDvdReverseDigitsMul

open MathlibExt.NumberTheory.Digits.ReverseDivisorWanted

-- Coprime case: 7 is coprime to 10.
example : ∃ k₀ : ℕ, 1 ≤ k₀ ∧ 7 ∣ Nat.reverseDigits 10 (k₀ * 7) :=
  exists_dvd_reverseDigits_mul 7 (Or.inl (by decide))

-- Palindrome case: 121 reads the same backwards.
example : ∃ k₀ : ℕ, 1 ≤ k₀ ∧ 121 ∣ Nat.reverseDigits 10 (k₀ * 121) :=
  exists_dvd_reverseDigits_mul 121 (Or.inr (Or.inl (by decide)))

-- Reverse divisor case: 1089 reverses to 9 * 1089.
example : ∃ k₀ : ℕ, 1 ≤ k₀ ∧ 1089 ∣ Nat.reverseDigits 10 (k₀ * 1089) :=
  exists_dvd_reverseDigits_mul 1089
    (Or.inr (Or.inr ⟨by decide, 9, by decide, by decide⟩))

end MathlibExtTest.NumberTheory.Digits.ReverseDivisorExistsDvdReverseDigitsMul
