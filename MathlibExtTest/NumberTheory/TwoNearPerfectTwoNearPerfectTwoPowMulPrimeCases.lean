/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.NumberTheory.TwoNearPerfectTwoNearPerfectTwoPowMulPrimeCases
import Mathlib.Tactic.NormNum

/-!
# Tests for two-near perfect numbers of the form `2^k p`

The omitted divisors of `24` give the two-power case, and the reversed omitted pair of `56`
gives a mixed case.

Source: Vedant Aryan, Dev Madhavani, Savan Parikh, Ingrid Slattery and Joshua Zelinsky,
*On 2-Near Perfect Numbers*, INTEGERS 24 (2024), Article A61, Theorem 1.
-/

namespace MathlibExtTest.NumberTheory.TwoNearPerfect

-- Check the divisor sums for the zeroth and a positive power independently of the formula.
example : ArithmeticFunction.sigma 1 (2 ^ 0) + 1 = 2 ^ (0 + 1) := by decide

example : ArithmeticFunction.sigma 1 (2 ^ 3) + 1 = 2 ^ (3 + 1) := by decide

example : ∃ a b : ℕ, (3 : ℤ) = 2 ^ 4 - 2 ^ a - 2 ^ b - 1 ∧
    ((2 ^ a = 4 ∧ 2 ^ b = 8) ∨ (2 ^ a = 8 ∧ 2 ^ b = 4)) := by
  obtain ⟨e₁, e₂, horder, hcases⟩ :=
    MetaMathlibExt.two_near_perfect_two_pow_mul_prime_cases (k := 3) (p := 3)
      (d₁ := 4) (d₂ := 8) (by decide) Nat.prime_three
      (by decide) (by decide) (by decide) (by decide)
  rcases horder with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · rcases hcases with h | ⟨a, b, heq, ha, hb⟩ | ⟨a, b, _, _, hb⟩ | ⟨a, b, _, ha, _⟩
    · norm_num at h
    · exact ⟨a, b, heq, Or.inl ⟨ha.symm, hb.symm⟩⟩
    · omega
    · omega
  · rcases hcases with h | ⟨a, b, heq, ha, hb⟩ | ⟨a, b, _, _, hb⟩ | ⟨a, b, _, ha, _⟩
    · norm_num at h
    · exact ⟨a, b, heq, Or.inr ⟨ha.symm, hb.symm⟩⟩
    · omega
    · omega

example : ∃ a b : ℕ, (7 : ℤ) * (1 + 2 ^ b) = 2 ^ 4 - 2 ^ a - 1 ∧
    2 ^ a = 1 ∧ 2 ^ b * 7 = 7 := by
  obtain ⟨e₁, e₂, horder, hcases⟩ :=
    MetaMathlibExt.two_near_perfect_two_pow_mul_prime_cases (k := 3) (p := 7)
      (d₁ := 7) (d₂ := 1) (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide)
  rcases horder with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · rcases hcases with ⟨_, ha, _⟩ | ⟨a, b, _, ha, _⟩ |
        ⟨a, b, _, _, hb⟩ | ⟨a, b, _, _, hb⟩
    · norm_num at ha
    · have h := Nat.prime_seven.dvd_of_dvd_pow (show 7 ∣ 2 ^ a by rw [← ha])
      norm_num at h
    · omega
    · omega
  · rcases hcases with h | ⟨a, b, _, _, hb⟩ | ⟨a, b, heq, ha, hb⟩ |
        ⟨a, b, _, ha, _⟩
    · exact ⟨0, 0, by norm_num, by norm_num, by norm_num⟩
    · have h := Nat.prime_seven.dvd_of_dvd_pow (show 7 ∣ 2 ^ b by rw [← hb])
      norm_num at h
    · exact ⟨a, b, heq, ha.symm, hb.symm⟩
    · omega

end MathlibExtTest.NumberTheory.TwoNearPerfect
