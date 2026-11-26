/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.NumberTheory.TwoNearPerfectTwoNearPerfectTwoPowMulPrimeSq

/-!
# Tests for the classification of two-near perfect numbers of the form `2^k p^2`

Concrete instances and exclusions using the classification theorem.
-/

namespace MathlibExtTest.NumberTheory.TwoNearPerfectTwoNearPerfectTwoPowMulPrimeSq

example : 18 = 18 ∨ 18 = 36 ∨ 18 = 200 :=
  MetaMathlibExt.two_near_perfect_two_pow_mul_prime_sq (k := 1) Nat.prime_three
    (d₁ := 1) (d₂ := 2) (by decide) (by decide) (by decide) (by decide)

example : 18 = 18 ∨ 18 = 36 ∨ 18 = 200 :=
  MetaMathlibExt.two_near_perfect_two_pow_mul_prime_sq (k := 1) Nat.prime_three
    (d₁ := 2) (d₂ := 1) (by decide) (by decide) (by decide) (by decide)

example : 36 = 18 ∨ 36 = 36 ∨ 36 = 200 :=
  MetaMathlibExt.two_near_perfect_two_pow_mul_prime_sq (k := 2) Nat.prime_three
    (d₁ := 1) (d₂ := 18) (by decide) (by decide) (by decide) (by decide)

example : 200 = 18 ∨ 200 = 36 ∨ 200 = 200 :=
  MetaMathlibExt.two_near_perfect_two_pow_mul_prime_sq (k := 3) (by decide : Nat.Prime 5)
    (d₁ := 25) (d₂ := 40) (by decide) (by decide) (by decide) (by decide)

example {d₁ d₂ : ℕ} (hd₁ : d₁ ∣ 9) (hd₂ : d₂ ∣ 9) (hne : d₁ ≠ d₂) :
    ArithmeticFunction.sigma 1 9 ≠ 2 * 9 + d₁ + d₂ := by
  intro hσ
  have h := MetaMathlibExt.two_near_perfect_two_pow_mul_prime_sq (k := 0)
    Nat.prime_three hd₁ hd₂ hne hσ
  exact (by decide : ¬(9 = 18 ∨ 9 = 36 ∨ 9 = 200)) h

example {d₁ d₂ : ℕ} (hd₁ : d₁ ∣ 16) (hd₂ : d₂ ∣ 16) (hne : d₁ ≠ d₂) :
    ArithmeticFunction.sigma 1 16 ≠ 2 * 16 + d₁ + d₂ := by
  intro hσ
  have h := MetaMathlibExt.two_near_perfect_two_pow_mul_prime_sq (k := 2)
    Nat.prime_two hd₁ hd₂ hne hσ
  exact (by decide : ¬(16 = 18 ∨ 16 = 36 ∨ 16 = 200)) h

end MathlibExtTest.NumberTheory.TwoNearPerfectTwoNearPerfectTwoPowMulPrimeSq
