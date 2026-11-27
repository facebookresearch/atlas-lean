/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.NumberTheory.TwoNearPerfectTwoNearPerfectTwoPowMulPrimeSqCaseFive
/-! # Tests for `MathlibExt.NumberTheory.TwoNearPerfect` -/

namespace MathlibExtTest.NumberTheory.TwoNearPerfect

open MetaMathlibExt

-- At 36, the Case V equation cannot hold with `m = j = 1` and `b = 1`.
example (h : ArithmeticFunction.sigma 1 (2 ^ 2 * 3 ^ 2)
    = 2 * (2 ^ 2 * 3 ^ 2) + 3 ^ 1 + 2 ^ 1 * 3 ^ 1) : False := by
  have h200 := two_near_perfect_two_pow_mul_prime_sq_case_five (k := 2) (p := 3) (m := 1)
    (b := 1) (j := 1) (by decide) (by decide) (Or.inl rfl) (by decide) (by decide)
    (Or.inl rfl) h
  exact absurd h200 (by decide)

-- Corollary: the prime in any Case V instance is `5`.
example {k p m b j : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hm : m = 1 ∨ m = 2) (hb : 1 ≤ b)
    (hbk : b ≤ k) (hj : j = 1 ∨ j = 2)
    (hσ : ArithmeticFunction.sigma 1 (2 ^ k * p ^ 2) =
      2 * (2 ^ k * p ^ 2) + p ^ m + 2 ^ b * p ^ j) :
    p = 5 := by
  have h200 := two_near_perfect_two_pow_mul_prime_sq_case_five hp hp2 hm hb hbk hj hσ
  have hpdvd : p ∣ 200 := by
    rw [← h200]
    have hpp : p ∣ p ^ 2 := by
      rw [pow_two]
      exact dvd_mul_right _ _
    exact dvd_mul_of_dvd_right hpp _
  have e200 : (200 : ℕ) = 2 ^ 3 * 5 ^ 2 := by decide
  rw [e200] at hpdvd
  rcases (hp.prime.dvd_mul).mp hpdvd with h | h
  · have h2 := Nat.Prime.dvd_of_dvd_pow hp h
    have hp2eq : p = 2 := by
      have hle := Nat.le_of_dvd (by decide) h2
      have h2le := hp.two_le
      omega
    omega
  · exact Nat.prime_eq_prime_of_dvd_pow hp (by decide) h

end MathlibExtTest.NumberTheory.TwoNearPerfect
