/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Data.Nat.Prime.Int
import Mathlib.Algebra.Order.Group.Unbundled.Int
import Mathlib.Tactic.Ring

namespace MetaMathlibExt

/-- **Large odd primes do not divide $k^2 - 4$.** Let $p$ be an odd prime and $k$ a natural
number. If either $k \ge 4$ is even and $p > k/2 + 1$, or $k$ is odd and $p > k + 2$, then $p$
does not divide $k^2 - 4$.

Source: Y. Gyoda and S. Maruyama, *Uniqueness Theorem of Generalized Markov Numbers That
Are Prime Powers*, INTEGERS 26 (2026), Article A91, Proposition 4.15. -/
public theorem not_dvd_sq_sub_four_of_large_prime {k p : ℕ} (hp : p.Prime)
    (hp2 : p ≠ 2) (h : (4 ≤ k ∧ Even k ∧ k / 2 + 1 < p) ∨ (Odd k ∧ k + 2 < p)) :
    ¬ (p : ℤ) ∣ (k : ℤ) ^ 2 - 4 := by
  have hp' := Nat.prime_iff_prime_int.mp hp
  have small {a : ℤ} (hne : a ≠ 0) (hlt : -(p : ℤ) < a ∧ a < p) : ¬ (p : ℤ) ∣ a :=
    fun hd => hne (Int.eq_zero_of_abs_lt_dvd hd (abs_lt.mpr hlt))
  rcases h with ⟨hk, ⟨m, rfl⟩, hbound⟩ | ⟨⟨m, rfl⟩, hbound⟩
  · have htwo : ¬ (p : ℤ) ∣ 2 := by
      exact_mod_cast mt (Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp hp2
    rw [Nat.cast_add, show ((m : ℤ) + m) ^ 2 - 4 =
      (2 * 2) * ((m - 1) * (m + 1)) by ring]
    apply hp'.not_dvd_mul (hp'.not_dvd_mul htwo htwo)
    apply hp'.not_dvd_mul <;> apply small <;> omega
  · rw [show (4 : ℤ) = 2 ^ 2 by decide, sq_sub_sq]
    apply hp'.not_dvd_mul <;> apply small <;> omega

end MetaMathlibExt
