/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.NumberTheory.ArithmeticFunction.Misc
import Mathlib.Algebra.Ring.GeomSum
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination

/-!
# Two-near perfect numbers with omitted divisors `1` and `2^b p^2`

The divisor-sum equation for an odd prime `p` and `1 ≤ b ≤ k` forces the number to be
`36` and the second omitted divisor to be `18`.

Source: Vedant Aryan, Dev Madhavani, Savan Parikh, Ingrid Slattery and Joshua Zelinsky,
*On 2-Near Perfect Numbers*, INTEGERS 24 (2024), Article A61 (arXiv:2310.01305),
Proposition 3.
-/

namespace MetaMathlibExt

private theorem classify_equation {A B p : ℤ} (hp : p = 3 ∨ 5 ≤ p)
    (hodd : p % 2 = 1) (hB : 0 < B) (hfour : B = 2 ∨ 4 ∣ B) (hdA : B ∣ A)
    (heq : A * (p + 1) = (B + 1) * p ^ 2 + p + 2) :
    A = 8 ∧ B = 2 ∧ p = 3 := by
  have hpge : 3 ≤ p := by omega
  let z := A - (B + 1) * (p - 1) - 1
  have hz : z * (p + 1) = B + 2 := by
    dsimp [z]
    linear_combination heq
  have hzpos : 1 ≤ z := by
    by_contra h
    have hzle : z ≤ 0 := by omega
    nlinarith
  have hAval : A = z * p ^ 2 - p + 2 := by
    apply mul_left_cancel₀ (show p + 1 ≠ 0 by omega)
    linear_combination heq - p ^ 2 * hz
  have hd : B ∣ p ^ 2 + p + 2 := by
    convert dvd_sub (hdA.mul_right (p + 1)) (dvd_mul_right B (p ^ 2)) using 1
    linear_combination -heq
  have hdprod : B ∣ (p + 1) * (p + z) := by
    convert dvd_add hd (dvd_refl B) using 1
    linear_combination hz
  have hd2 : B ∣ 2 * (p + z) := by
    convert dvd_sub (hdprod.mul_left z) (dvd_mul_right B (p + z)) using 1
    linear_combination -(p + z) * hz
  have hbound := Int.le_of_dvd (by omega : 0 < 2 * (p + z)) hd2
  rcases hp with rfl | hp
  · have hBtwo : B = 2 := by
      rcases hfour with h | ⟨t, ht⟩
      · exact h
      · omega
    have hz1 : z = 1 := by omega
    exact ⟨by nlinarith [hAval], hBtwo, rfl⟩
  · have hzle : z ≤ 3 := by
      by_contra h
      have hz4 : 4 ≤ z := by omega
      nlinarith
    have hBfour : 4 ∣ B := by
      rcases hfour with h | h
      · nlinarith
      · exact h
    obtain hz1 | hz2 | hz3 : z = 1 ∨ z = 2 ∨ z = 3 := by omega
    · have hd4 : B ∣ 4 := by
        convert dvd_sub hd2 ((dvd_refl B).mul_right 2) using 1
        nlinarith
      have hBle := Int.le_of_dvd (by decide : (0 : ℤ) < 4) hd4
      have hp5 : p = 5 := by nlinarith
      have hB4 : B = 4 := by nlinarith
      have hA22 : A = 22 := by nlinarith [hAval]
      norm_num [hB4, hA22] at hdA
    · obtain ⟨t, ht⟩ := hBfour
      rw [hz2] at hz
      omega
    · have hp5 : p = 5 := by nlinarith
      have hB16 : B = 16 := by nlinarith
      have hA72 : A = 72 := by nlinarith [hAval]
      norm_num [hB16, hA72] at hdA

/-- **$2$-near perfect $2^k p^2$ with omitted divisors $1$ and $2^b p^2$.** Let $p$ be an odd
prime and let $b, k$ be integers with $1 \le b \le k$. If $n = 2^k p^2$ satisfies
$\sigma(n) = 2n + 1 + 2^b p^2$, where $\sigma$ is the sum-of-divisors function (that is, $n$ is
$2$-near perfect with omitted divisors $1$ and $2^b p^2$), then $n = 36$ and $2^b p^2 = 18$.

Source: Vedant Aryan, Dev Madhavani, Savan Parikh, Ingrid Slattery and Joshua Zelinsky,
*On 2-Near Perfect Numbers*, INTEGERS 24 (2024), Article A61, Proposition 3
(`integers-2024-A61-prop-3`). -/
public theorem two_near_perfect_two_pow_mul_prime_sq_case_three {k p b : ℕ}
    (hp : p.Prime) (hp2 : p ≠ 2) (hb : 1 ≤ b) (hbk : b ≤ k)
    (hσ : ArithmeticFunction.sigma 1 (2 ^ k * p ^ 2) =
      2 * (2 ^ k * p ^ 2) + 1 + 2 ^ b * p ^ 2) :
    2 ^ k * p ^ 2 = 36 ∧ 2 ^ b * p ^ 2 = 18 := by
  have htwo : ArithmeticFunction.sigma 1 (2 ^ k) + 1 = 2 * 2 ^ k := by
    rw [ArithmeticFunction.sigma_one_apply_prime_pow Nat.prime_two]
    simpa only [one_add_one_eq_two, mul_one, pow_succ'] using
      geom_sum_mul_add (1 : ℕ) (k + 1)
  have hsquare : ArithmeticFunction.sigma 1 (p ^ 2) = 1 + p + p ^ 2 := by
    simp [ArithmeticFunction.sigma_one_apply_prime_pow hp, Finset.sum_range_succ]
  rw [ArithmeticFunction.isMultiplicative_sigma.map_mul_of_coprime
    (Nat.coprime_pow_primes k 2 Nat.prime_two hp hp2.symm), hsquare] at hσ
  have heq : (2 * 2 ^ k) * (p + 1) = (2 ^ b + 1) * p ^ 2 + p + 2 := by
    nlinarith only [hσ, congrArg (fun t => t * (1 + p + p ^ 2)) htwo]
  have hodd : p % 2 = 1 := Nat.odd_iff.mp (hp.odd_of_ne_two hp2)
  have hpcases : p = 3 ∨ 5 ≤ p := by have := hp.two_le; omega
  have hB : 0 < (2 : ℤ) ^ b := by positivity
  have hfour : (2 : ℤ) ^ b = 2 ∨ 4 ∣ (2 : ℤ) ^ b := by
    by_cases hb1 : b = 1
    · simp [hb1]
    · right
      have h : 4 ∣ (2 : ℕ) ^ b := by
        simpa using Nat.pow_dvd_pow 2 (show 2 ≤ b by omega)
      exact_mod_cast h
  have hdA : (2 : ℤ) ^ b ∣ 2 * 2 ^ k := by
    have h := Nat.pow_dvd_pow 2 hbk
    exact_mod_cast h.mul_left 2
  have heqz : (2 * (2 : ℤ) ^ k) * (p + 1) = (2 ^ b + 1) * p ^ 2 + p + 2 := by
    exact_mod_cast heq
  have hoddz : (p : ℤ) % 2 = 1 := by exact_mod_cast hodd
  obtain ⟨hA, hBtwo, hp3⟩ := classify_equation (by exact_mod_cast hpcases)
    hoddz hB hfour hdA heqz
  have hp3n : p = 3 := by exact_mod_cast hp3
  have hbpow : (2 : ℕ) ^ b = 2 := by exact_mod_cast hBtwo
  have hApow : 2 * (2 : ℕ) ^ k = 8 := by exact_mod_cast hA
  have hkpow : (2 : ℕ) ^ k = 4 := by omega
  norm_num [hp3n, hbpow, hkpow]

end MetaMathlibExt
