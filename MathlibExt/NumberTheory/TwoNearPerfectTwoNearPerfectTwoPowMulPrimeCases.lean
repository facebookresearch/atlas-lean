/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.NumberTheory.ArithmeticFunction.Misc
import Mathlib.Algebra.Ring.GeomSum
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Zify

/-!
# Two-near perfect numbers of the form `2^k p`

Classify the two omitted divisors of a two-near perfect number `2^k p`, where `p` is prime,
after possibly exchanging their order. The classification is a necessary condition.

Source: Vedant Aryan, Dev Madhavani, Savan Parikh, Ingrid Slattery and Joshua Zelinsky,
*On 2-Near Perfect Numbers*, INTEGERS 24 (2024), Article A61, Theorem 1 (arXiv:2310.01305).
-/

namespace MetaMathlibExt

private theorem sigma_two_pow_add_one (k : ℕ) :
    ArithmeticFunction.sigma 1 (2 ^ k) + 1 = 2 ^ (k + 1) := by
  rw [ArithmeticFunction.sigma_one_apply_prime_pow Nat.prime_two]
  simpa only [one_add_one_eq_two, mul_one] using geom_sum_mul_add (1 : ℕ) (k + 1)

private theorem divisor_two_pow_mul_prime {k p d : ℕ} (hp : p.Prime)
    (hd : d ∣ 2 ^ k * p) : ∃ a : ℕ, d = 2 ^ a ∨ d = 2 ^ a * p := by
  obtain ⟨x, y, hx, hy, rfl⟩ := exists_dvd_and_dvd_of_dvd_mul hd
  obtain ⟨a, _, rfl⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp hx
  rcases hp.eq_one_or_self_of_dvd y hy with rfl | rfl
  · exact ⟨a, Or.inl (mul_one _)⟩
  · exact ⟨a, Or.inr rfl⟩

private theorem omitted_divisors_equation {k p d₁ d₂ : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hσ : ArithmeticFunction.sigma 1 (2 ^ k * p) = 2 * (2 ^ k * p) + d₁ + d₂) :
    (p : ℤ) + d₁ + d₂ = 2 ^ (k + 1) - 1 := by
  have htwo := sigma_two_pow_add_one k
  have hprime : ArithmeticFunction.sigma 1 p = p + 1 := by
    simpa only [pow_one, Finset.sum_range_succ, Finset.sum_range_zero, zero_add, pow_zero,
      add_comm] using ArithmeticFunction.sigma_one_apply_prime_pow (i := 1) hp
  rw [ArithmeticFunction.isMultiplicative_sigma.map_mul_of_coprime
    (by simpa only [pow_one] using
      Nat.coprime_pow_primes k 1 Nat.prime_two hp hp2.symm), hprime] at hσ
  zify at htwo hσ ⊢
  rw [pow_succ (2 : ℤ) k] at htwo ⊢
  linear_combination (p + 1) * htwo - hσ

/-- **$2$-near perfect numbers of the form $2^k p$.** Let $k \ge 1$, let $p$ be a prime and let
$n = 2^k p$. Suppose $d_1 \ne d_2$ are divisors of $n$ with $\sigma(n) = 2n + d_1 + d_2$, where
$\sigma$ is the sum-of-divisors function (that is, $n$ is $2$-near perfect with omitted divisors
$d_1, d_2$). Then, after possibly swapping $d_1$ and $d_2$, one of the following holds, where
all equations are between integers: (1) $p = 2^k - 1$, $d_1 = 1$ and $d_2 = p$; (2) for some
natural numbers $a, b$, $p = 2^{k+1} - 2^a - 2^b - 1$, $d_1 = 2^a$ and $d_2 = 2^b$; (3) for some
natural numbers $a, b$, $p(1 + 2^b) = 2^{k+1} - 2^a - 1$, $d_1 = 2^a$ and $d_2 = 2^b p$; (4) for
some natural numbers $a, b$, $p(1 + 2^a + 2^b) = 2^{k+1} - 1$, $d_1 = 2^a p$ and $d_2 = 2^b p$.

The paper states only this necessary direction; the four situations are not sufficient as
printed ($k = 3$, $a = b = 1$ gives the prime $p = 11$ in situation 2, but $d_1 = d_2 = 2$).

Source: Vedant Aryan, Dev Madhavani, Savan Parikh, Ingrid Slattery and Joshua Zelinsky,
*On 2-Near Perfect Numbers*, INTEGERS 24 (2024), Article A61, Theorem 1
(`integers-2024-A61-thm-1`). -/
public theorem two_near_perfect_two_pow_mul_prime_cases {k p d₁ d₂ : ℕ} (hk : 0 < k)
    (hp : p.Prime) (hd₁ : d₁ ∣ 2 ^ k * p) (hd₂ : d₂ ∣ 2 ^ k * p) (hne : d₁ ≠ d₂)
    (hσ : ArithmeticFunction.sigma 1 (2 ^ k * p) = 2 * (2 ^ k * p) + d₁ + d₂) :
    ∃ e₁ e₂ : ℕ, ((e₁ = d₁ ∧ e₂ = d₂) ∨ (e₁ = d₂ ∧ e₂ = d₁)) ∧
      (((p : ℤ) = 2 ^ k - 1 ∧ e₁ = 1 ∧ e₂ = p) ∨
        (∃ a b : ℕ, (p : ℤ) = 2 ^ (k + 1) - 2 ^ a - 2 ^ b - 1 ∧ e₁ = 2 ^ a ∧ e₂ = 2 ^ b) ∨
        (∃ a b : ℕ, (p : ℤ) * (1 + 2 ^ b) = 2 ^ (k + 1) - 2 ^ a - 1 ∧
          e₁ = 2 ^ a ∧ e₂ = 2 ^ b * p) ∨
        (∃ a b : ℕ, (p : ℤ) * (1 + 2 ^ a + 2 ^ b) = 2 ^ (k + 1) - 1 ∧
          e₁ = 2 ^ a * p ∧ e₂ = 2 ^ b * p)) := by
  by_cases hp2 : p = 2
  · subst p
    obtain ⟨l, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hk)
    have hpositive : 0 < d₁ + d₂ := by omega
    have htwo := sigma_two_pow_add_one (l + 1 + 1)
    rw [← pow_succ] at hσ
    simp only [pow_succ, Nat.succ_eq_add_one] at htwo hσ
    omega
  have heq := omitted_divisors_equation hp hp2 hσ
  obtain ⟨a, ha | ha⟩ := divisor_two_pow_mul_prime hp hd₁
  · obtain ⟨b, hb | hb⟩ := divisor_two_pow_mul_prime hp hd₂
    · refine ⟨d₁, d₂, Or.inl ⟨rfl, rfl⟩, Or.inr (Or.inl ⟨a, b, ?_, ha, hb⟩)⟩
      rw [ha, hb] at heq
      push_cast at heq
      linear_combination heq
    · refine ⟨d₁, d₂, Or.inl ⟨rfl, rfl⟩, Or.inr (Or.inr (Or.inl ⟨a, b, ?_, ha, hb⟩))⟩
      rw [ha, hb] at heq
      push_cast at heq
      linear_combination heq
  · obtain ⟨b, hb | hb⟩ := divisor_two_pow_mul_prime hp hd₂
    · refine ⟨d₂, d₁, Or.inr ⟨rfl, rfl⟩, Or.inr (Or.inr (Or.inl ⟨b, a, ?_, hb, ha⟩))⟩
      rw [ha, hb] at heq
      push_cast at heq
      linear_combination heq
    · refine ⟨d₁, d₂, Or.inl ⟨rfl, rfl⟩, Or.inr (Or.inr (Or.inr ⟨a, b, ?_, ha, hb⟩))⟩
      rw [ha, hb] at heq
      push_cast at heq
      linear_combination heq

end MetaMathlibExt
