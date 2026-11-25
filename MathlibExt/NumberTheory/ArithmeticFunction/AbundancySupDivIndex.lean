/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Data.Nat.Factorization.Basic
public import MathlibExt.NumberTheory.ArithmeticFunction.PrimitiveNondeficient
import Mathlib.Algebra.Order.BigOperators.GroupWithZero.Finset
import Mathlib.Algebra.Ring.GeomSum
import Mathlib.NumberTheory.ArithmeticFunction.Misc
import Mathlib.Tactic.Linarith

/-! # Suryanarayana's bound for the ratio of abundancies -/

open MathlibExt.NumberTheory.PrimitiveNondeficientWanted

namespace MetaMathlibExt

private def primePowerRatio (p k : ℕ) : ℚ := (p : ℚ) ^ k / ((p : ℚ) ^ k - 1)

private theorem abundancyRatio_eq_prod {n : ℕ} (hn : n ≠ 0) :
    abundancySup n / abundancyIndex n =
      ∏ p ∈ n.primeFactors, primePowerRatio p (n.factorization p + 1) := by
  have hprod : (n : ℚ) = ∏ p ∈ n.primeFactors, (p : ℚ) ^ n.factorization p := by
    exact_mod_cast Nat.prod_primeFactors_pow_factorization hn
  rw [abundancyIndex, abundancySup, ← ArithmeticFunction.sigma_one_apply,
    ArithmeticFunction.sigma_eq_prod_primeFactors_sum_range_factorization_pow_mul hn, hprod]
  simp only [mul_one, Nat.cast_prod, Nat.cast_sum, Nat.cast_pow, ← Finset.prod_div_distrib]
  apply Finset.prod_congr rfl
  intro p _
  rw [div_div_div_eq, mul_geom_sum, ← pow_succ', primePowerRatio]

private theorem primePowerRatio_nonneg {p : ℕ} (hp : p.Prime) (k : ℕ) :
    0 ≤ primePowerRatio p k :=
  div_nonneg (by positivity) (sub_nonneg.mpr (one_le_pow₀ (by exact_mod_cast hp.one_le)))

private theorem primePowerRatio_le {p a b : ℕ} (hp : p.Prime) (ha : a ≠ 0) (hab : a ≤ b) :
    primePowerRatio p b ≤ primePowerRatio p a := by
  have hp' : (1 : ℚ) < p := by exact_mod_cast hp.one_lt
  have hpow := pow_le_pow_right₀ hp'.le hab
  have hlt := one_lt_pow₀ hp' ha
  apply (div_le_div_iff₀ (sub_pos.mpr (hlt.trans_le hpow)) (sub_pos.mpr hlt)).2
  linarith

/-- **Suryanarayana's bound for $H(n)/h(n)$ with one odd exponent.** For a positive integer
$n$ write $h(n) = \sigma(n)/n$ for its abundancy index, where $\sigma(n)$ is the sum of the
divisors of $n$, and $H(n) = \prod_{p \mid n} p/(p-1)$ for the product over its prime divisors.
Let $n$ be odd and let $j$ be a prime divisor of $n$ whose exponent in $n$ is odd, while the
exponent of every other prime divisor of $n$ is even. Then
$$\frac{H(n)}{h(n)} \le \frac{j^2}{j^2 - 1} \prod_{p \mid n,\ p \ne j} \frac{p^3}{p^3 - 1},$$
where $p$ runs over the prime divisors of $n$ other than $j$.

Source: Joshua Zelinsky, *The Sum of the Reciprocals of the Prime Divisors of an Odd
Perfect or Odd Primitive Non-deficient Number*, INTEGERS 25 (2025), Article A59,
Lemma 9 (`integers-2025-A59-lem-9`). -/
public theorem abundancySup_div_abundancyIndex_le_of_single_odd_exponent
    (n j : ℕ) (hn : Odd n) (hj : j ∈ n.primeFactors) (hjodd : Odd (n.factorization j))
    (heven : ∀ p ∈ n.primeFactors, p ≠ j → Even (n.factorization p)) :
    abundancySup n / abundancyIndex n ≤
      (j : ℚ) ^ 2 / ((j : ℚ) ^ 2 - 1) *
        ∏ p ∈ n.primeFactors.erase j, (p : ℚ) ^ 3 / ((p : ℚ) ^ 3 - 1) := by
  rw [abundancyRatio_eq_prod hn.pos.ne', ← Finset.mul_prod_erase _ _ hj]
  apply mul_le_mul
  · obtain ⟨k, hk⟩ := hjodd
    exact primePowerRatio_le (Nat.prime_of_mem_primeFactors hj) (by decide) (by omega)
  · apply Finset.prod_le_prod₀
    · intro p hp
      exact primePowerRatio_nonneg (Nat.prime_of_mem_primeFactors (Finset.mem_of_mem_erase hp)) _
    · intro p hp
      obtain ⟨hpj, hpn⟩ := Finset.mem_erase.mp hp
      have hpos := (Nat.prime_of_mem_primeFactors hpn).factorization_pos_of_dvd
        hn.pos.ne' (Nat.dvd_of_mem_primeFactors hpn)
      obtain ⟨k, hk⟩ := heven p hpn hpj
      exact primePowerRatio_le (Nat.prime_of_mem_primeFactors hpn) (by decide) (by omega)
  · exact Finset.prod_nonneg fun p hp =>
      primePowerRatio_nonneg (Nat.prime_of_mem_primeFactors (Finset.mem_of_mem_erase hp)) _
  · exact primePowerRatio_nonneg (Nat.prime_of_mem_primeFactors hj) _

end MetaMathlibExt
