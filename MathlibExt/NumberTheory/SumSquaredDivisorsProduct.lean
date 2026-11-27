/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import Mathlib.Algebra.Field.GeomSum
import Mathlib.Algebra.Order.BigOperators.GroupWithZero.Finset
public import Mathlib.Algebra.Order.Field.Rat
public import Mathlib.NumberTheory.ArithmeticFunction.Misc

/-!
# Product formulas for the sum of squared divisors

The prime-power factors of the sum of squared divisors are finite geometric sums.
Dividing by the square of the input gives a product whose factors are strictly
bounded by the corresponding infinite geometric series values.
-/

namespace MetaMathlibExt

/-- **Product formulas for the sum of squared divisors.** Let $n \ne 0$ be a natural number,
let $\sigma_2(n)$ be the sum of the squares of the divisors of $n$, and for each prime $p$
dividing $n$ let $k_p$ be the exponent of $p$ in $n$. Then, with products over the primes $p$
dividing $n$,
$$\sigma_2(n) = \prod_{p \mid n} \frac{p^{2(k_p + 1)} - 1}{p^2 - 1}$$
and
$$\frac{\sigma_2(n)}{n^2} = \prod_{p \mid n} \frac{p^{2(k_p + 1)} - 1}{p^{2k_p} (p^2 - 1)}.$$
If moreover $n > 1$, then $\sigma_2(n)/n^2 < \prod_{p \mid n} p^2/(p^2 - 1)$.

Source: Jayanta Kalita and Helen K. Saikia, *A Study on Generalized Zumkeller
Numbers*, INTEGERS 24 (2024), Article A95, Lemma 1(ii) (quoting Peng and
Bhaskara Rao). -/
public theorem sigma_two_prod_formulas (n : ℕ) (hn : n ≠ 0) :
    (ArithmeticFunction.sigma 2 n : ℚ) =
        ∏ p ∈ n.primeFactors, ((p : ℚ) ^ (2 * (n.factorization p + 1)) - 1) / (p ^ 2 - 1) ∧
      (ArithmeticFunction.sigma 2 n : ℚ) / n ^ 2 =
        ∏ p ∈ n.primeFactors,
          ((p : ℚ) ^ (2 * (n.factorization p + 1)) - 1) /
            ((p : ℚ) ^ (2 * n.factorization p) * (p ^ 2 - 1)) ∧
      (1 < n → (ArithmeticFunction.sigma 2 n : ℚ) / n ^ 2 <
        ∏ p ∈ n.primeFactors, (p : ℚ) ^ 2 / (p ^ 2 - 1)) := by
  have hp (p : ℕ) (h : p ∈ n.primeFactors) : 1 < (p : ℚ) := by
    exact_mod_cast (Nat.prime_of_mem_primeFactors h).one_lt
  have hpSq (p : ℕ) (h : p ∈ n.primeFactors) : 1 < (p : ℚ) ^ 2 :=
    one_lt_pow₀ (hp p h) (by decide)
  have hSigma : (ArithmeticFunction.sigma 2 n : ℚ) =
      ∏ p ∈ n.primeFactors, ((p : ℚ) ^ (2 * (n.factorization p + 1)) - 1) / (p ^ 2 - 1) := by
    rw [ArithmeticFunction.sigma_eq_prod_primeFactors_sum_range_factorization_pow_mul hn]
    push_cast
    refine Finset.prod_congr rfl fun p h ↦ ?_
    simpa only [pow_mul, Nat.mul_comm _ 2] using
      (geom_sum_eq (ne_of_gt (hpSq p h)) (n.factorization p + 1))
  have hSquare : (n : ℚ) ^ 2 = ∏ p ∈ n.primeFactors, (p : ℚ) ^ (2 * n.factorization p) := by
    have hFactor : (n : ℚ) = ∏ p ∈ n.primeFactors, (p : ℚ) ^ n.factorization p := by
      exact_mod_cast Nat.prod_primeFactors_pow_factorization hn
    conv_lhs => rw [hFactor]
    rw [← Finset.prod_pow]
    exact Finset.prod_congr rfl fun p _ ↦ by rw [← pow_mul, Nat.mul_comm]
  have hNormalized : (ArithmeticFunction.sigma 2 n : ℚ) / n ^ 2 =
      ∏ p ∈ n.primeFactors, ((p : ℚ) ^ (2 * (n.factorization p + 1)) - 1) /
        ((p : ℚ) ^ (2 * n.factorization p) * (p ^ 2 - 1)) := by
    rw [hSigma, hSquare, ← Finset.prod_div_distrib]
    exact Finset.prod_congr rfl fun p _ ↦ by
      rw [div_div, mul_comm ((p : ℚ) ^ 2 - 1)]
  refine ⟨hSigma, hNormalized, fun hn₁ ↦ ?_⟩
  rw [hNormalized]
  refine Finset.prod_lt_prod_of_nonempty₀ ?_ ?_ (Nat.nonempty_primeFactors.mpr hn₁)
  · intro p h
    have hpow := one_lt_pow₀ (hpSq p h) (Nat.succ_ne_zero (n.factorization p))
    rw [pow_mul]
    exact div_pos (sub_pos.mpr hpow)
      (mul_pos (pow_pos (zero_lt_one.trans (hp p h)) _) (sub_pos.mpr (hpSq p h)))
  · intro p h
    have hpow : 0 < (p : ℚ) ^ (2 * n.factorization p) := pow_pos (zero_lt_one.trans (hp p h)) _
    have hden : 0 < (p : ℚ) ^ 2 - 1 := sub_pos.mpr (hpSq p h)
    calc
      _ < (p : ℚ) ^ (2 * (n.factorization p + 1)) /
          ((p : ℚ) ^ (2 * n.factorization p) * (p ^ 2 - 1)) :=
        (div_lt_div_iff_of_pos_right (mul_pos hpow hden)).2 (sub_lt_self _ zero_lt_one)
      _ = (p : ℚ) ^ 2 / (p ^ 2 - 1) := by
        rw [Nat.mul_add, Nat.mul_one, pow_add, mul_div_mul_left _ _ hpow.ne']

end MetaMathlibExt
