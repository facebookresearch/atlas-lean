/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Data.Nat.Factorization.Basic
public import MathlibExt.NumberTheory.ArithmeticFunction.PrimitiveNondeficient
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import all MathlibExt.NumberTheory.PrimitiveNondeficient

/-!
# Generalized Puchta lemma for primitive non-deficient numbers

Let $n$ be primitive non-deficient with $k$ distinct prime factors and least prime factor $p_1$,
where $(p_1, k) \ne (3, 3)$. For rational $0 < \alpha < 1$ with $H(n) \ge 2 + \alpha$, where
$H(n)$ is the product of $p/(p-1)$ over the prime divisors of $n$, some prime divisor $p$ with
exponent $a$ in $n$ satisfies $p^{a+1} < \max(2(k+2+p_1)/\alpha, k(k+1))$.
The proof compares the correction product for $h(n)$ with an upper bound from the deficient
proper divisor $n/p_1$. It uses an existing telescoping-product bound $p_1 \le k$ in place of
Zelinsky's deduction from Grün's bound. The estimates do not need the exception on $(p_1,k)$
or the upper bound on $\alpha$; both hypotheses are kept as in Lemma 9.

## References

* Joshua Zelinsky, *Must a Primitive Non-Deficient Number Always Have a Small Component?*,
  Journal of Integer Sequences **29** (2026), Article 26.4.3, pp. 1–14, Lemma 9.
  <https://cs.uwaterloo.ca/journals/JIS/VOL29/Zelinsky/zel14.pdf>
* D.R. Heath-Brown, *Odd perfect numbers*, Mathematical Proceedings of the Cambridge
  Philosophical Society **115** (1994), pp. 191–196, §2, Lemma 1 (product-bound argument
  adapted by Zelinsky).
* O. Grün, *Über ungerade vollkommene Zahlen*, Mathematische Zeitschrift **55** (1952),
  pp. 353–354 (the least-prime bound in Zelinsky's proof).
* The Lean proof reuses `abundancyIndex_eq_sup_mul`, `prod_correction_ge`,
  `abundancy_lt_two_mul` and `least_prime_le_card` from
  `MathlibExt.NumberTheory.PrimitiveNondeficient`.
-/

set_option autoImplicit false

namespace MathlibExt.NumberTheory.PrimitiveNondeficientWanted

/-- **Generalized Puchta lemma.** Let $n$ be a primitive non-deficient number with $k$ distinct
prime factors, the least of which is $p_1$, and suppose that $(p_1, k) \ne (3, 3)$. Let $\alpha$
be a rational number with $0 < \alpha < 1$ such that $H(n) \ge 2 + \alpha$, where
$H(n) = \prod_p p/(p-1)$ is the product over the distinct primes $p$ dividing $n$. Then some
prime factor $p$ of $n$ satisfies $p^{a+1} < \max\bigl(2(k + 2 + p_1)/\alpha,\ k(k+1)\bigr)$,
where $a$ is the exponent of $p$ in $n$.

Source: Joshua Zelinsky, "Must a Primitive Non-Deficient Number
Always Have a Small Component?", Lemma 9
(label `GeneralizedPuchtalemma`). -/
public theorem exists_pow_factorization_add_one_lt_max
    (n p₁ : ℕ) (hn : IsPrimitiveNondeficient n)
    (hp₁ : p₁ ∈ n.primeFactors)
    (hmin : ∀ q ∈ n.primeFactors, p₁ ≤ q)
    (_hne : ¬ (p₁ = 3 ∧ n.primeFactors.card = 3))
    (α : ℚ) (hα0 : 0 < α) (_hα1 : α < 1)
    (hH : 2 + α ≤ abundancySup n) :
    ∃ p ∈ n.primeFactors,
      ((p ^ (n.factorization p + 1) : ℕ) : ℚ) <
        max
          (2 * ((n.primeFactors.card : ℚ) + 2 + (p₁ : ℚ)) / α)
          ((n.primeFactors.card : ℚ) *
            ((n.primeFactors.card : ℚ) + 1)) := by
  let k : ℚ := n.primeFactors.card
  let B := max (2 * (k + 2 + (p₁ : ℚ)) / α) (k * (k + 1))
  change ∃ p ∈ n.primeFactors, ((p ^ (n.factorization p + 1) : ℕ) : ℚ) < B
  by_contra! hbound
  have hp₁k : (p₁ : ℚ) ≤ k := by
    dsimp [k]
    exact_mod_cast least_prime_le_card n p₁ hn.1 hp₁ hmin
  have hk : 1 ≤ k := by
    dsimp [k]
    exact_mod_cast (Finset.card_pos.mpr ⟨p₁, hp₁⟩ : 1 ≤ n.primeFactors.card)
  have hk0 : 0 ≤ k := zero_le_one.trans hk
  have hkB : k * (k + 1) ≤ B := le_max_right _ _
  have hB : 1 ≤ B :=
    hk.trans ((le_mul_of_one_le_right hk0 (by linarith only [hk])).trans hkB)
  have hBpos : 0 < B := zero_lt_one.trans_le hB
  let m := 1 / B
  have hm0 : 0 ≤ m := (one_div_pos.mpr hBpos).le
  have hm1 : m ≤ 1 := (div_le_one hBpos).mpr hB
  have hcorr (p : ℕ) (hp : p ∈ n.primeFactors) :
      1 / (p : ℚ) ^ (n.factorization p + 1) ≤ m := by
    have hpB := hbound p hp
    rw [Nat.cast_pow] at hpB
    exact one_div_le_one_div_of_le hBpos hpB
  have hkmul : k * (k + 1) * m ≤ 1 := by
    change k * (k + 1) * (1 / B) ≤ 1
    rwa [mul_one_div, div_le_one hBpos]
  have hkm : k * m ≤ 1 :=
    (mul_le_mul_of_nonneg_right (le_mul_of_one_le_right hk0 (by linarith only [hk])) hm0).trans
      hkmul
  have hlower : (2 + α) * (1 - k * m) ≤ abundancyIndex n := by
    rw [abundancyIndex_eq_sup_mul n hn.1.1]
    exact mul_le_mul hH (prod_correction_ge n m hm1 hcorr) (sub_nonneg.mpr hkm)
      (by linarith only [hH, hα0])
  have hupper : abundancyIndex n < 2 * (1 + (p₁ : ℚ) * m) := by
    apply abundancy_lt_two_mul n p₁ hn hp₁ m
    have hp₁0 : (p₁ : ℚ) ≠ 0 := by exact_mod_cast (Nat.prime_of_mem_primeFactors hp₁).ne_zero
    calc
      1 / (p₁ : ℚ) ^ n.factorization p₁ =
          (p₁ : ℚ) * (1 / (p₁ : ℚ) ^ (n.factorization p₁ + 1)) := by
        rw [pow_succ', mul_one_div]
        simpa only [mul_one] using
          (mul_div_mul_left (1 : ℚ) ((p₁ : ℚ) ^ n.factorization p₁) hp₁0).symm
      _ ≤ (p₁ : ℚ) * m := mul_le_mul_of_nonneg_left (hcorr p₁ hp₁) (Nat.cast_nonneg _)
  -- The two terms in the maximum force the lower bound to reach the strict upper bound.
  have hα : 2 * (k + 2 + (p₁ : ℚ)) * m ≤ α := by
    change 2 * (k + 2 + (p₁ : ℚ)) * (1 / B) ≤ α
    rw [mul_one_div, div_le_iff₀ hBpos, mul_comm α B]
    exact (div_le_iff₀ hα0).mp (le_max_left _ _)
  have hcoef : (k + 2 + (p₁ : ℚ)) * (k * m) ≤ 2 := calc
    _ ≤ (2 * (k + 1)) * (k * m) :=
      mul_le_mul_of_nonneg_right (by linarith only [hp₁k]) (mul_nonneg hk0 hm0)
    _ = 2 * (k * (k + 1) * m) := by ring
    _ ≤ 2 := by linarith only [hkmul]
  have hgap : k + (p₁ : ℚ) ≤ (k + 2 + (p₁ : ℚ)) * (1 - k * m) := by
    nlinarith only [hcoef]
  have hscale := mul_le_mul_of_nonneg_right hα (sub_nonneg.mpr hkm)
  have hgap' := mul_le_mul_of_nonneg_right hgap (show 0 ≤ 2 * m by positivity)
  nlinarith only [hlower.trans_lt hupper, hscale, hgap']

end MathlibExt.NumberTheory.PrimitiveNondeficientWanted
