/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.RingTheory.Radical.NatInt
public import MathlibExt.NumberTheory.Bernoulli.DerivativeDenominator
import MathlibExt.NumberTheory.Bernoulli.KellnerSondowBernoulliDenominator

/-!
# The odd radical conjecture and derivatives of Bernoulli polynomials

Kellner's conjectured list of odd radical indices determines exactly which Bernoulli
polynomials have integral first derivative.
-/

namespace MetaMathlibExt

open Polynomial UniqueFactorizationMonoid

/-- If the base-`p` digit sum of an integral derivative's index reaches `p`, then `p` divides it. -/
private theorem dvd_index_of_digit_sum {m p : ℕ} (hm : 1 ≤ m)
    (hd : polynomialDenominator (Polynomial.bernoulli m) ∣ m + 1)
    (hp : p.Prime) (hle : p ≤ m + 1) (hs : p ≤ (p.digits (m + 1)).sum) : p ∣ m + 1 := by
  by_contra hn
  rw [polynomialDenominator, kellner_sondow_bernoulli_denom m hm] at hd
  apply hn
  apply dvd_trans _ hd
  apply dvd_mul_of_dvd_left
  apply dvd_mul_of_dvd_left
  apply Finset.dvd_prod_of_mem (fun i : ℕ => i)
  exact Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (by omega), hp, hn, hs⟩

/-- If `1 < p`, `p ≤ m` and `m % p + 1 = p`, then the sum of the base-`p` digits of `m` is at
least `p`. -/
public theorem le_digit_sum_of_last_digit {p m : ℕ} (hp : 1 < p) (hle : p ≤ m)
    (hmod : m % p + 1 = p) : p ≤ (p.digits m).sum := by
  have hdiv : m / p ≠ 0 := by
    have := (Nat.one_le_div_iff (by omega : 0 < p)).mpr hle
    omega
  have hne := (Nat.digits_ne_nil_iff_ne_zero (b := p)).mpr hdiv
  have hpos := Nat.getLast_digit_ne_zero p hdiv
  have hsum := List.le_sum_of_mem (List.getLast_mem hne)
  rw [Nat.digits_def' hp (by omega : 0 < m), List.sum_cons]
  omega

private theorem digit_sum_succ_of_no_carry {p m : ℕ} (hp : 1 < p) (hm : 0 < m)
    (hd : ¬ p ∣ m + 1) : (p.digits (m + 1)).sum = (p.digits m).sum + 1 := by
  have hne := mt Nat.dvd_of_mod_eq_zero hd
  have hu := @Nat.add_mod_eq_ite p m 1
  rw [Nat.mod_eq_of_lt hp] at hu
  have hlt := Nat.mod_lt m (by omega : 0 < p)
  split at hu
  · omega
  · rw [Nat.digits_def' hp (Nat.succ_pos m), Nat.digits_def' hp hm,
      Nat.succ_div_of_mod_ne_zero hne, hu, List.sum_cons, List.sum_cons]
    omega

/-- Beyond the first two indices, an integral derivative has an odd radical predecessor. -/
private theorem odd_radical_predecessor {m : ℕ} (hm : 2 ≤ m)
    (hd : polynomialDenominator (Polynomial.bernoulli m) ∣ m + 1) :
    bernoulliDiffDenominator m = radical (m + 1) ∧ Odd m := by
  have heven : 2 ∣ m + 1 := by
    by_contra hn
    apply hn (dvd_index_of_digit_sum (by omega) hd Nat.prime_two (by omega) ?_)
    apply le_digit_sum_of_last_digit (by decide) (by omega)
    omega
  refine ⟨?_, Nat.odd_iff.mpr (by omega)⟩
  rw [bernoulliDiffDenominator, Nat.radical_eq_prod_primeFactors]
  apply Finset.prod_congr _ (fun _ _ => rfl)
  ext p
  rw [Finset.mem_filter, Finset.mem_range, Nat.mem_primeFactors_of_ne_zero (by omega)]
  constructor
  · rintro ⟨hle, hp, hs⟩
    refine ⟨hp, ?_⟩
    by_contra hn
    apply hn (dvd_index_of_digit_sum (by omega) hd hp (by omega) ?_)
    rw [digit_sum_succ_of_no_carry hp.one_lt (by omega) hn]
    omega
  · rintro ⟨hp, hdiv⟩
    have hle := Nat.le_of_dvd (Nat.succ_pos m) hdiv
    have hproper : p ≤ m := by
      have := hp.eq_two_or_odd
      omega
    refine ⟨by omega, hp, le_digit_sum_of_last_digit hp.one_lt hproper ?_⟩
    have hu := Nat.mod_eq_zero_of_dvd hdiv
    rw [Nat.add_mod_eq_ite, Nat.mod_eq_of_lt hp.one_lt] at hu
    have := Nat.mod_lt m hp.pos
    split at hu <;> omega

/-- **The odd radical conjecture implies the integral-derivative conjecture.** For $n \ge 1$, let
$\mathbb{D}_n$ be the product of the primes $p$ with $s_p(n) \ge p$, where $s_p(n)$ is the sum of
the base-$p$ digits of $n$, and let $\operatorname{rad}(m)$ be the product of the distinct primes
dividing $m$. Let $\overline{\mathcal{S}}$ be the set of $n \ge 1$ such that the derivative
$B_n'(x)$ of the Bernoulli polynomial $B_n(x)$ has only integer coefficients. If the odd
integers $n \ge 1$ with $\mathbb{D}_n = \operatorname{rad}(n + 1)$ are exactly
$3, 5, 9, 11, 27, 29, 35, 59$, then
$\overline{\mathcal{S}} = \{1, 2, 4, 6, 10, 12, 28, 30, 36, 60\}$.

The hypothesis is Conjecture 11 of the source, about the set
$\overline{\mathcal{R}} = \{n \ge 1 : \mathbb{D}_n = \operatorname{rad}(n + 1)\}$, restricted to
odd $n$; the conclusion is Conjecture 1, and in particular $\overline{\mathcal{S}}$ is finite.

Source: Bernd C. Kellner, *On the Finiteness of Bernoulli Polynomials Whose Derivative Has Only
Integral Coefficients*, Journal of Integer Sequences 27 (2024), Article 24.2.8, Theorem 12
(`jis-2024-24.2.8-thm-12`). -/
public theorem odd_radical_conjecture_implies_bernoulli_integral_derivative_conjecture
    (h : {n : ℕ | 1 ≤ n ∧ bernoulliDiffDenominator n = radical (n + 1) ∧ Odd n} =
      {3, 5, 9, 11, 27, 29, 35, 59}) :
    bernoulliIntegralDerivativeIndices 1 = {1, 2, 4, 6, 10, 12, 28, 30, 36, 60} := by
  ext n
  constructor
  · intro hn
    obtain _ | m := n
    · exact (Nat.not_succ_le_zero 0 hn.1).elim
    rcases lt_or_ge m 2 with hsmall | hm
    · simp only [Set.mem_insert_iff, Set.mem_singleton_iff]
      omega
    · obtain ⟨hrad, hodd⟩ :=
        odd_radical_predecessor hm ((succ_mem_bernoulliIntegralDerivativeIndices_one_iff m).mp hn)
      have hmem : m ∈ {n : ℕ | 1 ≤ n ∧ bernoulliDiffDenominator n = radical (n + 1) ∧ Odd n} :=
        ⟨by omega, hrad, hodd⟩
      rw [h] at hmem
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hmem ⊢
      omega
  · intro hn
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hn
    rcases hn with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact one_mem_bernoulliIntegralDerivativeIndices_one
    all_goals
      apply (succ_mem_bernoulliIntegralDerivativeIndices_one_iff _).mpr
      rw [polynomialDenominator, kellner_sondow_bernoulli_denom _ (by decide)]
      decide +kernel

end MetaMathlibExt
