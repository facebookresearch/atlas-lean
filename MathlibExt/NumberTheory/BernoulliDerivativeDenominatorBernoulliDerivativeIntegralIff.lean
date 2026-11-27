/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.RingTheory.Radical.Basic
public import Mathlib.RingTheory.UniqueFactorizationDomain.Nat
public import MathlibExt.NumberTheory.Bernoulli.OddRadical
public import MathlibExt.NumberTheory.Bernoulli.PolynomialDenominatorRadical
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise
import Mathlib.Algebra.GCDMonoid.Finset
import Mathlib.Algebra.Order.BigOperators.Group.List
import Mathlib.Algebra.Polynomial.Coeff
import Mathlib.Data.Nat.Digits.Defs
import Mathlib.Data.Nat.Digits.Lemmas
import Mathlib.Data.Nat.GCD.BigOperators
import Mathlib.Data.Nat.Prime.Defs
import Mathlib.Data.Nat.PrimeFin
import Mathlib.Data.Rat.Lemmas
import Mathlib.Data.Set.Operations
import Mathlib.Logic.Function.Iterate
import Mathlib.NumberTheory.BernoulliPolynomials
import Mathlib.RingTheory.Radical.NatInt
import MathlibExt.NumberTheory.Bernoulli.KellnerSondowBernoulliDenominator

/-!
# Integrality of the derivative of a Bernoulli polynomial

For `n ≥ 1`, the derivative `Bₙ'(x)` has integer coefficients iff `𝔻^⊥ₙ = 1`, iff the
denominator of `Bₙ₋₁(x)` equals `rad(n)`; then `n + 1` is prime.

Source: Bernd C. Kellner, *On the Finiteness of Bernoulli Polynomials Whose Derivative Has Only
Integral Coefficients*, Journal of Integer Sequences 27 (2024), Article 24.2.8, Theorem 9
(`jis-2024-24.2.8-thm-9`).
-/

namespace MetaMathlibExt

@[expose] public section

open Polynomial UniqueFactorizationMonoid

private theorem prod_dvd_merge (n : ℕ) :
    (∏ p ∈ (Finset.range (n + 1)).filter
        (fun p => Nat.Prime p ∧ p ∣ n ∧ p ≤ (Nat.digits p n).sum), p) *
      (∏ p ∈ (Finset.range (n + 1)).filter
        (fun p => Nat.Prime p ∧ p ∣ n ∧ (Nat.digits p n).sum < p), p) =
      ∏ p ∈ (Finset.range (n + 1)).filter
        (fun p => Nat.Prime p ∧ p ∣ n), p := by
  have e1 : ((Finset.range (n + 1)).filter
      (fun p => Nat.Prime p ∧ p ∣ n)).filter
      (fun p => p ≤ (Nat.digits p n).sum) =
      (Finset.range (n + 1)).filter
        (fun p => Nat.Prime p ∧ p ∣ n ∧ p ≤ (Nat.digits p n).sum) := by
    ext p
    simp only [Finset.mem_filter]
    tauto
  have e2 : ((Finset.range (n + 1)).filter
      (fun p => Nat.Prime p ∧ p ∣ n)).filter
      (fun p => ¬ p ≤ (Nat.digits p n).sum) =
      (Finset.range (n + 1)).filter
        (fun p => Nat.Prime p ∧ p ∣ n ∧ (Nat.digits p n).sum < p) := by
    ext p
    simp only [Finset.mem_filter, not_le]
    tauto
  rw [← e1, ← e2, Finset.prod_filter_mul_prod_filter_not]

private theorem prod_dvd_eq_radical (n : ℕ) (hn : 1 ≤ n) :
    (∏ p ∈ (Finset.range (n + 1)).filter
      (fun p => Nat.Prime p ∧ p ∣ n), p) = radical n := by
  rw [Nat.radical_eq_prod_primeFactors]
  apply Finset.prod_congr _ (fun _ _ => rfl)
  ext p
  rw [Finset.mem_filter, Finset.mem_range,
    Nat.mem_primeFactors_of_ne_zero (by omega : n ≠ 0)]
  constructor
  · rintro ⟨-, hp, hdvd⟩
    exact ⟨hp, hdvd⟩
  · rintro ⟨hp, hdvd⟩
    have hle : p ≤ n := Nat.le_of_dvd (by omega) hdvd
    exact ⟨by omega, hp, hdvd⟩

private theorem denom_bernoulli_eq_coprime_mul_radical (n : ℕ) (hn : 2 ≤ n) :
    polynomialDenominator (Polynomial.bernoulli (n - 1)) =
      bernoulliDiffDenominatorCoprimePart n * radical n := by
  have hm : 1 ≤ n - 1 := by omega
  have hks := kellner_sondow_bernoulli_denom (n - 1) hm
  rw [polynomialDenominator]
  rw [hks]
  have h1 : n - 1 + 1 = n := by omega
  have h2 : n - 1 + 2 = n + 1 := by omega
  rw [h1, h2] at hks ⊢
  have hA : (∏ p ∈ (Finset.range (n + 1)).filter
        (fun p => Nat.Prime p ∧ ¬ p ∣ n ∧ p ≤ (Nat.digits p n).sum), p) =
      bernoulliDiffDenominatorCoprimePart n := rfl
  rw [← hA]
  rw [mul_assoc]
  congr 1
  rw [prod_dvd_merge, prod_dvd_eq_radical n (by omega)]

private theorem coprime_coprimePart (n : ℕ) :
    Nat.Coprime (bernoulliDiffDenominatorCoprimePart n) n := by
  rw [bernoulliDiffDenominatorCoprimePart, Nat.coprime_prod_left_iff]
  intro p hp
  rw [Finset.mem_filter] at hp
  obtain ⟨-, hprime, hndvd, -⟩ := hp
  exact (hprime.coprime_iff_not_dvd).mpr hndvd

/-- **Integrality of the derivative of a Bernoulli polynomial.** Let $n \ge 1$, let $B_m(x)$
denote the $m$-th Bernoulli polynomial, write $s_p(n)$ for the sum of the base-$p$ digits of $n$,
and let $\mathbb{D}^\perp_n$ be the product of the primes $p$ with $p \nmid n$ and
$s_p(n) \ge p$. Then $B_n'(x)$ has integer coefficients if and only if $\mathbb{D}^\perp_n = 1$,
and $\mathbb{D}^\perp_n = 1$ if and only if the denominator of $B_{n-1}(x)$ equals the radical
$\operatorname{rad}(n)$. Moreover, if $B_n'(x)$ has integer coefficients, then $n + 1$ is prime.

Source: Bernd C. Kellner, *On the Finiteness of Bernoulli Polynomials Whose Derivative Has Only
Integral Coefficients*, Journal of Integer Sequences 27 (2024), Article 24.2.8, Theorem 9
(`jis-2024-24.2.8-thm-9`). -/
public theorem bernoulli_derivative_integral_iff (n : ℕ) (hn : 1 ≤ n) :
    (n ∈ bernoulliIntegralDerivativeIndices 1 ↔ bernoulliDiffDenominatorCoprimePart n = 1) ∧
    (bernoulliDiffDenominatorCoprimePart n = 1 ↔
      polynomialDenominator (Polynomial.bernoulli (n - 1)) = radical n) ∧
    (n ∈ bernoulliIntegralDerivativeIndices 1 → (n + 1).Prime) := by
  rcases eq_or_ne n 1 with rfl | hne
  · have hleft : 1 ∈ bernoulliIntegralDerivativeIndices 1 :=
      one_mem_bernoulliIntegralDerivativeIndices_one
    have hD1 : bernoulliDiffDenominatorCoprimePart 1 = 1 := by decide +kernel
    have hD0 : polynomialDenominator (Polynomial.bernoulli (1 - 1)) =
        radical 1 := by
      have h0 : (1 : ℕ) - 1 = 0 := rfl
      rw [h0, polynomialDenominator_bernoulli_zero,
        UniqueFactorizationMonoid.radical_one]
    refine ⟨iff_of_true hleft hD1, iff_of_true hD1 hD0, fun _ => Nat.prime_two⟩
  · have hn2 : 2 ≤ n := by omega
    have hfact := denom_bernoulli_eq_coprime_mul_radical n hn2
    have hmem_iff : (n ∈ bernoulliIntegralDerivativeIndices 1 ↔
        polynomialDenominator (Polynomial.bernoulli (n - 1)) ∣ n) := by
      have h := succ_mem_bernoulliIntegralDerivativeIndices_one_iff (n - 1)
      rwa [Nat.sub_add_cancel hn] at h
    have hpart1 : (n ∈ bernoulliIntegralDerivativeIndices 1 ↔
        bernoulliDiffDenominatorCoprimePart n = 1) := by
      rw [hmem_iff]
      constructor
      · intro hdvd
        rw [hfact] at hdvd
        have hdiv : bernoulliDiffDenominatorCoprimePart n ∣ n :=
          dvd_trans (Nat.dvd_mul_right _ _) hdvd
        exact (coprime_coprimePart n).eq_one_of_dvd hdiv
      · intro h1
        rw [hfact, h1, one_mul]
        exact UniqueFactorizationMonoid.radical_dvd_self
    have hpart2 : (bernoulliDiffDenominatorCoprimePart n = 1 ↔
        polynomialDenominator (Polynomial.bernoulli (n - 1)) = radical n) := by
      constructor
      · intro h
        rw [hfact, h, one_mul]
      · intro h
        rw [hfact] at h
        have hpos : 0 < radical n := Nat.radical_pos n
        have h1 : bernoulliDiffDenominatorCoprimePart n * radical n =
            1 * radical n := by
          rw [h, one_mul]
        exact Nat.mul_right_cancel hpos h1
    have hpart3 : (n ∈ bernoulliIntegralDerivativeIndices 1 → (n + 1).Prime) := by
      intro hmem
      have hD : bernoulliDiffDenominatorCoprimePart n = 1 := hpart1.mp hmem
      by_contra hnot
      have hne1 : n + 1 ≠ 1 := by omega
      obtain ⟨p, hp, hdvd⟩ := Nat.exists_prime_and_dvd hne1
      obtain ⟨q, hq⟩ := hdvd
      have hplt : p < n + 1 := by
        have hle : p ≤ n + 1 := Nat.le_of_dvd (by omega) ⟨q, hq⟩
        have hne' : p ≠ n + 1 := by
          intro heq
          rw [heq] at hp
          exact hnot hp
        omega
      have hndvd : ¬ p ∣ n := by
        intro hdvd2
        have hdvd1 : p ∣ n + 1 := ⟨q, hq⟩
        have hsub := Nat.dvd_sub hdvd1 hdvd2
        rw [show n + 1 - n = 1 by omega] at hsub
        exact hp.ne_one (Nat.dvd_one.mp hsub)
      have hmod : n % p + 1 = p := by
        have h0 : (n + 1) % p = 0 := Nat.mod_eq_zero_of_dvd ⟨q, hq⟩
        rw [Nat.add_mod, Nat.mod_eq_of_lt hp.one_lt] at h0
        have hlt := Nat.mod_lt n hp.pos
        have hle := Nat.le_of_dvd (by omega) (Nat.dvd_of_mod_eq_zero h0)
        omega
      have hsum : p ≤ (Nat.digits p n).sum := le_digit_sum_of_last_digit hp.one_lt (by omega) hmod
      have hmem_filter : p ∈ (Finset.range (n + 1)).filter
          (fun p => p.Prime ∧ ¬ p ∣ n ∧ p ≤ (Nat.digits p n).sum) := by
        rw [Finset.mem_filter, Finset.mem_range]
        exact ⟨by omega, hp, hndvd, hsum⟩
      have hdvdD : p ∣ bernoulliDiffDenominatorCoprimePart n := by
        rw [bernoulliDiffDenominatorCoprimePart]
        exact Finset.dvd_prod_of_mem _ hmem_filter
      rw [hD, Nat.dvd_one] at hdvdD
      exact hp.ne_one hdvdD
    exact ⟨hpart1, hpart2, hpart3⟩

end

end MetaMathlibExt
