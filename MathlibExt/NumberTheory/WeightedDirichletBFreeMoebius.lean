/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Data.Nat.Factorization.Basic
public import MathlibExt.NumberTheory.WeightedDirichletConvolutionBFreeCoprimeIndicatorMulMoebius
import all MathlibExt.NumberTheory.WeightedDirichletConvolutionBFreeCoprimeIndicatorMulMoebius

/-!
# The B-free indicator convolved with Möbius

Specializing the coprimality-restricted convolution to modulus one gives the
untwisted convolution. Its value is the Möbius function of the primewise root
when all the exponent divisions are exact, and zero otherwise.

## References

* André Pierro de Camargo, *Weighted Summation of Dirichlet Convolutions and Applications to Some
  Divisor Problems over k-Free and B-Free Integers*, INTEGERS 24 (2024), Article A75, pp. 1–16,
  Lemma 5, Equation (22); the formal proof specializes Lemma 6, Equation (23).
* Emre Alkan and Alexandru Zaharescu, *A Survey on the Distribution of B-free Numbers*, Turkish
  Journal of Mathematics 30 (2006), no. 3, pp. 293–308, §1. Camargo cites it for B-freeness.
-/

namespace MetaMathlibExt

open ArithmeticFunction Finset
open scoped ArithmeticFunction.Moebius

private theorem factorization_prod_primeFactors_pow (n : ℕ) (f : ℕ → ℕ → ℕ)
    (hf : ∀ p, f p 0 = 0) (q : ℕ) :
    (n.factorization.prod fun p e => p ^ f p e).factorization q = f q (n.factorization q) := by
  classical
  rw [Nat.prod_factorization_eq_prod_primeFactors,
    Nat.factorization_prod_apply (fun p hp =>
      pow_ne_zero _ (Nat.prime_of_mem_primeFactors hp).ne_zero)]
  calc
    _ = ∑ p ∈ n.primeFactors, if p = q then f p (n.factorization p) else 0 := by
      apply sum_congr rfl
      intro p hp
      rw [(Nat.prime_of_mem_primeFactors hp).factorization_pow, Finsupp.single_apply]
    _ = _ := by
      by_cases hq : q ∈ n.primeFactors
      · simp [hq]
      · have hz : n.factorization q = 0 :=
          Finsupp.notMem_support_iff.mp (by simpa only [Nat.support_factorization] using hq)
        simp [hq, hz, hf]

open scoped Classical in
/-- **The $B_\kappa$-free indicator convolved with the Möbius function.** Let $\kappa$ be a
function from the natural numbers to the natural numbers with $\kappa(p) \ge 1$ for every prime
$p$, let $q_{B_\kappa}$ be the indicator of $B_\kappa$-free integers, let $\mu$ be the Möbius
function and let $*$ denote Dirichlet convolution. Let $n \ge 1$ be a natural number with prime
factorization $n = \prod_p p^{e_p}$. If $\kappa(p)$ divides $e_p$ for every prime $p$, then
$(q_{B_\kappa} * \mu)(n) = \mu(n^{1/\kappa})$, where $n^{1/\kappa} = \prod_p p^{e_p/\kappa(p)}$;
otherwise $(q_{B_\kappa} * \mu)(n) = 0$.

The source indexes the exponents by the position of the prime ($\kappa_i$ for the $i$-th prime
$p_i$) and requires $b_i = p_i^{\kappa_i} > 1$, which is the hypothesis $\kappa(p) \ge 1$.

Source: André Pierro de Camargo, *Weighted Summation of Dirichlet Convolutions and Applications
to Some Divisor Problems over k-Free and B-Free Integers*, INTEGERS 24 (2024), Article A75,
Lemma 5, Equation (22) (`integers-2024-A75-lem-5`). -/
public theorem bFreeIndicator_mul_moebius_apply {κ : ℕ → ℕ}
    (hκ : ∀ p : ℕ, p.Prime → 1 ≤ κ p) {n : ℕ} (hn : 1 ≤ n) :
    (bFreeIndicator κ * μ) n =
      if ∀ p : ℕ, κ p ∣ n.factorization p then
        μ (n.factorization.prod fun p e => p ^ (e / κ p))
      else 0 := by
  classical
  have hsum (m : ℕ) : (bFreeIndicator κ * μ) m =
      ∑ d ∈ m.divisors, (if d.Coprime 1 then bFreeIndicator κ d else 0) * μ (m / d) := by
    rw [ArithmeticFunction.mul_apply,
      Nat.sum_divisorsAntidiagonal (fun d e => bFreeIndicator κ d * μ e)]
    simp only [ite_eq_left (Nat.coprime_one_right _)]
  have hspec := bFreeCoprimeIndicator_mul_moebius hκ 1
  have hpower (r p : ℕ) : (kappaPower κ r).factorization p = κ p * r.factorization p :=
    factorization_prod_primeFactors_pow r (fun p e => κ p * e) (fun _ => mul_zero _) p
  by_cases hd : ∀ p : ℕ, κ p ∣ n.factorization p
  · rw [ite_eq_left hd]
    let r := n.factorization.prod fun p e => p ^ (e / κ p)
    have hr : r ≠ 0 := by
      rw [show r = ∏ p ∈ n.primeFactors, p ^ (n.factorization p / κ p) from rfl]
      exact prod_ne_zero_iff.mpr fun p hp =>
        pow_ne_zero _ (Nat.prime_of_mem_primeFactors hp).ne_zero
    have hnr : n = kappaPower κ r := by
      apply Nat.eq_of_factorization_eq (Nat.ne_of_gt hn)
      · rw [kappaPower, Nat.prod_factorization_eq_prod_primeFactors]
        exact prod_ne_zero_iff.mpr fun p hp =>
          pow_ne_zero _ (Nat.prime_of_mem_primeFactors hp).ne_zero
      · intro p
        rw [hpower, show r.factorization p = n.factorization p / κ p from
          factorization_prod_primeFactors_pow n (fun p e => e / κ p) (fun _ => Nat.zero_div _) p,
          Nat.mul_div_cancel' (hd p)]
    change (bFreeIndicator κ * μ) n = μ r
    rw [hsum, hnr]
    simpa only [kappaPower, one_mul, moebius_apply_one] using
      hspec.2 1 r dvd_rfl (Nat.coprime_one_right r) (Nat.pos_of_ne_zero hr)
  · rw [ite_eq_right hd]
    by_contra hnz
    obtain ⟨l, r, hl, -, hr⟩ := hspec.1 n (hsum n ▸ hnz)
    have hnr : n = kappaPower κ r := by simpa only [Nat.dvd_one.mp hl, one_mul, kappaPower] using hr
    apply hd
    intro p
    rw [hnr, hpower]
    exact dvd_mul_right _ _

end MetaMathlibExt
