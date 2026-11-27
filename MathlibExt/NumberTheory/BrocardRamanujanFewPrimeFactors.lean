/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Data.Nat.Factorial.Basic
public import Mathlib.Data.Nat.PrimeFin
public import Mathlib.Data.Set.Finite.Basic
import Mathlib.Basic.Finite.Prod
import Mathlib.Data.Nat.Choose.Factorization
import Mathlib.Order.Filter.AtTopBot.Finite
import Mathlib.Tactic.Ring

/-!
# Brocard–Ramanujan solutions with few prime factors

For a positive divisor `y` of `n!`, the factorial valuation bound and `p ≤ 2 ^ (p - 1)`
give `p ^ y.factorization p ≤ 2 ^ n` for each prime divisor `p`. Thus if `y` has fewer
than `l` distinct prime divisors, then `y ≤ (2 ^ (l - 1)) ^ n`. Taking `y` to be the
qualifying neighbour of `x` bounds `x ^ 2` by an exponential, which `n!` eventually exceeds.

The prime-power bound adapts the `hfactor` argument in
`MathlibExt.NumberTheory.FactorialDivisorBound`, and the factorization `n! = m * (m + 2)`
with its two divisor witnesses adapts `MathlibExt.NumberTheory.BrocardRamanujanPowerFree`.

## References

* Abderrahim Makki Naciri, *On the Brocard–Ramanujan Equation with 7-Free Integers and Prime
  Powers*, INTEGERS 25 (2025), Article A71, pp. 1–8, Theorem 1(ii), first sentence.
  The proof uses the factorial valuation estimate from §2 in place of the real-power bound
  in Lemma 2, and factorial growth in place of Stirling's inequality.
* G. H. Hardy and E. M. Wright, *An Introduction to the Theory of Numbers*, 5th ed.,
  Oxford University Press, 1979 (Legendre's formula for factorial valuations, cited in §2).
-/

open Nat

namespace MetaMathlibExt

/-- A nonzero divisor of `n!` with at most `r` distinct prime factors is at most `(2 ^ r) ^ n`. -/
private theorem le_pow_of_dvd_factorial_of_primeFactors_card_le {n y r : ℕ}
    (hy : y ≠ 0) (hdvd : y ∣ n !) (hcard : y.primeFactors.card ≤ r) : y ≤ (2 ^ r) ^ n := by
  have hfactor (p : ℕ) (hp : p ∈ y.primeFactors) : p ^ y.factorization p ≤ 2 ^ n := by
    have hprime := prime_of_mem_primeFactors hp
    have hbase : p ≤ 2 ^ (p - 1) := by
      have := Nat.lt_two_pow_self (n := p - 1)
      have := hprime.two_le
      omega
    have hexp : (p - 1) * y.factorization p ≤ n := calc
      _ ≤ (p - 1) * (n !).factorization p := Nat.mul_le_mul_left _
        ((factorization_le_iff_dvd hy (factorial_ne_zero n)).2 hdvd p)
      _ ≤ n := (sub_one_mul_factorization_factorial hprime).trans_le (Nat.sub_le _ _)
    calc
      p ^ y.factorization p ≤ (2 ^ (p - 1)) ^ y.factorization p := Nat.pow_le_pow_left hbase _
      _ = 2 ^ ((p - 1) * y.factorization p) := (pow_mul _ _ _).symm
      _ ≤ 2 ^ n := Nat.pow_le_pow_right (by decide) hexp
  calc
    y = ∏ p ∈ y.primeFactors, p ^ y.factorization p := prod_primeFactors_pow_factorization hy
    _ ≤ ∏ _p ∈ y.primeFactors, 2 ^ n := Finset.prod_le_prod hfactor
    _ = (2 ^ y.primeFactors.card) ^ n := by rw [Finset.prod_const, pow_right_comm]
    _ ≤ (2 ^ r) ^ n := Nat.pow_le_pow_left (Nat.pow_le_pow_right (by decide) hcard) _

private theorem factorial_lt_of_fewPrimeFactors {n x l : ℕ} (hl : 2 ≤ l)
    (hsol : n ! + 1 = x ^ 2)
    (hfew : (x - 1).primeFactors.card < l ∨ (x + 1).primeFactors.card < l) :
    n ! < 4 * ((2 ^ (l - 1)) ^ 2) ^ n := by
  have hx : 1 < x := by
    by_contra! h
    obtain rfl | rfl : x = 0 ∨ x = 1 := by omega
    · simp at hsol
    · exact factorial_ne_zero n (by simpa using hsol)
  obtain ⟨m, rfl⟩ : ∃ m, x = m + 1 := ⟨x - 1, by omega⟩
  have hfac : n ! = m * (m + 2) := by
    have : n ! + 1 = m * (m + 2) + 1 := by rw [hsol]; ring
    omega
  obtain ⟨y, hy, hdvd, hxy, hcard⟩ :
      ∃ y : ℕ, y ≠ 0 ∧ y ∣ n ! ∧ m + 1 ≤ 2 * y ∧ y.primeFactors.card < l := by
    rcases hfew with h | h
    · rw [Nat.add_sub_cancel] at h
      exact ⟨m, by omega, hfac ▸ dvd_mul_right _ _, by omega, h⟩
    · exact ⟨m + 2, by omega, hfac ▸ dvd_mul_left _ _, by omega, h⟩
  have hyBound : y ≤ (2 ^ (l - 1)) ^ n :=
    le_pow_of_dvd_factorial_of_primeFactors_card_le hy hdvd
      ((Nat.le_sub_iff_add_le (Nat.le_of_succ_le hl)).2 hcard)
  calc
    n ! < (m + 1) ^ 2 := hsol ▸ Nat.lt_succ_self _
    _ ≤ (2 * (2 ^ (l - 1)) ^ n) ^ 2 :=
      Nat.pow_le_pow_left (hxy.trans (Nat.mul_le_mul_left 2 hyBound)) _
    _ = 4 * ((2 ^ (l - 1)) ^ 2) ^ n := by
      simp only [mul_pow, pow_right_comm (2 ^ (l - 1)) n 2, show (2 : ℕ) ^ 2 = 4 by decide]

/-- **Brocard–Ramanujan solutions with $x - 1$ or $x + 1$ having few prime factors are finite.**
For every natural number $l \ge 2$, there are only finitely many pairs of natural numbers
$(n, x)$ with $n! + 1 = x^2$ such that $x - 1$ or $x + 1$ has fewer than $l$ distinct prime
divisors.

Source: Abderrahim Makki Naciri, *On the Brocard-Ramanujan Equation with 7-Free
Integers and Prime Powers*, INTEGERS 25 (2025), Article A71, Theorem 1(ii), first
sentence (`integers-2025-A71-thm-1`). -/
public theorem brocardRamanujan_fewPrimeFactors_finite (l : ℕ) (hl : 2 ≤ l) :
    {p : ℕ × ℕ | p.1 ! + 1 = p.2 ^ 2 ∧
      ((p.2 - 1).primeFactors.card < l ∨ (p.2 + 1).primeFactors.card < l)}.Finite := by
  obtain ⟨N, hN⟩ := Filter.eventually_atTop.mp
    (Nat.eventually_mul_pow_lt_factorial_sub 4 ((2 ^ (l - 1)) ^ 2) 0)
  simp only [Nat.sub_zero] at hN
  refine ((Set.finite_Iio N).prod (Set.finite_Iic (N ! + 1))).subset ?_
  rintro ⟨n, x⟩ ⟨hsol, hfew⟩
  have hn : n < N := lt_of_not_ge fun hge ↦
    (not_le_of_gt (hN n hge)) (factorial_lt_of_fewPrimeFactors hl hsol hfew).le
  refine ⟨hn, ?_⟩
  change x ≤ N ! + 1
  calc
    x ≤ x ^ 2 := Nat.le_self_pow (by decide) x
    _ = n ! + 1 := hsol.symm
    _ ≤ N ! + 1 := Nat.add_le_add_right (Nat.factorial_le hn.le) _

end MetaMathlibExt
