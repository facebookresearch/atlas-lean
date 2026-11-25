/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Algebra.BigOperators.Group.Finset.Defs
public import Mathlib.Data.Nat.Nth
public import Mathlib.Data.Nat.PrimeFin
import Mathlib.Data.Nat.GCD.BigOperators
import Mathlib.Data.Nat.Prime.Nth
import Mathlib.NumberTheory.Multiplicity

/-!
# A prime divisor bound for power-of-two exponents

We prove the ramified bound and its weaker corollary for exponents `2 ^ a`.
For odd bases, lifting the exponent gives divisibility by `2 ^ (a + 2)`.
For even bases, all prime factors of `x ^ (2 ^ a) - 1` are odd.
-/

namespace MetaMathlibExt

open Finset

private theorem prod_first_primes_le (s : Finset ℕ) (hs : ∀ p ∈ s, Nat.Prime p) :
    ∏ i ∈ range s.card, Nat.nth Nat.Prime i ≤ ∏ p ∈ s, p := by
  induction s using Finset.induction_on_max with
  | empty => simp
  | insert p s hlt ih =>
    have hp := hs p (mem_insert_self p s)
    have hs' : ∀ q ∈ s, Nat.Prime q := forall_of_forall_insert hs
    have hcount : s.card ≤ Nat.count Nat.Prime p := by
      rw [Nat.count_eq_card_filter_range]
      exact card_le_card fun q hq ↦ mem_filter.mpr ⟨mem_range.mpr (hlt q hq), hs' q hq⟩
    have hnth := Nat.nth_monotone Nat.infinite_setOfPred_prime hcount
    rw [Nat.nth_count hp] at hnth
    have hps : p ∉ s := fun h ↦ (hlt p h).false
    rw [card_insert_of_notMem hps, prod_range_succ, prod_insert hps, mul_comm p]
    exact Nat.mul_le_mul (ih hs') hnth

/-- **The ramified bound for $n = 2^a$.** Let $a \ge 1$, let $n = 2^a$, let $x > 1$ be a natural
number, let $\omega_n$ be the number of distinct prime factors of $x^n - 1$, and let
$s_1 = 2 < s_2 = 3 < s_3 = 5 < \cdots$ be the primes in increasing order. Then
$$\min\Bigl(1 + 2n \prod_{i=1}^{\omega_n} s_i,\ 1 + \prod_{i=2}^{\omega_n + 1} s_i\Bigr) \le x^n.$$

Equivalently, $x$ is at least the smaller of the $n$-th roots of these two numbers, which is the
form of the source. The source admits every positive integer $x$; at $x = 1$ the number
$x^n - 1 = 0$ has an empty prime factorization, so $\omega_n = 0$ and the bound would read
$2 \le 1$.

Source: Gustav Kjærbye Bagger, *Hybrid Bounds for Prime Divisors*, INTEGERS 26 (2026),
Article A95, Theorem 3 (`integers-2026-A95-thm-3`). -/
public theorem two_pow_ramified_bound {a x : ℕ} (ha : 0 < a) (hx : 1 < x) :
    min (1 + 2 * 2 ^ a * ∏ i ∈ Finset.range (x ^ 2 ^ a - 1).primeFactors.card, Nat.nth Nat.Prime i)
        (1 + ∏ i ∈ Finset.range (x ^ 2 ^ a - 1).primeFactors.card, Nat.nth Nat.Prime (i + 1)) ≤
      x ^ 2 ^ a := by
  set m := x ^ 2 ^ a - 1
  have hn : (2 : ℕ) ^ a ≠ 0 := by positivity
  have hpow : 1 < x ^ 2 ^ a := one_lt_pow₀ hx hn
  have hm : 0 < m := Nat.sub_pos_of_lt hpow
  have hadd : 1 + m = x ^ 2 ^ a := by omega
  have hrad := Nat.prod_primeFactors_dvd m
  have hprimes : ∀ p ∈ m.primeFactors, Nat.Prime p := fun _ ↦ Nat.prime_of_mem_primeFactors
  rw [min_add_add_left, ← hadd, Nat.add_le_add_iff_left]
  by_cases h₂ : 2 ∈ m.primeFactors
  · apply (min_le_left _ _).trans
    refine (Nat.mul_le_mul_left _ (prod_first_primes_le _ hprimes)).trans (Nat.le_of_dvd hm ?_)
    have hodd : ¬ 2 ∣ x := by
      intro hx₂
      have hpow₂ := hx₂.trans (dvd_pow_self x hn)
      have hm₂ := Nat.dvd_of_mem_primeFactors h₂
      omega
    have heven : Even ((2 : ℕ) ^ a) := even_iff_two_dvd.mpr (dvd_pow_self 2 ha.ne')
    have hpowdvd : 2 ^ (a + 2) ∣ m := by
      apply (padicValNat_dvd_iff_le_of_ne_one (by decide) hm.ne').mpr
      simpa only [m, padicValNat_base_pow one_lt_two] using
        padicValNat.pow_two_sub_one_ge hx hodd hn heven
    let t := m.primeFactors.erase 2
    have hsplit : 2 * (∏ p ∈ t, p) = ∏ p ∈ m.primeFactors, p :=
      mul_prod_erase _ (fun p ↦ p) h₂
    have hcop : Nat.Coprime 2 (∏ p ∈ t, p) := by
      refine Nat.coprime_prod_right_iff.mpr fun p hp ↦ ?_
      exact (Nat.coprime_primes Nat.prime_two
        (Nat.prime_of_mem_primeFactors (mem_erase.mp hp).2)).mpr (mem_erase.mp hp).1.symm
    rw [← hsplit] at hrad ⊢
    rw [← mul_assoc, ← pow_succ', ← pow_succ]
    exact (hcop.pow_left _).mul_dvd_of_dvd_of_dvd hpowdvd
      ((dvd_mul_left _ _).trans hrad)
  · apply (min_le_right _ _).trans
    have h := prod_first_primes_le (insert 2 m.primeFactors) ((forall_mem_insert _ _ _).mpr
      ⟨Nat.prime_two, hprimes⟩)
    rw [card_insert_of_notMem h₂, prod_range_succ', Nat.nth_prime_zero_eq_two, prod_insert h₂,
      mul_comm 2] at h
    exact (Nat.le_of_mul_le_mul_right h (by decide)).trans (Nat.le_of_dvd hm hrad)

/-- **A weaker ramified bound for $n = 2^a$.** Let $a \ge 1$, let $n = 2^a$, let $x > 1$ be a
natural number, let $\omega_n$ be the number of distinct prime factors of $x^n - 1$, and let
$s_1 = 2 < s_2 = 3 < s_3 = 5 < \cdots$ be the primes in increasing order. Then
$$\min\Bigl(1 + n \prod_{i=1}^{\omega_n} s_i,\ 1 + \prod_{i=2}^{\omega_n + 1} s_i\Bigr) \le x^n.$$

This weakens the ramified bound for $n = 2^a$, which has the factor $2n$ in place of $n$. The
extracted text of the source reads $n = 2a$; its own discussion ($n = 4$, "extends to $n = 2^a$")
shows that $n = 2^a$ is meant. As in the stronger bound, $x > 1$ replaces the source's positive
integer $x$.

Source: Gustav Kjærbye Bagger, *Hybrid Bounds for Prime Divisors*, INTEGERS 26 (2026),
Article A95, Corollary 1 (`integers-2026-A95-cor-1`). -/
public theorem two_pow_trivial_ramified_bound {a x : ℕ} (ha : 0 < a) (hx : 1 < x) :
    min (1 + 2 ^ a * ∏ i ∈ Finset.range (x ^ 2 ^ a - 1).primeFactors.card, Nat.nth Nat.Prime i)
        (1 + ∏ i ∈ Finset.range (x ^ 2 ^ a - 1).primeFactors.card, Nat.nth Nat.Prime (i + 1)) ≤
      x ^ 2 ^ a := by
  apply le_trans _ (two_pow_ramified_bound ha hx)
  apply min_le_min_right
  rw [mul_assoc]
  exact Nat.add_le_add_left (Nat.le_mul_of_pos_left _ (by decide)) _

end MetaMathlibExt
