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
import Mathlib.Data.Nat.Prime.Nth
import Mathlib.FieldTheory.Finite.Basic

/-!
# A prime divisor bound for power-of-two exponents

For odd bases, Euler's theorem modulo `2 ^ (a + 1)` accounts for the extra copies of `2`.
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
  set m := x ^ 2 ^ a - 1
  have hpow : 1 < x ^ 2 ^ a := hx.trans (lt_self_pow₀ hx (one_lt_pow₀ one_lt_two ha.ne'))
  have hm : 0 < m := Nat.sub_pos_of_lt hpow
  have hadd : 1 + m = x ^ 2 ^ a := by omega
  have hrad := Nat.prod_primeFactors_dvd m
  have hprimes : ∀ p ∈ m.primeFactors, Nat.Prime p := fun _ ↦ Nat.prime_of_mem_primeFactors
  rw [min_add_add_left, ← hadd, Nat.add_le_add_iff_left]
  by_cases h₂ : 2 ∈ m.primeFactors
  · apply (min_le_left _ _).trans
    refine (Nat.mul_le_mul_left _ (prod_first_primes_le _ hprimes)).trans (Nat.le_of_dvd hm ?_)
    have hodd : Odd x := by
      have hd := Nat.dvd_of_mem_primeFactors h₂
      apply (Nat.odd_pow_iff (e := 2 ^ a) (by positivity)).mp
      rw [Nat.odd_iff]
      omega
    have hpowdvd : 2 ^ (a + 1) ∣ m := by
      simpa [m, Nat.totient_prime_pow_succ Nat.prime_two] using
        (Nat.ModEq.pow_totient (hodd.coprime_two_right.pow_right (a + 1))).symm.dvd'
    let t := m.primeFactors.erase 2
    have hsplit : 2 * (∏ p ∈ t, p) = ∏ p ∈ m.primeFactors, p :=
      mul_prod_erase _ (fun p ↦ p) h₂
    have hcop : Nat.Coprime 2 (∏ p ∈ t, p) := by
      refine Nat.coprime_prod_right_iff.mpr fun p hp ↦ ?_
      exact (Nat.coprime_primes Nat.prime_two
        (Nat.prime_of_mem_primeFactors (mem_erase.mp hp).2)).mpr (mem_erase.mp hp).1.symm
    rw [← hsplit] at hrad ⊢
    rw [← mul_assoc, ← pow_succ]
    exact (hcop.pow_left _).mul_dvd_of_dvd_of_dvd hpowdvd
      ((dvd_mul_left _ _).trans hrad)
  · apply (min_le_right _ _).trans
    have h := prod_first_primes_le (insert 2 m.primeFactors) ((forall_mem_insert _ _ _).mpr
      ⟨Nat.prime_two, hprimes⟩)
    rw [card_insert_of_notMem h₂, prod_range_succ', Nat.nth_prime_zero_eq_two, prod_insert h₂,
      mul_comm 2] at h
    exact (Nat.le_of_mul_le_mul_right h (by decide)).trans (Nat.le_of_dvd hm hrad)

end MetaMathlibExt
