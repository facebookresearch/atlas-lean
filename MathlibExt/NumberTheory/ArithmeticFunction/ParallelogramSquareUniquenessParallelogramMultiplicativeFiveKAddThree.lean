/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Basic.Complex.Basic
public import Mathlib.NumberTheory.ArithmeticFunction.Defs
import Mathlib.Tactic.LinearCombination

/-!
# The parallelogram identity at five times k plus three

A multiplicative arithmetic function satisfying the parallelogram identity takes the square
value at `5 * k + 3` under induction on prime powers below a prime `p = 4 * k - 1`,
when `19 ≤ p` and `¬ 4 ∣ k`.

Source: Poo-Sung Park, *On the Parallelogram Uniqueness of Square Numbers for Multiplicative
Functions*, INTEGERS 24 (2024), Article A108, Lemma 4.
-/

namespace MetaMathlibExt

open ArithmeticFunction

private lemma value_of_prime_divisors (f : ArithmeticFunction ℂ)
    (hf : f.IsMultiplicative) {p : ℕ}
    (hind : ∀ q s : ℕ, q.Prime → q < p → 1 ≤ s → f (q ^ s) = (q : ℂ) ^ (2 * s))
    (n : ℕ) (hn : ∀ q : ℕ, q.Prime → q ∣ n → q < p) :
    f n = (n : ℂ) ^ 2 := by
  induction n using Nat.recOnPosPrimePosCoprime with
  | zero => simp
  | one => simp [hf]
  | prime_pow q s hq hs =>
    rw [hind q s hq (hn q hq (dvd_pow_self q hs.ne')) hs, Nat.cast_pow, ← pow_mul]
    congr 1
    omega
  | coprime a b ha hb hab iha ihb =>
    rw [hf.map_mul_of_coprime hab,
      iha (fun q hq hqa => hn q hq (dvd_mul_of_dvd_left hqa b)),
      ihb (fun q hq hqb => hn q hq (dvd_mul_of_dvd_right hqb a)), Nat.cast_mul, mul_pow]

private lemma value_below (f : ArithmeticFunction ℂ)
    (hf : f.IsMultiplicative) {p : ℕ}
    (hind : ∀ q s : ℕ, q.Prime → q < p → 1 ≤ s → f (q ^ s) = (q : ℂ) ^ (2 * s))
    (n : ℕ) (hn : n < p) : f n = (n : ℂ) ^ 2 := by
  by_cases hn0 : n = 0
  · subst n
    simp
  exact value_of_prime_divisors f hf hind n
    (fun q _ hq => (Nat.le_of_dvd (by omega) hq).trans_lt hn)

private lemma square_below (f : ArithmeticFunction ℂ)
    (hf : f.IsMultiplicative) {p : ℕ}
    (hind : ∀ q s : ℕ, q.Prime → q < p → 1 ≤ s → f (q ^ s) = (q : ℂ) ^ (2 * s))
    (n : ℕ) (hn : n < p) : f (n ^ 2) = (n : ℂ) ^ 4 := by
  by_cases hn0 : n = 0
  · subst n
    simp
  have h := value_of_prime_divisors f hf hind (n ^ 2)
    (fun q hq hqd => (Nat.le_of_dvd (by omega) (hq.dvd_of_dvd_pow hqd)).trans_lt hn)
  simpa [Nat.cast_pow, ← pow_mul] using h

private lemma value_composite (f : ArithmeticFunction ℂ)
    (hf : f.IsMultiplicative) {p : ℕ}
    (hind : ∀ q s : ℕ, q.Prime → q < p → 1 ≤ s → f (q ^ s) = (q : ℂ) ^ (2 * s))
    (n : ℕ) (hn : n < 2 * p) (hprime : ¬ n.Prime) : f n = (n : ℂ) ^ 2 := by
  by_cases hn0 : n = 0
  · subst n
    simp
  apply value_of_prime_divisors f hf hind n
  intro q hq hqd
  obtain ⟨b, hb⟩ := hqd
  have hb2 : 2 ≤ b := by
    by_contra hb2
    have hb01 : b = 0 ∨ b = 1 := by omega
    rcases hb01 with hb0 | hb1
    · simp only [hb0, Nat.mul_zero] at hb
      exact hn0 hb
    · simp only [hb1, Nat.mul_one] at hb
      exact hprime (hb ▸ hq)
  nlinarith

/-- **Parallelogram induction: the value at 5k + 3.**
Let $f$ be a complex-valued multiplicative arithmetic function
(so $f(0) = 0$) such that $f(m^2 + n^2) + f(m^2 - n^2) = 2f(m^2) + 2f(n^2)$ for all integers
$m > n \ge 1$.
Let $p$ be a prime such that $f(q^s) = q^{2s}$ for every prime $q < p$ and every integer
$s \ge 1$.
If $p = 4k - 1$ for a natural number $k$ with $4 \nmid k$, and $p \ge 19$, then
$f(5k + 3) = (5k + 3)^2$.

Source: Poo-Sung Park, *On the Parallelogram Uniqueness of Square Numbers for Multiplicative
Functions*, INTEGERS 24 (2024), Article A108, Lemma 4 (`integers-2024-A108-lem-4`). -/
public theorem parallelogram_multiplicative_five_k_add_three (f : ArithmeticFunction ℂ)
    (hf : f.IsMultiplicative)
    (hpar : ∀ m n : ℕ, 0 < n → n < m →
      f (m ^ 2 + n ^ 2) + f (m ^ 2 - n ^ 2) = 2 * f (m ^ 2) + 2 * f (n ^ 2))
    {p : ℕ} (hp : p.Prime)
    (hind : ∀ q s : ℕ, q.Prime → q < p → 1 ≤ s → f (q ^ s) = (q : ℂ) ^ (2 * s))
    {k : ℕ} (hpk : p = 4 * k - 1) (h19 : 19 ≤ p) (hk : ¬ 4 ∣ k) :
    f (5 * k + 3) = ((5 * k + 3 : ℕ) : ℂ) ^ 2 := by
  have hk5 : 5 ≤ k := by
    have hp2 := hp.two_le
    omega
  by_cases hN : (5 * k + 3).Prime
  · obtain ⟨u, hu⟩ := hN.odd_of_ne_two (by omega)
    have hkm : k % 4 = 2 := by
      have hmod := Nat.mod_lt k (by decide : 0 < 4)
      have hnot : k % 4 ≠ 0 := by simpa [Nat.dvd_iff_mod_eq_zero] using hk
      omega
    obtain ⟨t, ht⟩ : ∃ t : ℕ, k = 4 * t + 2 := ⟨k / 4, by omega⟩
    subst k
    have ht1 : 1 ≤ t := by omega
    have hpval : p = 16 * t + 7 := by omega
    have hdiff : (15 * t + 6) ^ 2 - (5 * t + 7) ^ 2 =
        (10 * t - 1) * (5 * (4 * t + 2) + 3) := by
      apply Nat.sub_eq_of_eq_add
      have hsub : 10 * t - 1 + 1 = 10 * t := by omega
      nlinarith
    have hsum : (15 * t + 6) ^ 2 + (5 * t + 7) ^ 2 =
        5 * ((5 * t + 4) ^ 2 + (5 * t + 1) ^ 2) := by ring
    have hdiff' : (5 * t + 4) ^ 2 - (5 * t + 1) ^ 2 =
        3 * (10 * t + 5) := by
      apply Nat.sub_eq_of_eq_add
      ring
    have hcop5 : Nat.Coprime 5 ((5 * t + 4) ^ 2 + (5 * t + 1) ^ 2) := by
      apply Nat.prime_five.coprime_iff_not_dvd.mpr
      rw [Nat.dvd_iff_mod_eq_zero]
      simp [Nat.add_mod, Nat.pow_mod]
    have hcop3 : Nat.Coprime 3 (10 * t + 5) := by
      apply Nat.prime_three.coprime_iff_not_dvd.mpr
      intro hdiv
      have hdivN : 3 ∣ 5 * (4 * t + 2) + 3 := by
        rw [Nat.dvd_iff_mod_eq_zero] at hdiv ⊢
        omega
      have h3 := (Nat.prime_dvd_prime_iff_eq Nat.prime_three hN).mp hdivN
      omega
    have hcopN : Nat.Coprime (10 * t - 1) (5 * (4 * t + 2) + 3) := by
      exact (Nat.coprime_of_lt_prime (by omega) (by omega) hN).symm
    have heq := hpar (5 * t + 4) (5 * t + 1) (by omega) (by omega)
    rw [hdiff', hf.map_mul_of_coprime hcop3,
      value_below f hf hind 3 (by omega),
      value_below f hf hind (10 * t + 5) (by omega),
      square_below f hf hind (5 * t + 4) (by omega),
      square_below f hf hind (5 * t + 1) (by omega)] at heq
    have heq' := hpar (15 * t + 6) (5 * t + 7) (by omega) (by omega)
    rw [hdiff, hsum, hf.map_mul_of_coprime hcop5,
      value_below f hf hind 5 (by omega), hf.map_mul_of_coprime hcopN,
      value_below f hf hind (10 * t - 1) (by omega),
      square_below f hf hind (15 * t + 6) (by omega),
      square_below f hf hind (5 * t + 7) (by omega)] at heq'
    have hcast : ((10 * t - 1 : ℕ) : ℂ) = 10 * (t : ℂ) - 1 := by
      rw [Nat.cast_sub (by omega)]
      push_cast
      rfl
    rw [hcast] at heq'
    push_cast at heq heq' ⊢
    have hzero : (10 * (t : ℂ) - 1) ^ 2 *
        (f (5 * (4 * t + 2) + 3) - (5 * (4 * (t : ℂ) + 2) + 3) ^ 2) = 0 := by
      linear_combination heq' - 25 * heq
    have hnz : (10 * (t : ℂ) - 1) ^ 2 ≠ 0 := by
      exact pow_ne_zero 2 (by exact_mod_cast (show (10 * t : ℤ) - 1 ≠ 0 by omega))
    exact sub_eq_zero.mp ((mul_eq_zero.mp hzero).resolve_left hnz)
  · exact value_composite f hf hind (5 * k + 3) (by omega) hN

end MetaMathlibExt
