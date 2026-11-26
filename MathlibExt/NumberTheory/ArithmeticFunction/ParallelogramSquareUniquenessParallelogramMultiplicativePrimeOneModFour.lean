/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Basic.Complex.Basic
public import Mathlib.NumberTheory.ArithmeticFunction.Defs

import Mathlib.NumberTheory.SumTwoSquares
import Mathlib.Tactic.LinearCombination

/-!
# Parallelogram induction at primes congruent to one modulo four

A multiplicative arithmetic function satisfying the parallelogram identity takes the square
value at a prime congruent to one modulo four when it takes square values at all powers of
smaller primes.

Source: Poo-Sung Park, *On the Parallelogram Uniqueness of Square Numbers for Multiplicative
Functions*, INTEGERS 24 (2024), Article A108, Theorem 5.
-/

namespace MetaMathlibExt

open ArithmeticFunction

private lemma value_below_prime (f : ArithmeticFunction ℂ) (hf : f.IsMultiplicative)
    {p : ℕ}
    (hind : ∀ q s : ℕ, q.Prime → q < p → 1 ≤ s → f (q ^ s) = (q : ℂ) ^ (2 * s))
    (t : ℕ) (ht : t < p) : f t = (t : ℂ) ^ 2 := by
  induction t using Nat.recOnPosPrimePosCoprime with
  | prime_pow q s hq hs =>
    have hqp := (Nat.le_self_pow hs.ne' q).trans_lt ht
    rw [hind q s hq hqp hs, Nat.cast_pow, ← pow_mul]
    congr 1
    omega
  | zero => simp
  | one => simp [hf]
  | coprime a b ha hb hab iha ihb =>
    have ha' := (Nat.le_mul_of_pos_right a (by omega : 0 < b)).trans_lt ht
    have hb' := (Nat.le_mul_of_pos_left b (by omega : 0 < a)).trans_lt ht
    rw [hf.map_mul_of_coprime hab, iha ha', ihb hb', Nat.cast_mul, mul_pow]

private lemma ordered_sq_add_sq {p : ℕ} (hp : p.Prime) (hp4 : p % 4 = 1) :
    ∃ m n : ℕ, 0 < n ∧ n < m ∧ m ^ 2 + n ^ 2 = p := by
  let : Fact p.Prime := ⟨hp⟩
  obtain ⟨a, b, hsum⟩ := Nat.Prime.sq_add_sq (by omega : p % 4 ≠ 3)
  have ha : a ≠ 0 := by
    intro h
    have := hp.pow_eq_iff.mp (by simpa [h] using hsum : b ^ 2 = p)
    omega
  have hb : b ≠ 0 := by
    intro h
    have := hp.pow_eq_iff.mp (by simpa [h] using hsum : a ^ 2 = p)
    omega
  have hab : a ≠ b := by
    intro h
    have htwo : 2 ∣ p := ⟨a ^ 2, by nlinarith [hsum]⟩
    have := (hp.dvd_iff_eq (by decide : 2 ≠ 1)).mp htwo
    omega
  rcases lt_or_gt_of_ne hab with hab | hba
  · exact ⟨b, a, by omega, hab, by omega⟩
  · exact ⟨a, b, by omega, hba, hsum⟩

/-- **Parallelogram induction: primes congruent to 1 mod 4.**
Let $f$ be a complex-valued multiplicative arithmetic function
(so $f(0) = 0$) such that $f(m^2 + n^2) + f(m^2 - n^2) = 2f(m^2) + 2f(n^2)$ for all integers
$m > n \ge 1$.
Let $p$ be a prime such that $f(q^s) = q^{2s}$ for every prime $q < p$ and every integer
$s \ge 1$.
If $p \equiv 1 \pmod 4$, then $f(p) = p^2$.

Source: Poo-Sung Park, *On the Parallelogram Uniqueness of Square Numbers for Multiplicative
Functions*, INTEGERS 24 (2024), Article A108, Theorem 5 (`integers-2024-A108-thm-5`). -/
public theorem parallelogram_multiplicative_prime_one_mod_four (f : ArithmeticFunction ℂ)
    (hf : f.IsMultiplicative)
    (hpar : ∀ m n : ℕ, 0 < n → n < m →
      f (m ^ 2 + n ^ 2) + f (m ^ 2 - n ^ 2) = 2 * f (m ^ 2) + 2 * f (n ^ 2))
    {p : ℕ} (hp : p.Prime)
    (hind : ∀ q s : ℕ, q.Prime → q < p → 1 ≤ s → f (q ^ s) = (q : ℂ) ^ (2 * s))
    (hp4 : p % 4 = 1) :
    f p = (p : ℂ) ^ 2 := by
  obtain ⟨m, n, hn, hnm, hsum⟩ := ordered_sq_add_sq hp hp4
  have hn2 : 0 < n ^ 2 := Nat.pow_pos hn
  have hm2 : 0 < m ^ 2 := Nat.pow_pos (by omega : 0 < m)
  have hm_lt : m ^ 2 < p := by omega
  have hn_lt : n ^ 2 < p := by omega
  have hdiff_lt : m ^ 2 - n ^ 2 < p := (Nat.sub_le _ _).trans_lt hm_lt
  have hle : n ^ 2 ≤ m ^ 2 := Nat.pow_le_pow_left hnm.le 2
  have h := hpar m n hn hnm
  rw [hsum, value_below_prime f hf hind _ hdiff_lt,
    value_below_prime f hf hind _ hm_lt, value_below_prime f hf hind _ hn_lt] at h
  rw [Nat.cast_sub hle] at h
  have hsum_cast : (m : ℂ) ^ 2 + (n : ℂ) ^ 2 = (p : ℂ) := by
    exact_mod_cast hsum
  push_cast at h
  linear_combination h + ((m : ℂ) ^ 2 + (n : ℂ) ^ 2 + (p : ℂ)) * hsum_cast

end MetaMathlibExt
