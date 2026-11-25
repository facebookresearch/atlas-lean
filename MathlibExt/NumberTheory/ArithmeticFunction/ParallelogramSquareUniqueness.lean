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
# The parallelogram identity at an odd prime square plus one

A multiplicative function satisfying the parallelogram identity on squares takes the square
value at `p ^ 2 + 1` if it takes square values at the odd prime `p` and at powers of smaller primes.
-/

namespace MetaMathlibExt

open ArithmeticFunction

/-- **Parallelogram induction: the value at p² + 1.**
Let $f$ be a complex-valued multiplicative arithmetic function
(so $f(0) = 0$) such that $f(m^2 + n^2) + f(m^2 - n^2) = 2f(m^2) + 2f(n^2)$ for all integers
$m > n \ge 1$.
Let $p$ be a prime such that $f(q^s) = q^{2s}$ for every prime $q < p$ and every integer
$s \ge 1$.
If $p$ is odd and $f(p) = p^2$, then $f(p^2 + 1) = (p^2 + 1)^2$.

The hypothesis $p \ne 2$ is needed: the function with $f(n) = 0$ if $4 \mid n$, $f(n) = 4$ if
$n \equiv 2 \pmod 4$ and $f(n) = 1$ otherwise satisfies the hypotheses for $p = 2$, but
$f(5) = 1$.

Source: Poo-Sung Park, *On the Parallelogram Uniqueness of Square Numbers for Multiplicative
Functions*, INTEGERS 24 (2024), Article A108, Lemma 1 (`integers-2024-A108-lem-1`). -/
public theorem parallelogram_multiplicative_sq_add_one (f : ArithmeticFunction ℂ)
    (hf : f.IsMultiplicative)
    (hpar : ∀ m n : ℕ, 0 < n → n < m →
      f (m ^ 2 + n ^ 2) + f (m ^ 2 - n ^ 2) = 2 * f (m ^ 2) + 2 * f (n ^ 2))
    {p : ℕ} (hp : p.Prime)
    (hind : ∀ q s : ℕ, q.Prime → q < p → 1 ≤ s → f (q ^ s) = (q : ℂ) ^ (2 * s))
    (hp2 : p ≠ 2) (hfp : f p = (p : ℂ) ^ 2) :
    f (p ^ 2 + 1) = ((p ^ 2 + 1 : ℕ) : ℂ) ^ 2 := by
  -- Extend the prime-power hypothesis to squares with base below p.
  have hsq (n : ℕ) : n < p → f (n ^ 2) = (n : ℂ) ^ 4 := by
    induction n using Nat.recOnPosPrimePosCoprime with
    | prime_pow q s hq hs =>
      intro hlt
      have hqp := (Nat.le_self_pow hs.ne' q).trans_lt hlt
      rw [← pow_mul, hind q (s * 2) hq hqp (by omega), Nat.cast_pow, ← pow_mul]
      congr 1
      omega
    | zero => simp
    | one => simp [hf]
    | coprime a b ha hb hab iha ihb =>
      intro hlt
      have ha' := (Nat.le_mul_of_pos_right a (by omega : 0 < b)).trans_lt hlt
      have hb' := (Nat.le_mul_of_pos_left b (by omega : 0 < a)).trans_lt hlt
      rw [mul_pow, hf.map_mul_of_coprime (hab.pow 2 2), iha ha', ihb hb', Nat.cast_mul, mul_pow]
  obtain ⟨k, hpk⟩ := hp.odd_of_ne_two hp2
  have hpgt := hp.two_le
  have hk : 0 < k := by omega
  have hf2 : f 2 = (2 : ℂ) ^ 2 := by
    simpa using hind 2 1 Nat.prime_two (by omega) (by decide)
  -- The difference of the consecutive squares is p, and their sum is odd.
  have hdiff : (k + 1) ^ 2 - k ^ 2 = p := by
    apply Nat.sub_eq_of_eq_add
    rw [hpk]
    ring
  have hsum := hpar (k + 1) k hk (Nat.lt_succ_self k)
  rw [hdiff, hfp, hsq (k + 1) (by omega), hsq k (by omega)] at hsum
  have hcop : Nat.Coprime 2 ((k + 1) ^ 2 + k ^ 2) :=
    Nat.coprime_two_left.mpr ⟨k ^ 2 + k, by ring⟩
  have hfactor : p ^ 2 + 1 = 2 * ((k + 1) ^ 2 + k ^ 2) := by
    rw [hpk]
    ring
  rw [hfactor, hf.map_mul_of_coprime hcop, hf2]
  rw [hpk] at hsum
  push_cast at hsum ⊢
  linear_combination 4 * hsum

end MetaMathlibExt
