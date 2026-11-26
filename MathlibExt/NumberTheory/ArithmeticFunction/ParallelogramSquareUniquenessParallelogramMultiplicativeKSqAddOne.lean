/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Basic.Complex.Basic
public import Mathlib.NumberTheory.ArithmeticFunction.Defs
import Mathlib.Data.Nat.Factorization.Induction
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.NormNum
import MathlibExt.NumberTheory.ArithmeticFunction.ParallelogramSquareUniqueness

/-!
# Parallelogram induction: the values at `k ^ 2 + 1` and `4 * k ^ 2 + 1`

A complex-valued multiplicative arithmetic function satisfying the parallelogram identity on
squares takes square values at `k ^ 2 + 1` and `4 * k ^ 2 + 1` when it takes square values at
every positive power of every prime less than `4 * k - 1`.

Statement from Poo-Sung Park, *On the Parallelogram Uniqueness of Square Numbers for
Multiplicative Functions*, INTEGERS 24 (2024), Article A108, Lemma 3. Multiplicative functions
are `ArithmeticFunction ℂ` with `IsMultiplicative`.
-/

namespace MetaMathlibExt

open ArithmeticFunction

/-- Values at numbers whose prime factors are all below `p` are squares. -/
private theorem aux_sq_of_small_prime_factors (f : ArithmeticFunction ℂ)
    (hf : f.IsMultiplicative)
    {p : ℕ} (hp : p.Prime)
    (hind : ∀ q s : ℕ, q.Prime → q < p → 1 ≤ s → f (q ^ s) = (q : ℂ) ^ (2 * s))
    (n : ℕ) (hall : ∀ q : ℕ, q.Prime → q ∣ n → q < p) :
    f n = (n : ℂ) ^ 2 := by
  induction n using Nat.recOnPosPrimePosCoprime with
  | prime_pow q s hq hs =>
    have hs0 : s ≠ 0 := by omega
    have hqp : q < p := hall q hq (dvd_pow_self q hs0)
    rw [hind q s hq hqp (by omega), Nat.cast_pow, ← pow_mul]
    congr 1
    omega
  | zero =>
    exact absurd (hall p hp (dvd_zero p)) (by omega)
  | one =>
    simp [hf]
  | coprime a b _ _ hab iha ihb =>
    have ha' : ∀ q : ℕ, q.Prime → q ∣ a → q < p :=
      fun q hq hqa => hall q hq (hqa.trans (dvd_mul_right a b))
    have hb' : ∀ q : ℕ, q.Prime → q ∣ b → q < p :=
      fun q hq hqb => hall q hq (hqb.trans (dvd_mul_left b a))
    rw [hf.map_mul_of_coprime hab, iha ha', ihb hb', Nat.cast_mul, mul_pow]

/-- **Parallelogram induction: the values at k² + 1 and 4k² + 1.**
Let $f$ be a complex-valued multiplicative arithmetic function
(so $f(0) = 0$) such that $f(m^2 + n^2) + f(m^2 - n^2) = 2f(m^2) + 2f(n^2)$ for all integers
$m > n \ge 1$.
Let $p$ be a prime such that $f(q^s) = q^{2s}$ for every prime $q < p$ and every integer
$s \ge 1$.
If $p = 4k - 1$ for a natural number $k$, then $f(k^2 + 1) = (k^2 + 1)^2$ and
$f(4k^2 + 1) = (4k^2 + 1)^2$.

Source: Poo-Sung Park, *On the Parallelogram Uniqueness of Square Numbers for Multiplicative
Functions*, INTEGERS 24 (2024), Article A108, Lemma 3 (`integers-2024-A108-lem-3`). -/
public theorem parallelogram_multiplicative_k_sq_add_one (f : ArithmeticFunction ℂ)
    (hf : f.IsMultiplicative)
    (hpar : ∀ m n : ℕ, 0 < n → n < m →
      f (m ^ 2 + n ^ 2) + f (m ^ 2 - n ^ 2) = 2 * f (m ^ 2) + 2 * f (n ^ 2))
    {p : ℕ} (hp : p.Prime)
    (hind : ∀ q s : ℕ, q.Prime → q < p → 1 ≤ s → f (q ^ s) = (q : ℂ) ^ (2 * s))
    {k : ℕ} (hpk : p = 4 * k - 1) :
    f (k ^ 2 + 1) = ((k ^ 2 + 1 : ℕ) : ℂ) ^ 2 ∧
      f (4 * k ^ 2 + 1) = ((4 * k ^ 2 + 1 : ℕ) : ℂ) ^ 2 := by
  rcases lt_or_ge k 2 with hk | hk
  · have hk01 : k = 0 ∨ k = 1 := by omega
    rcases hk01 with rfl | rfl
    · norm_num at hpk
      subst hpk
      exact absurd hp (by decide)
    · norm_num at hpk
      subst hpk
      have e1 : (1 : ℕ) ^ 2 + 1 = 2 := by norm_num
      have e2 : 4 * (1 : ℕ) ^ 2 + 1 = 5 := by norm_num
      rw [e1, e2]
      have hf2 : f 2 = (2 : ℂ) ^ 2 := by
        simpa using hind 2 1 Nat.prime_two (by decide) (by decide)
      have hf5 := (parallelogram_multiplicative_add_two f hf hpar hp hind (by decide)).1
      refine ⟨?_, ?_⟩
      · simpa using hf2
      · simpa using hf5
  · obtain ⟨j, rfl⟩ := Nat.exists_eq_add_of_le (show 1 ≤ k by omega)
    have h1k : 1 < 1 + j := by omega
    have hsum1 := hpar (1 + j) 1 zero_lt_one h1k
    simp only [one_pow] at hsum1
    have hfactor : (1 + j) ^ 2 - 1 = (1 + j + 1) * (1 + j - 1) := by
      have h := Nat.sq_sub_sq (1 + j) 1
      simpa using h
    have hkm1 : f ((1 + j) ^ 2 - 1) = (((1 + j) ^ 2 - 1 : ℕ) : ℂ) ^ 2 := by
      apply aux_sq_of_small_prime_factors f hf hp hind
      intro q hq hdiv
      rw [hfactor] at hdiv
      rcases (hq.dvd_mul.mp hdiv) with h | h
      · have hle : q ≤ 1 + j + 1 := Nat.le_of_dvd (by omega) h
        omega
      · have hle : q ≤ 1 + j - 1 := Nat.le_of_dvd (by omega) h
        omega
    have hksq : f ((1 + j) ^ 2) = ((((1 + j) ^ 2 : ℕ)) : ℂ) ^ 2 := by
      apply aux_sq_of_small_prime_factors f hf hp hind
      intro q hq hdiv
      have hqk : q ∣ 1 + j := hq.dvd_of_dvd_pow hdiv
      have hle : q ≤ 1 + j := Nat.le_of_dvd (by omega) hqk
      omega
    rw [hkm1, hksq, hf.map_one] at hsum1
    have hle1 : 1 ≤ (1 + j) ^ 2 := Nat.one_le_pow 2 (1 + j) (by omega)
    rw [Nat.cast_sub hle1] at hsum1
    have claim1 : f ((1 + j) ^ 2 + 1) = ((((1 + j) ^ 2 + 1 : ℕ)) : ℂ) ^ 2 := by
      push_cast at hsum1 ⊢
      linear_combination hsum1
    have e : 2 * (1 + j) - 1 = 2 * j + 1 := by omega
    have h2k1 : 0 < 2 * (1 + j) - 1 := by omega
    have h2klt : 2 * (1 + j) - 1 < 2 * (1 + j) + 1 := by omega
    have hsum2 := hpar (2 * (1 + j) + 1) (2 * (1 + j) - 1) h2k1 h2klt
    rw [e] at hsum2
    have hfactor2 : (2 * (1 + j) + 1) ^ 2 + (2 * j + 1) ^ 2 = 2 * (4 * (1 + j) ^ 2 + 1) := by ring
    have hdiff2 : (2 * (1 + j) + 1) ^ 2 - (2 * j + 1) ^ 2 = 8 * (1 + j) := by
      apply Nat.sub_eq_of_eq_add
      ring
    rw [hfactor2, hdiff2] at hsum2
    have hcop2 : Nat.Coprime 2 (4 * (1 + j) ^ 2 + 1) :=
      Nat.coprime_two_left.mpr ⟨2 * (1 + j) ^ 2, by ring⟩
    have hf2 : f 2 = (2 : ℂ) ^ 2 := by
      simpa using hind 2 1 Nat.prime_two (by omega) (by decide)
    rw [hf.map_mul_of_coprime hcop2, hf2] at hsum2
    have h8k : f (8 * (1 + j)) = ((8 * (1 + j) : ℕ) : ℂ) ^ 2 := by
      apply aux_sq_of_small_prime_factors f hf hp hind
      intro q hq hdiv
      have h8eq : (8 : ℕ) = 2 ^ 3 := by norm_num
      rw [h8eq] at hdiv
      rcases (hq.dvd_mul.mp hdiv) with h | h
      · have hq2 : q ∣ 2 := hq.dvd_of_dvd_pow h
        have hle : q ≤ 2 := Nat.le_of_dvd (by omega) hq2
        omega
      · have hle : q ≤ 1 + j := Nat.le_of_dvd (by omega) h
        omega
    have hsq2a : f ((2 * (1 + j) + 1) ^ 2) = ((((2 * (1 + j) + 1) ^ 2 : ℕ)) : ℂ) ^ 2 := by
      apply aux_sq_of_small_prime_factors f hf hp hind
      intro q hq hdiv
      have hqd : q ∣ 2 * (1 + j) + 1 := hq.dvd_of_dvd_pow hdiv
      have hle : q ≤ 2 * (1 + j) + 1 := Nat.le_of_dvd (by omega) hqd
      omega
    have hsq2b : f ((2 * j + 1) ^ 2) = ((((2 * j + 1) ^ 2 : ℕ)) : ℂ) ^ 2 := by
      apply aux_sq_of_small_prime_factors f hf hp hind
      intro q hq hdiv
      have hqd : q ∣ 2 * j + 1 := hq.dvd_of_dvd_pow hdiv
      have hle : q ≤ 2 * j + 1 := Nat.le_of_dvd (by omega) hqd
      omega
    rw [h8k, hsq2a, hsq2b] at hsum2
    have claim2 : f (4 * (1 + j) ^ 2 + 1) = ((4 * (1 + j) ^ 2 + 1 : ℕ) : ℂ) ^ 2 := by
      push_cast at hsum2 ⊢
      linear_combination hsum2 / 4
    exact ⟨claim1, claim2⟩

end MetaMathlibExt
