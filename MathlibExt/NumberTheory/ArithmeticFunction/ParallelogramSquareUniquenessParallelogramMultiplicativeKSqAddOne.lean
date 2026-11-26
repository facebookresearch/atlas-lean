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

/-!
# Parallelogram induction: the values at `k ^ 2 + 1` and `4 * k ^ 2 + 1`

A complex-valued multiplicative arithmetic function satisfying the parallelogram identity on
squares takes square values at `k ^ 2 + 1` and `4 * k ^ 2 + 1` when it takes square values at
all prime powers below the prime `4 * k - 1`.

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
      have h1 : f 1 = 1 := hf.map_one
      have hf2 : f 2 = (2 : ℂ) ^ 2 := by
        simpa using hind 2 1 Nat.prime_two (by decide) (by decide)
      have h4r : f 4 = (2 : ℂ) ^ 4 := by
        simpa using hind 2 2 Nat.prime_two (by decide) (by decide)
      have h8r : f 8 = (2 : ℂ) ^ 6 := by
        simpa using hind 2 3 Nat.prime_two (by decide) (by decide)
      have h16r : f 16 = (2 : ℂ) ^ 8 := by
        simpa using hind 2 4 Nat.prime_two (by decide) (by decide)
      have hf10 : f 10 = f 2 * f 5 := hf.map_mul_of_coprime (m := 2) (n := 5) (by decide)
      have hf15 : f 15 = f 3 * f 5 := hf.map_mul_of_coprime (m := 3) (n := 5) (by decide)
      have hf26 : f 26 = f 2 * f 13 := hf.map_mul_of_coprime (m := 2) (n := 13) (by decide)
      have hf24 : f 24 = f 8 * f 3 := hf.map_mul_of_coprime (m := 8) (n := 3) (by decide)
      have hf34 : f 34 = f 2 * f 17 := hf.map_mul_of_coprime (m := 2) (n := 17) (by decide)
      have hf21 : f 21 = f 3 * f 7 := hf.map_mul_of_coprime (m := 3) (n := 7) (by decide)
      have hf50 : f 50 = f 2 * f 25 := hf.map_mul_of_coprime (m := 2) (n := 25) (by decide)
      have hf48 : f 48 = f 16 * f 3 := hf.map_mul_of_coprime (m := 16) (n := 3) (by decide)
      have hf58 : f 58 = f 2 * f 29 := hf.map_mul_of_coprime (m := 2) (n := 29) (by decide)
      have hf40 : f 40 = f 8 * f 5 := hf.map_mul_of_coprime (m := 8) (n := 5) (by decide)
      have eA : f 5 + f 3 = 2 * f 4 + 2 * f 1 := by
        simpa using hpar 2 1 (by decide) (by decide)
      rw [h1, h4r] at eA
      have h3 : f 3 = 34 - f 5 := by linear_combination eA
      have eB : f 10 + f 8 = 2 * f 9 + 2 * f 1 := by
        simpa using hpar 3 1 (by decide) (by decide)
      rw [hf10, hf2, h8r, h1] at eB
      have h9 : f 9 = 2 * f 5 + 31 := by linear_combination -eB / 2
      have e32 : f 13 + f 5 = 2 * f 9 + 2 * f 4 := by
        simpa using hpar 3 2 (by decide) (by decide)
      rw [h9, h4r] at e32
      have h13 : f 13 = 3 * f 5 + 94 := by linear_combination e32
      have eC : f 17 + f 15 = 2 * f 16 + 2 * f 1 := by
        simpa using hpar 4 1 (by decide) (by decide)
      rw [hf15, h3, h16r, h1] at eC
      have h17 : f 17 = 514 - 34 * f 5 + (f 5) ^ 2 := by linear_combination eC
      have eH : f 34 + f 16 = 2 * f 25 + 2 * f 9 := by
        simpa using hpar 5 3 (by decide) (by decide)
      rw [hf34, hf2, h16r, h9, h17] at eH
      have h25 : f 25 = 1125 - 70 * f 5 + 2 * (f 5) ^ 2 := by linear_combination -eH / 2
      have eF : f 26 + f 24 = 2 * f 25 + 2 * f 1 := by
        simpa using hpar 5 1 (by decide) (by decide)
      rw [hf26, hf24, hf2, h8r, h3, h13, h25, h1] at eF
      have hquad : (f 5) ^ 2 - 22 * f 5 - 75 = 0 := by linear_combination -eF / 4
      have eD : f 25 + f 7 = 2 * f 16 + 2 * f 9 := by
        simpa using hpar 4 3 (by decide) (by decide)
      rw [h25, h16r, h9] at eD
      have h7 : f 7 = -551 + 74 * f 5 - 2 * (f 5) ^ 2 := by linear_combination eD
      have eG : f 29 + f 21 = 2 * f 25 + 2 * f 4 := by
        simpa using hpar 5 2 (by decide) (by decide)
      rw [hf21, h3, h25, h7, h4r] at eG
      have h29 : f 29 = 21016 - 3207 * f 5 + 146 * (f 5) ^ 2 - 2 * (f 5) ^ 3 := by
        linear_combination eG
      have e71 : f 50 + f 48 = 2 * f 49 + 2 * f 1 := by
        simpa using hpar 7 1 (by decide) (by decide)
      rw [hf50, hf48, hf2, h16r, h3, h25, h1] at e71
      have h49 : f 49 = 6601 - 268 * f 5 + 4 * (f 5) ^ 2 := by linear_combination -e71 / 2
      have e73 : f 58 + f 40 = 2 * f 49 + 2 * f 9 := by
        simpa using hpar 7 3 (by decide) (by decide)
      rw [hf58, hf40, hf2, h8r, h29, h49, h9] at e73
      have hcub : (f 5) ^ 3 - 72 * (f 5) ^ 2 + 1529 * f 5 - 8850 = 0 := by
        linear_combination -e73 / 8
      have hfin : 504 * (f 5 - 25) = 0 := by linear_combination hcub - (f 5 - 50) * hquad
      have hne : (504 : ℂ) ≠ 0 := by norm_num
      have h5sub : f 5 - 25 = 0 := (mul_eq_zero.mp hfin).resolve_left hne
      have h5eq : f 5 = 25 := sub_eq_zero.mp h5sub
      refine ⟨?_, ?_⟩
      · simpa using hf2
      · rw [h5eq]
        norm_num
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
