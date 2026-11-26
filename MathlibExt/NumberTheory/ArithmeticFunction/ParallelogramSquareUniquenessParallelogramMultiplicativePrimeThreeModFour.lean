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
# Parallelogram induction at primes congruent to three modulo four

We prove the square value at a prime `p = 4 * k - 1` with `19 ≤ p`, assuming square values
at every power of a smaller prime and the parallelogram identity on squares.

Source: Poo-Sung Park, *On the Parallelogram Uniqueness of Square Numbers for Multiplicative
Functions*, INTEGERS 24 (2024), Article A108, Theorem 6.
-/

namespace MetaMathlibExt

open ArithmeticFunction

private theorem smooth_eq_sq (f : ArithmeticFunction ℂ) (hf : f.IsMultiplicative)
    {p n : ℕ}
    (hind : ∀ q s : ℕ, q.Prime → q < p → 1 ≤ s → f (q ^ s) = (q : ℂ) ^ (2 * s))
    (hn : ∀ q : ℕ, q.Prime → q ∣ n → q < p) : f n = (n : ℂ) ^ 2 := by
  induction n using Nat.recOnPosPrimePosCoprime with
  | zero => simp
  | one => simp [hf]
  | prime_pow q s hq hs =>
    have hqp := hn q hq (dvd_pow_self q hs.ne')
    rw [hind q s hq hqp hs, Nat.cast_pow, ← pow_mul]
    congr 1
    omega
  | coprime a b ha hb hab iha ihb =>
    rw [hf.map_mul_of_coprime hab, iha (fun q hq hqa =>
      hn q hq (dvd_mul_of_dvd_left hqa b)), ihb (fun q hq hqb =>
      hn q hq (dvd_mul_of_dvd_right hqb a)), Nat.cast_mul, mul_pow]

private theorem small_prime_factors {p n : ℕ} (hn0 : 0 < n) (hn : n < 2 * p)
    (hprime : n.Prime → n < p) : ∀ q : ℕ, q.Prime → q ∣ n → q < p := by
  intro q hq hqn
  by_contra hqp
  obtain ⟨a, rfl⟩ := hqn
  have ha : a < 2 := by nlinarith [hq.two_le]
  have ha0 : a ≠ 0 := by
    intro ha0
    subst a
    simp at hn0
  have ha1 : a = 1 := by omega
  subst a
  simp only [mul_one] at hprime
  exact hqp (hprime hq)

private theorem square_value (f : ArithmeticFunction ℂ) (hf : f.IsMultiplicative)
    {p n : ℕ}
    (hind : ∀ q s : ℕ, q.Prime → q < p → 1 ≤ s → f (q ^ s) = (q : ℂ) ^ (2 * s))
    (hn : ∀ q : ℕ, q.Prime → q ∣ n → q < p) : f (n ^ 2) = (n : ℂ) ^ 4 := by
  have h := smooth_eq_sq f hf hind (n := n ^ 2)
    (fun q hq hqn => hn q hq (hq.dvd_of_dvd_pow hqn))
  simpa only [Nat.cast_pow, ← pow_mul] using h

private theorem sum_squares_value (f : ArithmeticFunction ℂ) (hf : f.IsMultiplicative)
    (hpar : ∀ m n : ℕ, 0 < n → n < m →
      f (m ^ 2 + n ^ 2) + f (m ^ 2 - n ^ 2) = 2 * f (m ^ 2) + 2 * f (n ^ 2))
    {p : ℕ}
    (hind : ∀ q s : ℕ, q.Prime → q < p → 1 ≤ s → f (q ^ s) = (q : ℂ) ^ (2 * s))
    (m n : ℕ) (hmn : m + n < p) :
    f (m ^ 2 + n ^ 2) = ((m ^ 2 + n ^ 2 : ℕ) : ℂ) ^ 2 := by
  have hsmall (a : ℕ) (ha0 : 0 < a) (ha : a < p) :
      ∀ q : ℕ, q.Prime → q ∣ a → q < p := by
    intro q _ hqa
    exact (Nat.le_of_dvd ha0 hqa).trans_lt ha
  have hsq (a : ℕ) (ha : a < p) : f (a ^ 2) = (a : ℂ) ^ 4 := by
    by_cases ha0 : a = 0
    · subst a
      simp
    exact square_value f hf hind (hsmall a (by omega) ha)
  wlog hle : n ≤ m generalizing m n
  · simpa [add_comm] using this n m (by omega) (by omega)
  by_cases hn0 : n = 0
  · subst n
    simpa [← pow_mul] using hsq m (by omega)
  by_cases hnm : n = m
  · subst n
    apply smooth_eq_sq f hf hind
    intro q hq hqd
    have hd : q ∣ 2 * m ^ 2 := by simpa [two_mul] using hqd
    rcases hq.dvd_mul.mp hd with hq2 | hqm
    · exact (Nat.le_of_dvd (by decide) hq2).trans_lt (by omega)
    · exact hsmall m (by omega) (by omega) q hq (hq.dvd_of_dvd_pow hqm)
  have hdiff : m ^ 2 - n ^ 2 = (m + n) * (m - n) := by
    apply Nat.sub_eq_of_eq_add
    have hsub : m - n + n = m := Nat.sub_add_cancel hle
    nlinarith
  have hd := smooth_eq_sq f hf hind (n := m ^ 2 - n ^ 2) (by
    rw [hdiff]
    intro q hq hqd
    rcases hq.dvd_mul.mp hqd with hqsum | hqsub
    · exact (Nat.le_of_dvd (by omega) hqsum).trans_lt hmn
    · exact (Nat.le_of_dvd (by omega) hqsub).trans_lt (by omega))
  have h := hpar m n (by omega) (by omega)
  rw [hd, hsq m (by omega), hsq n (by omega)] at h
  have hle2 : n ^ 2 ≤ m ^ 2 := Nat.pow_le_pow_left hle 2
  push_cast [Nat.cast_sub hle2] at h ⊢
  linear_combination h

private theorem norm_value (f : ArithmeticFunction ℂ) (hf : f.IsMultiplicative)
    (hpar : ∀ m n : ℕ, 0 < n → n < m →
      f (m ^ 2 + n ^ 2) + f (m ^ 2 - n ^ 2) = 2 * f (m ^ 2) + 2 * f (n ^ 2))
    {p d : ℕ}
    (hind : ∀ q s : ℕ, q.Prime → q < p → 1 ≤ s → f (q ^ s) = (q : ℂ) ^ (2 * s))
    (hd : ∃ m n : ℕ, d = m ^ 2 + n ^ 2) (hlt : 2 * d < p ^ 2) :
    f d = (d : ℂ) ^ 2 := by
  obtain ⟨m, n, rfl⟩ := hd
  apply sum_squares_value f hf hpar hind m n
  have hbound : (m + n) ^ 2 ≤ 2 * (m ^ 2 + n ^ 2) := by
    zify
    nlinarith [sq_nonneg ((m : ℤ) - (n : ℤ))]
  nlinarith

private theorem smooth_mul_norm_value (f : ArithmeticFunction ℂ) (hf : f.IsMultiplicative)
    (hpar : ∀ m n : ℕ, 0 < n → n < m →
      f (m ^ 2 + n ^ 2) + f (m ^ 2 - n ^ 2) = 2 * f (m ^ 2) + 2 * f (n ^ 2))
    {p c n : ℕ}
    (hind : ∀ q s : ℕ, q.Prime → q < p → 1 ≤ s → f (q ^ s) = (q : ℂ) ^ (2 * s))
    (hc : ∀ q : ℕ, q.Prime → q ∣ c → q < p)
    (hn0 : 0 < n) (hn : IsSquare (-1 : ZMod n)) (hlt : 2 * n < p ^ 2) :
    f (c * n) = ((c * n : ℕ) : ℂ) ^ 2 := by
  have hpow (q s : ℕ) (hq : q.Prime) (hs : 0 < s) (hd : q ^ s ∣ c * n) :
      f (q ^ s) = ((q ^ s : ℕ) : ℂ) ^ 2 := by
    by_cases hqp : q < p
    · simpa [Nat.cast_pow, ← pow_mul, Nat.mul_comm] using hind q s hq hqp hs
    have hcop : Nat.Coprime q c := hq.coprime_iff_not_dvd.mpr
      (fun hqc => hqp (hc q hq hqc))
    have hdn : q ^ s ∣ n := (hcop.pow_left s).dvd_of_dvd_mul_left hd
    exact norm_value f hf hpar hind
      (Nat.eq_sq_add_sq_of_isSquare_mod_neg_one (ZMod.isSquare_neg_one_of_dvd hdn hn))
      (lt_of_le_of_lt (Nat.mul_le_mul_left 2 (Nat.le_of_dvd hn0 hdn)) hlt)
  have hgen (a : ℕ) (ha : a ∣ c * n) : f a = (a : ℂ) ^ 2 := by
    induction a using Nat.recOnPosPrimePosCoprime with
    | zero => simp
    | one => simp [hf]
    | prime_pow q s hq hs => exact hpow q s hq hs ha
    | coprime a b ha0 hb0 hab iha ihb =>
      rw [hf.map_mul_of_coprime hab, iha (dvd_trans (dvd_mul_right a b) ha),
        ihb (dvd_trans (dvd_mul_left b a) ha), Nat.cast_mul, mul_pow]
  exact hgen (c * n) dvd_rfl

private theorem small_square_value (f : ArithmeticFunction ℂ) (hf : f.IsMultiplicative)
    {p n : ℕ}
    (hind : ∀ q s : ℕ, q.Prime → q < p → 1 ≤ s → f (q ^ s) = (q : ℂ) ^ (2 * s))
    (hn : n < p) : f (n ^ 2) = (n : ℂ) ^ 4 := by
  by_cases hn0 : n = 0
  · subst n
    simp
  exact square_value f hf hind (fun q _ hqd =>
    (Nat.le_of_dvd (by omega) hqd).trans_lt hn)

private theorem odd_square_value (f : ArithmeticFunction ℂ) (hf : f.IsMultiplicative)
    (hpar : ∀ m n : ℕ, 0 < n → n < m →
      f (m ^ 2 + n ^ 2) + f (m ^ 2 - n ^ 2) = 2 * f (m ^ 2) + 2 * f (n ^ 2))
    {p r : ℕ}
    (hind : ∀ q s : ℕ, q.Prime → q < p → 1 ≤ s → f (q ^ s) = (q : ℂ) ^ (2 * s))
    (hp2 : 2 < p) (hr : Odd r) (hrlt : r + 1 < 2 * p)
    (hfr : f r = (r : ℂ) ^ 2) : f (r ^ 2) = (r : ℂ) ^ 4 := by
  obtain ⟨a, rfl⟩ := hr
  by_cases ha0 : a = 0
  · subst a
    simpa using hfr
  have ha : 0 < a := by omega
  have ha' : a + 1 < p := by omega
  have hf2 : f 2 = (2 : ℂ) ^ 2 := by
    simpa using hind 2 1 Nat.prime_two hp2 (by decide)
  have hdiff : (a + 1) ^ 2 - a ^ 2 = 2 * a + 1 := by
    apply Nat.sub_eq_of_eq_add
    ring
  have hsum := hpar (a + 1) a ha (by omega)
  rw [hdiff, hfr, small_square_value f hf hind ha',
    small_square_value f hf hind (by omega : a < p)] at hsum
  have hcop : Nat.Coprime 2 ((a + 1) ^ 2 + a ^ 2) :=
    Nat.coprime_two_left.mpr ⟨a ^ 2 + a, by ring⟩
  have hfactor : (2 * a + 1) ^ 2 + 1 = 2 * ((a + 1) ^ 2 + a ^ 2) := by ring
  have hplus : f ((2 * a + 1) ^ 2 + 1) = (((2 * a + 1) ^ 2 + 1 : ℕ) : ℂ) ^ 2 := by
    rw [hfactor, hf.map_mul_of_coprime hcop, hf2]
    push_cast at hsum ⊢
    linear_combination 4 * hsum
  have hminus : (2 * a + 1) ^ 2 - 1 = 4 * (a * (a + 1)) := by
    apply Nat.sub_eq_of_eq_add
    ring
  have hminusval := smooth_eq_sq f hf hind (n := (2 * a + 1) ^ 2 - 1) (by
    rw [hminus]
    intro q hq hqd
    rcases hq.dvd_mul.mp hqd with hq4 | hqab
    · have hq2 : q ∣ 2 := hq.dvd_of_dvd_pow (by simpa using hq4 : q ∣ 2 ^ 2)
      exact (Nat.le_of_dvd (by decide) hq2).trans_lt hp2
    · rcases hq.dvd_mul.mp hqab with hqa | hqa'
      · exact (Nat.le_of_dvd ha hqa).trans_lt (by omega)
      · exact (Nat.le_of_dvd (by omega) hqa').trans_lt ha')
  have h := hpar (2 * a + 1) 1 (by decide) (by omega)
  simp only [one_pow] at h
  rw [hplus, hminusval, hminus] at h
  simp only [hf.map_one] at h
  push_cast at h ⊢
  linear_combination -h / 2

/-- **Parallelogram induction: primes congruent to 3 mod 4 from 19 on.**
Let $f$ be a complex-valued multiplicative arithmetic function
(so $f(0) = 0$) such that $f(m^2 + n^2) + f(m^2 - n^2) = 2f(m^2) + 2f(n^2)$ for all integers
$m > n \ge 1$.
Let $p$ be a prime such that $f(q^s) = q^{2s}$ for every prime $q < p$ and every integer
$s \ge 1$.
If $p = 4k - 1$ for some natural number $k$ and $p \ge 19$, then $f(p) = p^2$.

Source: Poo-Sung Park, *On the Parallelogram Uniqueness of Square Numbers for Multiplicative
Functions*, INTEGERS 24 (2024), Article A108, Theorem 6 (`integers-2024-A108-thm-6`). -/
public theorem parallelogram_multiplicative_prime_three_mod_four (f : ArithmeticFunction ℂ)
    (hf : f.IsMultiplicative)
    (hpar : ∀ m n : ℕ, 0 < n → n < m →
      f (m ^ 2 + n ^ 2) + f (m ^ 2 - n ^ 2) = 2 * f (m ^ 2) + 2 * f (n ^ 2))
    {p : ℕ} (hp : p.Prime)
    (hind : ∀ q s : ℕ, q.Prime → q < p → 1 ≤ s → f (q ^ s) = (q : ℂ) ^ (2 * s))
    {k : ℕ} (hpk : p = 4 * k - 1) (h19 : 19 ≤ p) :
    f p = (p : ℂ) ^ 2 := by
  have hk : 5 ≤ k := by omega
  have hpk' : p + 1 = 4 * k := by omega
  have hsmall (a : ℕ) (ha0 : 0 < a) (ha : a < p) :
      ∀ q : ℕ, q.Prime → q ∣ a → q < p := by
    intro q _ hqa
    exact (Nat.le_of_dvd ha0 hqa).trans_lt ha
  have hnorm (a c : ℕ) (hc0 : 0 < c) (hc : c < 2 * p) (hcp : ¬ c.Prime)
      (hlt : 2 * (a ^ 2 + 1) < p ^ 2) :
      f (c * (a ^ 2 + 1)) = ((c * (a ^ 2 + 1) : ℕ) : ℂ) ^ 2 := by
    exact smooth_mul_norm_value f hf hpar hind
      (small_prime_factors hc0 hc (by aesop)) (by positivity)
      (ZMod.isSquare_neg_one_of_eq_sq_add_sq_of_coprime
        (x := a) (y := 1) (by simp) (by simp)) hlt
  have hproduct (c a : ℕ) (hc0 : 0 < c) (hc : c < p) (ha0 : 0 < a) (ha : a < p) :
      f (c * a * p) = ((c * a : ℕ) : ℂ) ^ 2 * f p := by
    have hs : ∀ q : ℕ, q.Prime → q ∣ c * a → q < p := by
      intro q hq hqd
      rcases hq.dvd_mul.mp hqd with hqc | hqa
      · exact hsmall c hc0 hc q hq hqc
      · exact hsmall a ha0 ha q hq hqa
    have hcop : Nat.Coprime (c * a) p :=
      (hp.coprime_iff_not_dvd.mpr (fun hpd => (lt_irrefl p) (hs p hp hpd))).symm
    rw [hf.map_mul_of_coprime hcop, smooth_eq_sq f hf hind hs]
  rcases Nat.even_or_odd k with heven | hodd
  · have hr : (6 * k + 1) % 4 = 1 := by
      obtain ⟨t, ht⟩ := heven
      omega
    have hfr : f (6 * k + 1) = ((6 * k + 1 : ℕ) : ℂ) ^ 2 := by
      by_cases hprime : (6 * k + 1).Prime
      · have : Fact (6 * k + 1).Prime := ⟨hprime⟩
        obtain ⟨a, b, hab⟩ := Nat.Prime.sq_add_sq (p := 6 * k + 1) (by omega)
        exact norm_value f hf hpar hind ⟨a, b, hab.symm⟩ (by nlinarith)
      · exact smooth_eq_sq f hf hind (small_prime_factors (by omega)
          (by omega) (by aesop))
    have hrsq := odd_square_value f hf hpar hind (by omega : 2 < p)
      (show Odd (6 * k + 1) from ⟨3 * k, by omega⟩) (by omega) hfr
    have hsum : (6 * k + 1) ^ 2 + (2 * k - 3) ^ 2 = 10 * ((2 * k) ^ 2 + 1) := by
      have hsub : 2 * k - 3 + 3 = 2 * k := by omega
      nlinarith
    have hdiff : (6 * k + 1) ^ 2 - (2 * k - 3) ^ 2 = 8 * (k + 1) * p := by
      apply Nat.sub_eq_of_eq_add
      have hsub : 2 * k - 3 + 3 = 2 * k := by omega
      nlinarith
    have h := hpar (6 * k + 1) (2 * k - 3) (by omega) (by omega)
    rw [hsum, hnorm (2 * k) 10 (by decide) (by omega) (by decide) (by nlinarith),
      hdiff, hproduct 8 (k + 1) (by decide) (by omega) (by omega) (by omega),
      hrsq, small_square_value f hf hind (by omega : 2 * k - 3 < p)] at h
    have hsub : ((2 * k - 3 : ℕ) : ℂ) = 2 * (k : ℂ) - 3 := by
      push_cast [Nat.cast_sub (by omega : 3 ≤ 2 * k)]
      ring
    rw [hsub] at h
    have hpc : (p : ℂ) = 4 * (k : ℂ) - 1 := by
      exact_mod_cast (show (p : ℤ) = 4 * (k : ℤ) - 1 by omega)
    have hc : ((8 * (k + 1) : ℕ) : ℂ) ^ 2 ≠ 0 := by
      exact pow_ne_zero 2 (Nat.cast_ne_zero.mpr (by omega))
    apply (mul_left_cancel₀ hc)
    push_cast at h ⊢
    rw [hpc]
    linear_combination h
  · obtain ⟨t, ht⟩ := hodd
    have hm : 5 * k + 3 = 2 * (5 * t + 4) := by omega
    have hms : ∀ q : ℕ, q.Prime → q ∣ 5 * k + 3 → q < p := by
      rw [hm]
      intro q hq hqd
      rcases hq.dvd_mul.mp hqd with hq2 | hqt
      · exact (Nat.le_of_dvd (by decide) hq2).trans_lt (by omega)
      · exact hsmall (5 * t + 4) (by omega) (by omega) q hq hqt
    have hsum : (5 * k + 3) ^ 2 + (3 * k - 5) ^ 2 = 34 * (k ^ 2 + 1) := by
      have hsub : 3 * k - 5 + 5 = 3 * k := by omega
      nlinarith
    have hdiff : (5 * k + 3) ^ 2 - (3 * k - 5) ^ 2 = 4 * (k + 4) * p := by
      apply Nat.sub_eq_of_eq_add
      have hsub : 3 * k - 5 + 5 = 3 * k := by omega
      nlinarith
    have h := hpar (5 * k + 3) (3 * k - 5) (by omega) (by omega)
    rw [hsum, hnorm k 34 (by decide) (by omega) (by decide) (by nlinarith),
      hdiff, hproduct 4 (k + 4) (by decide) (by omega) (by omega) (by omega),
      square_value f hf hind hms,
      small_square_value f hf hind (by omega : 3 * k - 5 < p)] at h
    have hsub : ((3 * k - 5 : ℕ) : ℂ) = 3 * (k : ℂ) - 5 := by
      push_cast [Nat.cast_sub (by omega : 5 ≤ 3 * k)]
      ring
    rw [hsub] at h
    have hpc : (p : ℂ) = 4 * (k : ℂ) - 1 := by
      exact_mod_cast (show (p : ℤ) = 4 * (k : ℤ) - 1 by omega)
    have hc : ((4 * (k + 4) : ℕ) : ℂ) ^ 2 ≠ 0 := by
      exact pow_ne_zero 2 (Nat.cast_ne_zero.mpr (by omega))
    apply (mul_left_cancel₀ hc)
    push_cast at h ⊢
    rw [hpc]
    linear_combination h

end MetaMathlibExt
