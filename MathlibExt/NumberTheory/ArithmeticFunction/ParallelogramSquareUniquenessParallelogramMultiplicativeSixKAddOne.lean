/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Basic.Complex.Basic
public import Mathlib.NumberTheory.ArithmeticFunction.Defs
import Mathlib.Data.Nat.Factorization.Basic
import Mathlib.NumberTheory.SumTwoSquares
import Mathlib.Tactic.LinearCombination

/-!
# Parallelogram induction: the value at 6k + 1

A multiplicative function satisfying the parallelogram identity on squares takes the square
value at `6 * k + 1` under the prime-power induction hypothesis for `p = 4 * k - 1`,
when `k ≢ 3 (mod 4)` and `p ≥ 19`.

Statement from Poo-Sung Park, *On the Parallelogram Uniqueness of Square Numbers for
Multiplicative Functions*, INTEGERS 24 (2024), Article A108.
-/

namespace MetaMathlibExt

open ArithmeticFunction

private theorem eq_sq_of_prime_factors_lt (f : ArithmeticFunction ℂ)
    (hf : f.IsMultiplicative) {p : ℕ} (hp : p.Prime)
    (hind : ∀ q s : ℕ, q.Prime → q < p → 1 ≤ s → f (q ^ s) = (q : ℂ) ^ (2 * s))
    (n : ℕ) (h : ∀ q : ℕ, q.Prime → q ∣ n → q < p) : f n = (n : ℂ) ^ 2 := by
  induction n using Nat.recOnPosPrimePosCoprime with
  | prime_pow q s hq hs =>
    rw [hind q s hq (h q hq (dvd_pow_self q hs.ne')) hs, Nat.cast_pow, ← pow_mul]
    congr 1
    omega
  | zero =>
    exact absurd (h p hp (dvd_zero p)) (lt_irrefl p)
  | one =>
    simp [hf.map_one]
  | coprime a b _ _ hab iha ihb =>
    have ha' : ∀ q : ℕ, q.Prime → q ∣ a → q < p :=
      fun q hq hqa => h q hq (hqa.trans (Nat.dvd_mul_right a b))
    have hb' : ∀ q : ℕ, q.Prime → q ∣ b → q < p :=
      fun q hq hqb => h q hq (hqb.trans (Nat.dvd_mul_left b a))
    rw [hf.map_mul_of_coprime hab, iha ha', ihb hb', Nat.cast_mul, mul_pow]

private theorem map_small_prime_mul (f : ArithmeticFunction ℂ)
    (hf : f.IsMultiplicative) {q : ℕ} (hq : q.Prime)
    (hpow : ∀ s : ℕ, 1 ≤ s → f (q ^ s) = (q : ℂ) ^ (2 * s))
    (n : ℕ) : f (q * n) = (q : ℂ) ^ 2 * f n := by
  by_cases hn : n = 0
  · subst n
    simp
  obtain ⟨e, m, hqm, rfl⟩ := Nat.exists_eq_pow_mul_and_not_dvd hn q hq.ne_one
  have hpow' (s : ℕ) : f (q ^ s) = (q : ℂ) ^ (2 * s) := by
    cases s with
    | zero => simp [hf.map_one]
    | succ s => exact hpow (s + 1) (by omega)
  have hfactor : q * (q ^ e * m) = q ^ (e + 1) * m := by
    rw [pow_succ]
    ring
  rw [hfactor, hf.map_mul_of_coprime ((hq.coprime_iff_not_dvd.mpr hqm).pow_left _),
    hf.map_mul_of_coprime ((hq.coprime_iff_not_dvd.mpr hqm).pow_left _), hpow', hpow',
    show 2 * (e + 1) = 2 + 2 * e by omega, pow_add]
  ring

private theorem pos_of_add_sq_eq_prime (t : ℕ) (htp : t.Prime) (ht31 : 31 ≤ t)
    (x y : ℕ) (h : x ^ 2 + y ^ 2 = t) : 1 ≤ x ∧ 1 ≤ y := by
  have one_le_fst : ∀ u v : ℕ, u ^ 2 + v ^ 2 = t → 1 ≤ u := by
    intro u v huv
    by_contra hcon
    have hu0 : u = 0 := by omega
    subst hu0
    norm_num at huv
    have hdiv : v ∣ t := by
      rw [← huv]
      exact dvd_pow_self v (by norm_num)
    rcases htp.eq_one_or_self_of_dvd v hdiv with hv1 | hvt
    · rw [hv1, one_pow] at huv
      omega
    · rw [hvt] at huv
      have hlt : t < t ^ 2 := by
        rw [pow_two]
        exact lt_mul_of_one_lt_right (by omega) (by omega)
      rw [huv] at hlt
      exact (lt_irrefl t) hlt
  exact ⟨one_le_fst x y h, one_le_fst y x ((add_comm (y ^ 2) (x ^ 2)).trans h)⟩

private theorem eq_pow_four_of_prime_factors_lt (f : ArithmeticFunction ℂ)
    (hf : f.IsMultiplicative) {p : ℕ} (hp : p.Prime)
    (hind : ∀ q s : ℕ, q.Prime → q < p → 1 ≤ s → f (q ^ s) = (q : ℂ) ^ (2 * s))
    (m : ℕ) (h : ∀ q : ℕ, q.Prime → q ∣ m → q < p) : f (m ^ 2) = (m : ℂ) ^ 4 := by
  have h2 : ∀ q : ℕ, q.Prime → q ∣ m ^ 2 → q < p :=
    fun q hq hqdvd => h q hq (hq.dvd_of_dvd_pow hqdvd)
  rw [eq_sq_of_prime_factors_lt f hf hp hind (m ^ 2) h2]
  push_cast
  ring

private theorem eq_sq_six_k_add_one_of_one_mod_four (f : ArithmeticFunction ℂ)
    (hf : f.IsMultiplicative)
    (hpar : ∀ m n : ℕ, 0 < n → n < m →
      f (m ^ 2 + n ^ 2) + f (m ^ 2 - n ^ 2) = 2 * f (m ^ 2) + 2 * f (n ^ 2))
    {p : ℕ} (hp : p.Prime)
    (hind : ∀ q s : ℕ, q.Prime → q < p → 1 ≤ s → f (q ^ s) = (q : ℂ) ^ (2 * s))
    {k : ℕ} (hpk : p = 4 * k - 1) (h19 : 19 ≤ p) (hk : k % 4 = 1) :
    f (6 * k + 1) = ((6 * k + 1 : ℕ) : ℂ) ^ 2 := by
  have hk5 : 5 ≤ k := by omega
  obtain ⟨r, hkr⟩ : ∃ r : ℕ, k = 4 * r + 1 := ⟨k / 4, by omega⟩
  have hsq (m : ℕ) (hm0 : 0 < m) (hmp : m < p) :
      f (m ^ 2) = (m : ℂ) ^ 4 := by
    apply eq_pow_four_of_prime_factors_lt f hf hp hind
    intro q _ hqm
    exact (Nat.le_of_dvd hm0 hqm).trans_lt hmp
  have hprod (a b : ℕ) (ha0 : 0 < a) (hb0 : 0 < b) (hap : a < p) (hbp : b < p) :
      f (a * b) = ((a * b : ℕ) : ℂ) ^ 2 := by
    apply eq_sq_of_prime_factors_lt f hf hp hind
    intro q hq hqdvd
    rcases hq.dvd_mul.mp hqdvd with hqa | hqb
    · exact (Nat.le_of_dvd ha0 hqa).trans_lt hap
    · exact (Nat.le_of_dvd hb0 hqb).trans_lt hbp
  have hdiff : (3 * k) ^ 2 - 1 ^ 2 = (3 * k + 1) * (3 * k - 1) := by
    simpa using Nat.sq_sub_sq (3 * k) 1
  have hfdiff := hprod (3 * k + 1) (3 * k - 1)
    (by omega) (by omega) (by omega) (by omega)
  have hplus : f ((3 * k) ^ 2 + 1) = (((3 * k) ^ 2 + 1 : ℕ) : ℂ) ^ 2 := by
    have h := hpar (3 * k) 1 (by omega) (by omega)
    rw [hdiff, hfdiff, hsq (3 * k) (by omega) (by omega), hsq 1 (by omega) (by omega)] at h
    norm_num at h
    rw [Nat.cast_sub (by omega : 1 ≤ 3 * k)] at h
    push_cast at h ⊢
    linear_combination h
  have hbcast : ((3 * k - 2 : ℕ) : ℂ) = 3 * (k : ℂ) - 2 := by
    rw [Nat.cast_sub (by omega : 2 ≤ 3 * k)]
    push_cast
    rfl
  have hsumsq : (6 * k + 1) ^ 2 + (3 * k - 2) ^ 2 = 5 * ((3 * k) ^ 2 + 1) := by
    have hb : 3 * k - 2 + 2 = 3 * k := by omega
    nlinarith [sq_nonneg (3 * k - 2)]
  have hfsumsq : f ((6 * k + 1) ^ 2 + (3 * k - 2) ^ 2) =
      (5 : ℂ) ^ 2 * (((3 * k) ^ 2 + 1 : ℕ) : ℂ) ^ 2 := by
    rw [hsumsq, map_small_prime_mul f hf (by decide : Nat.Prime 5)
      (fun s hs => hind 5 s (by decide) (by omega) hs), hplus]
    norm_num
  have hfdiffsq : f ((6 * k + 1) ^ 2 - (3 * k - 2) ^ 2) =
      (((6 * k + 1) ^ 2 - (3 * k - 2) ^ 2 : ℕ) : ℂ) ^ 2 := by
    apply eq_sq_of_prime_factors_lt f hf hp hind
    intro q hq hqdvd
    have hsum : 6 * k + 1 + (3 * k - 2) = 4 * (9 * r + 2) := by omega
    have hsub : 6 * k + 1 - (3 * k - 2) = 3 * k + 3 := by omega
    rw [Nat.sq_sub_sq, hsum, hsub] at hqdvd
    rcases hq.dvd_mul.mp hqdvd with hqa | hqb
    · rcases hq.dvd_mul.mp hqa with hq4 | hqr
      · exact (Nat.le_of_dvd (by omega : 0 < 4) hq4).trans_lt (by omega)
      · exact (Nat.le_of_dvd (by omega : 0 < 9 * r + 2) hqr).trans_lt (by omega)
    · exact (Nat.le_of_dvd (by omega : 0 < 3 * k + 3) hqb).trans_lt (by omega)
  have htsq : f ((6 * k + 1) ^ 2) = ((6 * k + 1 : ℕ) : ℂ) ^ 4 := by
    have h := hpar (6 * k + 1) (3 * k - 2) (by omega) (by omega)
    rw [hfsumsq, hfdiffsq, hsq (3 * k - 2) (by omega) (by omega),
      Nat.cast_sub (Nat.pow_le_pow_left (by omega : 3 * k - 2 ≤ 6 * k + 1) 2),
      Nat.cast_pow, Nat.cast_pow, hbcast] at h
    push_cast at h ⊢
    linear_combination -(1 / 2 : ℂ) * h
  have htplus : f ((6 * k + 1) ^ 2 + 1) = (((6 * k + 1) ^ 2 + 1 : ℕ) : ℂ) ^ 2 := by
    have hdiff : (6 * k + 1) ^ 2 - 1 ^ 2 = (6 * k + 2) * (6 * k) := by
      simpa using Nat.sq_sub_sq (6 * k + 1) 1
    have hfdiff : f ((6 * k + 2) * (6 * k)) = (((6 * k + 2) * (6 * k) : ℕ) : ℂ) ^ 2 := by
      apply eq_sq_of_prime_factors_lt f hf hp hind
      intro q hq hqdvd
      have hfactor : (6 * k + 2) * (6 * k) = 12 * ((3 * k + 1) * k) := by ring
      rw [hfactor] at hqdvd
      rcases hq.dvd_mul.mp hqdvd with hq12 | hqprod
      · exact (Nat.le_of_dvd (by omega : 0 < 12) hq12).trans_lt (by omega)
      · rcases hq.dvd_mul.mp hqprod with hqa | hqb
        · exact (Nat.le_of_dvd (by omega : 0 < 3 * k + 1) hqa).trans_lt (by omega)
        · exact (Nat.le_of_dvd (by omega : 0 < k) hqb).trans_lt (by omega)
    have h := hpar (6 * k + 1) 1 (by omega) (by omega)
    rw [hdiff, hfdiff, htsq, hsq 1 (by omega) (by omega)] at h
    norm_num at h
    push_cast at h ⊢
    linear_combination h
  have hsumval : f ((3 * k + 1) ^ 2 + (3 * k) ^ 2) =
      (((3 * k + 1) ^ 2 + (3 * k) ^ 2 : ℕ) : ℂ) ^ 2 := by
    have hfactor : (6 * k + 1) ^ 2 + 1 = 2 * ((3 * k + 1) ^ 2 + (3 * k) ^ 2) := by
      ring
    rw [hfactor, map_small_prime_mul f hf Nat.prime_two
      (fun s hs => hind 2 s Nat.prime_two (by omega) hs)] at htplus
    push_cast at htplus ⊢
    linear_combination (1 / 4 : ℂ) * htplus
  have hdiff : (3 * k + 1) ^ 2 - (3 * k) ^ 2 = 6 * k + 1 := by
    apply Nat.sub_eq_of_eq_add
    ring
  have h := hpar (3 * k + 1) (3 * k) (by omega) (by omega)
  rw [hdiff, hsumval, hsq (3 * k + 1) (by omega) (by omega),
    hsq (3 * k) (by omega) (by omega)] at h
  push_cast at h ⊢
  linear_combination h

/-- **Parallelogram induction: the value at 6k + 1.**
Let $f$ be a complex-valued multiplicative arithmetic function
(so $f(0) = 0$) such that $f(m^2 + n^2) + f(m^2 - n^2) = 2f(m^2) + 2f(n^2)$ for all integers
$m > n \ge 1$.
Let $p$ be a prime such that $f(q^s) = q^{2s}$ for every prime $q < p$ and every integer
$s \ge 1$.
If $p = 4k - 1$ for a natural number $k$ with $k \not\equiv 3 \pmod 4$, and $p \ge 19$,
then $f(6k + 1) = (6k + 1)^2$.

Source: Poo-Sung Park, *On the Parallelogram Uniqueness of Square Numbers for Multiplicative
Functions*, INTEGERS 24 (2024), Article A108, Lemma 5 (`integers-2024-A108-lem-5`). -/
public theorem parallelogram_multiplicative_six_k_add_one (f : ArithmeticFunction ℂ)
    (hf : f.IsMultiplicative)
    (hpar : ∀ m n : ℕ, 0 < n → n < m →
      f (m ^ 2 + n ^ 2) + f (m ^ 2 - n ^ 2) = 2 * f (m ^ 2) + 2 * f (n ^ 2))
    {p : ℕ} (hp : p.Prime)
    (hind : ∀ q s : ℕ, q.Prime → q < p → 1 ≤ s → f (q ^ s) = (q : ℂ) ^ (2 * s))
    {k : ℕ} (hpk : p = 4 * k - 1) (h19 : 19 ≤ p) (hk : k % 4 ≠ 3) :
    f (6 * k + 1) = ((6 * k + 1 : ℕ) : ℂ) ^ 2 := by
  have hk5 : 5 ≤ k := by omega
  have ht_lt_2p : 6 * k + 1 < 2 * p := by omega
  by_cases htp : (6 * k + 1).Prime
  · by_cases hk2 : k % 2 = 0
    · have : Fact ((6 * k + 1).Prime) := ⟨htp⟩
      obtain ⟨a, b, hab⟩ :=
        Nat.Prime.sq_add_sq (show (6 * k + 1) % 4 ≠ 3 by omega)
      obtain ⟨ha1, hb1⟩ := pos_of_add_sq_eq_prime (6 * k + 1) htp (by omega) a b hab
      have hab_ne : a ≠ b := by
        rintro rfl
        have hdiv : 2 ∣ 6 * k + 1 := by
          rw [← hab]
          exact ⟨a ^ 2, by ring⟩
        omega
      obtain ⟨m, n, hnm, hn1, hmn_sq⟩ :
          ∃ m n, n < m ∧ 1 ≤ n ∧ m ^ 2 + n ^ 2 = 6 * k + 1 := by
        rcases lt_or_gt_of_ne hab_ne with hlt | hgt
        · exact ⟨b, a, hlt, ha1, by rw [add_comm (b ^ 2) (a ^ 2)]; exact hab⟩
        · exact ⟨a, b, hgt, hb1, hab⟩
      have hm_pos : 0 < m := by omega
      have hn_pos : 0 < n := by omega
      have hmsq_lt : m ^ 2 < p ^ 2 := by
        have h1 : m ^ 2 ≤ 6 * k + 1 := by omega
        have h2 : 6 * k + 1 < p ^ 2 := by
          calc 6 * k + 1 < 19 * p := by omega
          _ ≤ p * p := Nat.mul_le_mul_right p h19
          _ = p ^ 2 := (pow_two p).symm
        exact lt_of_le_of_lt h1 h2
      have hm_lt : m < p := lt_of_pow_lt_pow_left' 2 hmsq_lt
      have hn_lt : n < p := lt_of_le_of_lt (le_of_lt hnm) hm_lt
      have hsum_lt : m + n < p := by
        apply lt_of_pow_lt_pow_left' 2
        have h2mn : 2 * m * n ≤ m ^ 2 + n ^ 2 := two_mul_le_add_pow_two m n
        have hexp : (m + n) ^ 2 = m ^ 2 + 2 * m * n + n ^ 2 := by ring
        have h2t : 2 * (6 * k + 1) < p ^ 2 := by
          calc 2 * (6 * k + 1) < 19 * p := by omega
          _ ≤ p * p := Nat.mul_le_mul_right p h19
          _ = p ^ 2 := (pow_two p).symm
        omega
      have hm_factors : ∀ q : ℕ, q.Prime → q ∣ m → q < p := by
        intro q _ hqm
        exact lt_of_le_of_lt (Nat.le_of_dvd hm_pos hqm) hm_lt
      have hn_factors : ∀ q : ℕ, q.Prime → q ∣ n → q < p := by
        intro q _ hqn
        exact lt_of_le_of_lt (Nat.le_of_dvd hn_pos hqn) hn_lt
      have hdiff_factors : ∀ q : ℕ, q.Prime → q ∣ m ^ 2 - n ^ 2 → q < p := by
        intro q hq hqdvd
        rw [Nat.sq_sub_sq] at hqdvd
        rcases hq.dvd_mul.mp hqdvd with h1 | h1
        · exact lt_of_le_of_lt (Nat.le_of_dvd (by omega) h1) hsum_lt
        · have hle : q ≤ m + n :=
            le_trans (Nat.le_of_dvd (by omega) h1) (by omega)
          exact lt_of_le_of_lt hle hsum_lt
      have hfm : f (m ^ 2) = (m : ℂ) ^ 4 :=
        eq_pow_four_of_prime_factors_lt f hf hp hind m hm_factors
      have hfn : f (n ^ 2) = (n : ℂ) ^ 4 :=
        eq_pow_four_of_prime_factors_lt f hf hp hind n hn_factors
      have hfdiff : f (m ^ 2 - n ^ 2) = ((m ^ 2 - n ^ 2 : ℕ) : ℂ) ^ 2 :=
        eq_sq_of_prime_factors_lt f hf hp hind (m ^ 2 - n ^ 2) hdiff_factors
      have hpar_inst := hpar m n hn1 hnm
      rw [hmn_sq, hfdiff, hfm, hfn] at hpar_inst
      have hdiff_cast : ((m ^ 2 - n ^ 2 : ℕ) : ℂ) = (m : ℂ) ^ 2 - (n : ℂ) ^ 2 := by
        rw [Nat.cast_sub (Nat.pow_le_pow_left (le_of_lt hnm) 2), Nat.cast_pow, Nat.cast_pow]
      rw [hdiff_cast] at hpar_inst
      have hgoal_cast : ((6 * k + 1 : ℕ) : ℂ) = (m : ℂ) ^ 2 + (n : ℂ) ^ 2 := by
        rw [← hmn_sq, Nat.cast_add, Nat.cast_pow, Nat.cast_pow]
      rw [hgoal_cast]
      linear_combination hpar_inst
    · exact eq_sq_six_k_add_one_of_one_mod_four f hf hpar hp hind hpk h19 (by omega)
  · apply eq_sq_of_prime_factors_lt f hf hp hind
    intro q hq hqdvd
    obtain ⟨m, hm⟩ := hqdvd
    have hm2 : 2 ≤ m := by
      by_contra hcon
      have hm01 : m = 0 ∨ m = 1 := by omega
      rcases hm01 with rfl | rfl
      · omega
      · rw [mul_one] at hm
        rw [hm] at htp
        exact absurd hq htp
    have hle : q * 2 ≤ 6 * k + 1 := by
      rw [hm]
      exact Nat.mul_le_mul_left q hm2
    omega

end MetaMathlibExt
