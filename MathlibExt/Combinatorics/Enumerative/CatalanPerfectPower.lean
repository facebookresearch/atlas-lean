/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Portions of this file are adapted from:

`Mathlib/NumberTheory/Bertrand.lean` (Mathlib):
Copyright (c) 2020 Patrick Stevens. All rights reserved.
Licensed under the Apache License, Version 2.0 (https://www.apache.org/licenses/LICENSE-2.0).
Authors: Patrick Stevens, Bolton Bailey
-/

module

public import Mathlib.Combinatorics.Enumerative.Catalan.Basic
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Convex.SpecificFunctions.Basic
import Mathlib.Analysis.Convex.SpecificFunctions.Deriv
import Mathlib.Data.Int.Star
import Mathlib.Data.Nat.Choose.Dvd
import Mathlib.NumberTheory.Primorial
import Mathlib.RingTheory.Etale.Weakly
import Mathlib.RingTheory.Flat.TorsionFree
import Mathlib.RingTheory.TotallySplit
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

@[expose] public section

namespace MetaMathlibExt

/-! # Catalan numbers are never perfect powers
-/

-- A real-analytic inequality, adapting `Bertrand.real_main_inequality` with an
-- extra `2 * x` factor (which the original bound has room to absorb for `x ≥ 512`).
open Real in
private theorem my_real_inequality {x : ℝ} (x_large : (512 : ℝ) ≤ x) :
    x * (2 * x) ^ (√(2 * x) + 1) * 4 ^ (2 * x / 3) ≤ 4 ^ x := by
  let f : ℝ → ℝ := fun x => log x + √(2 * x) * log (2 * x) + log (2 * x) - log 4 / 3 * x
  have hf' : ∀ x, 0 < x → 0 < x * (2 * x) ^ (√(2 * x) + 1) / 4 ^ (x / 3) := fun x h =>
    div_pos (mul_pos h (rpow_pos_of_pos (mul_pos two_pos h) _)) (rpow_pos_of_pos four_pos _)
  have hf : ∀ x, 0 < x → f x = log (x * (2 * x) ^ (√(2 * x) + 1) / 4 ^ (x / 3)) := by
    intro x h5
    have h6 := mul_pos (zero_lt_two' ℝ) h5
    have h7 := rpow_pos_of_pos h6 (√(2 * x) + 1)
    rw [log_div (mul_pos h5 h7).ne' (rpow_pos_of_pos four_pos _).ne', log_mul h5.ne' h7.ne',
      log_rpow h6, log_rpow zero_lt_four, ← mul_div_right_comm, ← mul_div, mul_comm x]
    change log x + √(2 * x) * log (2 * x) + log (2 * x) - log 4 / 3 * x = _
    ring
  have h5 : 0 < x := lt_of_lt_of_le (by norm_num1) x_large
  rw [← div_le_one (rpow_pos_of_pos four_pos x), ← div_div_eq_mul_div, ← rpow_sub four_pos, ←
    mul_div 2 x, mul_div_left_comm, ← mul_one_sub, (by norm_num1 : (1 : ℝ) - 2 / 3 = 1 / 3),
    mul_one_div, ← log_nonpos_iff (hf' x h5).le, ← hf x h5]
  have h : ConcaveOn ℝ (Set.Ioi 0.5) f := by
    apply ConcaveOn.sub
    · apply ConcaveOn.add
      · apply ConcaveOn.add
        · exact strictConcaveOn_log_Ioi.concaveOn.subset
            (Set.Ioi_subset_Ioi (by norm_num)) (convex_Ioi 0.5)
        · convert!
            ((strictConcaveOn_sqrt_mul_log_Ioi.concaveOn.comp_linearMap ((2 : ℝ) • LinearMap.id)))
            using 1
          ext y
          simp only [Set.mem_Ioi, Set.mem_preimage, LinearMap.smul_apply,
            LinearMap.id_coe, id_eq, smul_eq_mul]
          rw [← mul_lt_mul_iff_right₀ (two_pos)]
          norm_num1
          rfl
      · refine (strictConcaveOn_log_Ioi.concaveOn.comp_linearMap
          ((2 : ℝ) • LinearMap.id)).subset ?_ (convex_Ioi 0.5)
        intro y hy
        simp only [Set.mem_Ioi, Set.mem_preimage, LinearMap.smul_apply,
          LinearMap.id_coe, id_eq, smul_eq_mul] at *
        linarith
    apply ConvexOn.smul
    · refine div_nonneg (log_nonneg (by norm_num1)) (by norm_num1)
    · exact convexOn_id (convex_Ioi (0.5 : ℝ))
  suffices ∃ x1 x2, 0.5 < x1 ∧ x1 < x2 ∧ x2 ≤ x ∧ 0 ≤ f x1 ∧ f x2 ≤ 0 by
    obtain ⟨x1, x2, h1, h2, h0, h3, h4⟩ := this
    exact (h.right_le_of_le_left'' h1 ((h1.trans h2).trans_le h0) h2 h0 (h4.trans h3)).trans h4
  refine ⟨18, 512, by norm_num1, by norm_num1, x_large, ?_, ?_⟩
  · have h18 : √(2 * 18 : ℝ) = 6 :=
      (sqrt_eq_iff_mul_self_eq_of_pos (by norm_num1)).mpr (by norm_num1)
    rw [hf _ (by norm_num1), log_nonneg_iff (by positivity), h18, one_le_div (by norm_num1)]
    norm_num1
  · have h512 : √(2 * 512) = 32 :=
      (sqrt_eq_iff_mul_self_eq_of_pos (by norm_num1)).mpr (by norm_num1)
    rw [hf _ (by norm_num1), log_nonpos_iff (hf' _ (by norm_num1)).le, h512,
        div_le_one (by positivity)]
    rw [show (32 : ℝ) + 1 = ((33 : ℕ) : ℝ) by norm_num1,
        show (512 : ℝ) = 2 ^ (9 : ℕ) by norm_num1,
        show (2 : ℝ) * 2 ^ (9 : ℕ) = 2 ^ (10 : ℕ) by norm_num1,
        rpow_natCast, ← pow_mul, ← pow_add, ← rpow_natCast]
    rw [show (4 : ℝ) = (2 : ℝ) ^ (2 : ℝ) by rw [rpow_two]; norm_num1, ← rpow_mul (by norm_num1)]
    apply rpow_le_rpow_of_exponent_le (by norm_num1)
    norm_num1

-- The Nat analogue of `my_real_inequality`, matching `bertrand_main_inequality`.
open Nat in
private theorem my_bertrand_inequality {n : ℕ} (n_large : 512 ≤ n) :
    n * (2 * n) ^ (Nat.sqrt (2 * n) + 1) * 4 ^ (2 * n / 3) ≤ 4 ^ n := by
  rw [← @Nat.cast_le ℝ]
  push_cast [← Real.rpow_natCast]
  refine _root_.trans ?_ (my_real_inequality (by exact_mod_cast n_large))
  gcongr
  · exact_mod_cast (show 1 ≤ 2 * n by omega)
  · exact_mod_cast Real.nat_sqrt_le_real_sqrt
  · norm_num1
  · exact Nat.cast_div_le.trans (le_of_eq (by push_cast; ring))

-- An unconditional bound on the contribution of primes `≤ 2 * n / 3` to
-- `centralBinom n`, extracted from the proof of `centralBinom_le_of_no_bertrand_prime`.
open Nat in
private theorem prod_small_le (n : ℕ) (n_large : 2 < n) :
    ∏ p ∈ Finset.range (2 * n / 3 + 1), p ^ (Nat.centralBinom n).factorization p
      ≤ (2 * n) ^ Nat.sqrt (2 * n) * 4 ^ (2 * n / 3) := by
  have n_pos : 0 < n := (Nat.zero_le _).trans_lt n_large
  have n2_pos : 1 ≤ 2 * n := mul_pos (zero_lt_two' ℕ) n_pos
  let S := {p ∈ Finset.range (2 * n / 3 + 1) | Nat.Prime p}
  let f x := x ^ n.centralBinom.factorization x
  have hS : ∏ x ∈ S, f x = ∏ x ∈ Finset.range (2 * n / 3 + 1), f x := by
    refine Finset.prod_filter_of_ne fun p _ h => ?_
    contrapose h; dsimp only [f]
    rw [factorization_eq_zero_of_not_prime n.centralBinom h, _root_.pow_zero]
  rw [← hS, ← Finset.prod_filter_mul_prod_filter_not S (· ≤ sqrt (2 * n))]
  apply mul_le_mul'
  · refine (Finset.prod_le_prod fun p _ => (?_ : f p ≤ 2 * n)).trans ?_
    · exact pow_factorization_choose_le (mul_pos two_pos n_pos)
    have : (Finset.Icc 1 (sqrt (2 * n))).card = sqrt (2 * n) := by rw [card_Icc, Nat.add_sub_cancel]
    rw [Finset.prod_const]
    refine pow_right_mono₀ n2_pos ((Finset.card_le_card fun x hx => ?_).trans this.le)
    obtain ⟨h1, h2⟩ := Finset.mem_filter.1 hx
    exact Finset.mem_Icc.mpr ⟨(Finset.mem_filter.1 h1).2.one_lt.le, h2⟩
  · refine le_trans ?_ (primorial_le_four_pow (2 * n / 3))
    refine (Finset.prod_le_prod fun p hp => (?_ : f p ≤ p)).trans ?_
    · obtain ⟨h1, h2⟩ := Finset.mem_filter.1 hp
      refine (pow_right_mono₀ (Finset.mem_filter.1 h1).2.one_lt.le ?_).trans (pow_one p).le
      exact Nat.factorization_choose_le_one (sqrt_lt'.mp <| not_le.1 h2)
    refine Finset.prod_le_prod_of_subset_of_one_le (Finset.filter_subset _ _) ?_
    exact fun p hp _ => (Finset.mem_filter.1 hp).2.one_lt.le

-- If no prime lies in `(n + 1, 2 * n]`, then `centralBinom n` is small.
-- The only large prime factor can be `n + 1` (with multiplicity `≤ 1`).
open Nat in
private theorem centralBinom_le' (n : ℕ) (n_large : 2 < n)
    (no_prime : ∀ p : ℕ, p.Prime → n + 1 < p → 2 * n < p) :
    Nat.centralBinom n ≤ (2 * n) ^ (Nat.sqrt (2 * n) + 1) * 4 ^ (2 * n / 3) := by
  have hIco : ∏ p ∈ Finset.Ico (2 * n / 3 + 1) (2 * n + 1),
      p ^ (Nat.centralBinom n).factorization p
      = (n + 1) ^ (Nat.centralBinom n).factorization (n + 1) := by
    apply Finset.prod_eq_single_of_mem (n + 1)
    · rw [Finset.mem_Ico]; omega
    · intro p hp hpne
      rw [Finset.mem_Ico] at hp
      rcases em p.Prime with hpp | hpp
      · rcases Nat.lt_or_ge n p with hpn | hpn
        · exact absurd (no_prime p hpp (by omega)) (by omega)
        · rw [factorization_centralBinom_of_two_mul_self_lt_three_mul n_large hpn (by omega),
            pow_zero]
      · rw [factorization_eq_zero_of_not_prime _ hpp, pow_zero]
  have key : Nat.centralBinom n ≤ (n + 1) *
      ∏ p ∈ Finset.range (2 * n / 3 + 1), p ^ (Nat.centralBinom n).factorization p := by
    conv_lhs => rw [← prod_pow_factorization_centralBinom n, Finset.range_eq_Ico,
      ← Finset.prod_Ico_consecutive _ (Nat.zero_le _) (show 2 * n / 3 + 1 ≤ 2 * n + 1 by omega)]
    rw [← Finset.range_eq_Ico, hIco, mul_comm (n + 1)]
    apply Nat.mul_le_mul_left
    calc (n + 1) ^ (Nat.centralBinom n).factorization (n + 1)
        ≤ (n + 1) ^ 1 := by
          apply Nat.pow_le_pow_right (by omega)
          rw [Nat.centralBinom_eq_two_mul_choose]
          exact Nat.factorization_choose_le_one (by nlinarith)
      _ = n + 1 := pow_one _
  calc Nat.centralBinom n
      ≤ (n + 1) * ∏ p ∈ Finset.range (2 * n / 3 + 1),
          p ^ (Nat.centralBinom n).factorization p := key
    _ ≤ (2 * n) * ((2 * n) ^ Nat.sqrt (2 * n) * 4 ^ (2 * n / 3)) :=
        Nat.mul_le_mul (by omega) (prod_small_le n n_large)
    _ = (2 * n) ^ (Nat.sqrt (2 * n) + 1) * 4 ^ (2 * n / 3) := by
        rw [pow_succ]; ring

-- For `n ≥ 512` there is a prime `p` with `n + 1 < p ≤ 2 * n`.
open Nat in
private theorem exists_prime_eventually (n : ℕ) (n_large : 512 ≤ n) :
    ∃ p : ℕ, p.Prime ∧ n + 1 < p ∧ p ≤ 2 * n := by
  have H : 4 ^ n < n * n.centralBinom := Nat.four_pow_lt_mul_centralBinom n (by omega)
  contrapose! H
  have hb : Nat.centralBinom n ≤ (2 * n) ^ (Nat.sqrt (2 * n) + 1) * 4 ^ (2 * n / 3) :=
    centralBinom_le' n (by omega) H
  calc n * n.centralBinom
      ≤ n * ((2 * n) ^ (Nat.sqrt (2 * n) + 1) * 4 ^ (2 * n / 3)) := Nat.mul_le_mul_left _ hb
    _ = n * (2 * n) ^ (Nat.sqrt (2 * n) + 1) * 4 ^ (2 * n / 3) := by ring
    _ ≤ 4 ^ n := my_bertrand_inequality n_large

/-- For `3 ≤ n` there is a prime `p` with `n + 1 < p ≤ 2 * n`.
For `n < 512` this is covered by an explicit list of primes; for `n ≥ 512`
it follows from `exists_prime_eventually`. -/
private theorem exists_prime_gt_succ_le_two_mul (n : ℕ) (hn : 3 ≤ n) :
    ∃ p, Nat.Prime p ∧ n + 1 < p ∧ p ≤ 2 * n := by
  rcases Nat.lt_or_ge n 512 with h | h
  · rcases Nat.lt_or_ge n 4 with ha | ha
    · exact ⟨5, by norm_num, by omega, by omega⟩
    rcases Nat.lt_or_ge n 6 with hb | hb
    · exact ⟨7, by norm_num, by omega, by omega⟩
    rcases Nat.lt_or_ge n 10 with hc | hc
    · exact ⟨11, by norm_num, by omega, by omega⟩
    rcases Nat.lt_or_ge n 12 with hd | hd
    · exact ⟨13, by norm_num, by omega, by omega⟩
    rcases Nat.lt_or_ge n 22 with he | he
    · exact ⟨23, by norm_num, by omega, by omega⟩
    rcases Nat.lt_or_ge n 36 with hf | hf
    · exact ⟨37, by norm_num, by omega, by omega⟩
    rcases Nat.lt_or_ge n 70 with hg | hg
    · exact ⟨71, by norm_num, by omega, by omega⟩
    rcases Nat.lt_or_ge n 136 with hi | hi
    · exact ⟨137, by norm_num, by omega, by omega⟩
    rcases Nat.lt_or_ge n 262 with hj | hj
    · exact ⟨263, by norm_num, by omega, by omega⟩
    exact ⟨523, by norm_num, by omega, by omega⟩
  · exact exists_prime_eventually n h

/--
**Catalan numbers other than $1$ are not perfect powers.** For every natural number $n \ge 2$, the
$n$-th Catalan number $C_n$ is not a perfect power: there are no natural numbers $m$ and $k$
with $k \ge 2$ and $C_n = m^k$.

The proof of Checcoli and D'Adderio checks small cases directly, and for $n \ge 6$ uses a
Ramanujan prime $p$ with $n + 2 \le p < 2n$, which divides $C_n$ exactly once, so $C_n = m^k$
with $k \ge 2$ is impossible.

Proves `Wanted` entry `catalan_not_perfect_power`.

Source: Nathaniel Benjamin, Grant Fickes, Eugene Fiorini,
Edgar Jaramillo Rodriguez, Eric Jovinelly, and Tony W. H. Wong,
"Primes and Perfect Powers in the Catalan Triangle,"
Journal of Integer Sequences 22 (2019), Article 19.7.6,
Theorem [Checcoli–D'Adderio] (label `c_nn not power`), lines 148–150,
https://cs.uwaterloo.ca/journals/JIS/VOL22/Fiorini/fiorini3.tex
-/
theorem catalan_not_perfect_power
    (n : ℕ) (hn : 2 ≤ n) :
    ¬ ∃ m k : ℕ, 2 ≤ k ∧ catalan n = m ^ k := by
  rintro ⟨m, k, hk, hmk⟩
  rcases Nat.lt_or_ge n 3 with hlt | hn3
  · -- `n = 2`: `catalan 2 = 2` is not a perfect power.
    interval_cases n
    rw [catalan_two] at hmk
    rcases Nat.lt_or_ge m 2 with hm | hm
    · interval_cases m
      · rw [zero_pow (show k ≠ 0 by omega)] at hmk; exact absurd hmk (by norm_num)
      · rw [one_pow] at hmk; exact absurd hmk (by norm_num)
    · have h4 : (4 : ℕ) ≤ m ^ k :=
        le_trans (by norm_num : (4 : ℕ) ≤ 2 ^ 2)
          (le_trans (Nat.pow_le_pow_right (by norm_num) hk) (Nat.pow_le_pow_left hm k))
      omega
  · -- `n ≥ 3`: pick a prime `n + 1 < p ≤ 2 * n`; then `v_p (catalan n) = 1`.
    obtain ⟨p, hp, hlo, hhi⟩ := exists_prime_gt_succ_le_two_mul n hn3
    have hcb : Nat.centralBinom n = (n + 1) * m ^ k := by
      rw [← succ_mul_catalan_eq_centralBinom n, hmk]
    have hmk0 : m ^ k ≠ 0 := by
      rw [← hmk]
      intro h
      have hsucc := succ_mul_catalan_eq_centralBinom n
      rw [h, mul_zero] at hsucc
      exact (Nat.centralBinom_pos n).ne' hsucc.symm
    have hcbne : Nat.centralBinom n ≠ 0 := (Nat.centralBinom_pos n).ne'
    have hle1 : (Nat.centralBinom n).factorization p ≤ 1 := by
      rw [Nat.centralBinom_eq_two_mul_choose]
      exact Nat.factorization_choose_le_one (by nlinarith [hlo])
    have hdvd : p ∣ Nat.centralBinom n := by
      rw [Nat.centralBinom_eq_two_mul_choose]
      exact hp.dvd_choose (by omega) (by omega) hhi
    have hpos : 0 < (Nat.centralBinom n).factorization p :=
      hp.factorization_pos_of_dvd hcbne hdvd
    have hcard1 : (Nat.centralBinom n).factorization p = 1 := by omega
    have h_np1_zero : (n + 1).factorization p = 0 := by
      apply Nat.factorization_eq_zero_of_not_dvd
      intro h
      have := Nat.le_of_dvd (by omega) h
      omega
    have hfmul : ((n + 1) * m ^ k).factorization p
        = (n + 1).factorization p + (m ^ k).factorization p := by
      rw [Nat.factorization_mul (by omega) hmk0, Finsupp.add_apply]
    have hfpow : (m ^ k).factorization p = k * m.factorization p := by
      rw [Nat.factorization_pow, Finsupp.smul_apply, smul_eq_mul]
    have hone : k * m.factorization p = 1 := by
      have : (1 : ℕ) = k * m.factorization p := by
        rw [← hcard1, hcb, hfmul, h_np1_zero, hfpow, zero_add]
      omega
    have hkdvd : k ∣ 1 := ⟨m.factorization p, hone.symm⟩
    have := Nat.le_of_dvd one_pos hkdvd
    omega

end MetaMathlibExt
