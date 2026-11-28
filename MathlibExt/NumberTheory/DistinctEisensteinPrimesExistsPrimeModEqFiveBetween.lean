/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Data.Nat.Prime.Basic
import Mathlib.NumberTheory.ArithmeticFunction.Misc
import Mathlib.NumberTheory.Chebyshev
import Mathlib.Analysis.SpecialFunctions.Log.Sum
import Mathlib.Data.Nat.Choose.Central
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import MathlibExt.NumberTheory.CentralBinomLog
import MathlibExt.NumberTheory.DistinctEisensteinPrimes
import MathlibExt.NumberTheory.PrimeInterval.Breusch.Theta

/-!
# Breusch's theorem for primes congruent to five modulo six

There is a prime congruent to five modulo six strictly between `x` and `2 * x` for `x ≥ 7`.

Source: Elchin Hasanalizade, "Sums of Distinct Eisenstein Primes", *INTEGERS* 24 (2024),
Article A57, Lemma 2 (citing Breusch).
-/

set_option autoImplicit false

@[expose] public section

namespace MathlibExt.NumberTheory.DistinctEisensteinPrimesWanted

open Finset ArithmeticFunction MathlibExt.NumberTheory.CharModThree

private def mask (n : ℕ) : ℝ := if n % 3 = 0 then 0 else 1

private lemma mask_mul (m n : ℕ) : mask (m * n) = mask m * mask n := by
  simp only [mask, Nat.mul_mod m n]
  have hm := Nat.mod_lt m (by decide : 0 < 3)
  have hn := Nat.mod_lt n (by decide : 0 < 3)
  interval_cases m % 3 <;> interval_cases n % 3 <;> norm_num

private lemma sum_mask (n : ℕ) :
    ∑ i ∈ Ioc 0 n, mask i = (n : ℝ) - (n / 3 : ℕ) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [sum_Ioc_succ_top (Nat.zero_le _), ih]
    have hn := Nat.mod_lt n (by decide : 0 < 3)
    have hdiv := Nat.div_add_mod n 3
    interval_cases n % 3
    all_goals simp only [mask]
    all_goals split_ifs <;> try omega
    all_goals first
      | have hd : (n + 1) / 3 = n / 3 := by omega
        simp only [hd, Nat.cast_add, Nat.cast_one]; ring
      | have hd : (n + 1) / 3 = n / 3 + 1 := by omega
        simp only [hd, Nat.cast_add, Nat.cast_one]; ring

private lemma convolution (w : ℕ → ℝ) (hw : w 0 = 0)
    (hmul : ∀ a b, w (a * b) = w a * w b) (N : ℕ) :
    ∑ i ∈ Ioc 0 N, w i * Real.log i =
      ∑ d ∈ Ioc 0 N, w d * Λ d * ∑ i ∈ Ioc 0 (N / d), w i := by
  let f : ArithmeticFunction ℝ := ⟨fun d => w d * Λ d, by simp⟩
  let g : ArithmeticFunction ℝ := ⟨w, hw⟩
  have term (n : ℕ) : (f * g) n = w n * Real.log n := by
    rw [ArithmeticFunction.mul_apply, ← ArithmeticFunction.vonMangoldt_sum,
      ← Nat.sum_divisorsAntidiagonal (fun i _ => Λ i), Finset.mul_sum]
    refine sum_congr rfl fun ⟨a, b⟩ hab => ?_
    change w a * Λ a * w b = w n * Λ a
    rw [← (Nat.mem_divisorsAntidiagonal.mp hab).1, hmul]
    ring
  simpa only [term, f, g, ArithmeticFunction.coe_mk] using
    ArithmeticFunction.sum_Ioc_mul_eq_sum_sum f g N

private def coeff (m d : ℕ) : ℝ :=
  mask d * ((6 * m / d : ℕ) - 2 * (3 * m / d : ℕ) -
    (2 * m / d : ℕ) + 2 * (m / d : ℕ) : ℝ) -
    chi d * (if 6 * m / d % 3 = 1 then 1 else 0)

private lemma quotient (m d k : ℕ) (hk : 0 < k) : (k * m / d) / k = m / d := by
  rw [Nat.div_div_eq_div_mul, Nat.mul_comm d k, Nat.mul_div_mul_left _ _ hk]

private lemma coeff_cases (m d : ℕ) :
    coeff m d ≤ 2 ∧ (0 < coeff m d → d % 3 = 2 ∧ 6 * m / d % 6 = 1) := by
  have h2 := quotient (3 * m) d 2 (by decide)
  have h3 := quotient (2 * m) d 3 (by decide)
  have h6 := quotient m d 6 (by decide)
  norm_num [← Nat.mul_assoc] at h2 h3
  have hf (n : ℕ) : ((n : ℝ) - 2 * (n / 2 : ℕ) - (n / 3 : ℕ) +
      2 * (n / 6 : ℕ)) =
      if n % 6 = 1 then 1 else if n % 6 = 4 then -1 else 0 := by
    have hq2 : n / 2 = 3 * (n / 6) + n % 6 / 2 := by omega
    have hq3 : n / 3 = 2 * (n / 6) + n % 6 / 3 := by omega
    have hq : n = 6 * (n / 6) + n % 6 := (Nat.div_add_mod n 6).symm
    nth_rw 1 [hq]
    rw [hq2, hq3]
    push_cast
    have hr := Nat.mod_lt n (by decide : 0 < 6)
    interval_cases n % 6 <;> norm_num <;> ring
  have he := hf (6 * m / d)
  rw [h2, h3, h6] at he
  unfold coeff mask chi
  rw [he]
  have hr := Nat.mod_lt d (by decide : 0 < 3)
  have hq := Nat.mod_lt (6 * m / d) (by decide : 0 < 6)
  have hmod : 6 * m / d % 3 = 6 * m / d % 6 % 3 := by omega
  interval_cases d % 3 <;> interval_cases 6 * m / d % 6
  all_goals simp_all
  all_goals norm_num

private noncomputable def weightedLog (n : ℕ) : ℝ := ∑ i ∈ Ioc 0 n, mask i * Real.log i

private lemma weightedLog_eq (n : ℕ) : weightedLog n = Real.log n.factorial -
    Real.log (n / 3).factorial - (n / 3 : ℕ) * Real.log 3 := by
  have hs : (Ioc 0 n).filter (fun i => i % 3 = 0) =
      (Ioc 0 (n / 3)).image (3 * ·) := by
    ext i
    simp only [mem_filter, mem_Ioc, mem_image]
    constructor
    · rintro ⟨⟨hi0, hin⟩, hi⟩
      obtain ⟨k, hk⟩ := Nat.dvd_of_mod_eq_zero hi
      refine ⟨k, ⟨by omega, ?_⟩, hk.symm⟩
      rw [Nat.le_div_iff_mul_le (by decide)]
      omega
    · rintro ⟨k, ⟨hk0, hkn⟩, rfl⟩
      rw [Nat.le_div_iff_mul_le (by decide)] at hkn
      exact ⟨⟨by omega, by omega⟩, by omega⟩
  have htotal : weightedLog n = (∑ i ∈ Ioc 0 n, Real.log i) -
      ∑ i ∈ (Ioc 0 n).filter (fun i => i % 3 = 0), Real.log i := by
    rw [weightedLog, sum_filter, ← sum_sub_distrib]
    apply sum_congr rfl
    intro i hi
    simp only [mask]
    split_ifs <;> simp
  rw [htotal, hs, sum_image (by intro i hi j hj hij; dsimp at hij; omega)]
  have hlog (i : ℕ) (hi : i ∈ Ioc 0 (n / 3)) :
      Real.log (3 * i : ℕ) = Real.log 3 + Real.log i := by
    push_cast
    exact Real.log_mul (by norm_num) (by exact_mod_cast (mem_Ioc.mp hi).1.ne')
  rw [sum_congr rfl hlog, sum_add_distrib, sum_const, Nat.card_Ioc,
    Nat.sub_zero, nsmul_eq_mul, Real.sum_log_eq_log_factorial,
    Real.sum_log_eq_log_factorial]
  ring

private lemma coeff_sum (m : ℕ) : ∑ d ∈ Ioc 0 (6 * m), coeff m d * Λ d =
    weightedLog (6 * m) - 2 * weightedLog (3 * m) -
      ∑ i ∈ Ioc 0 (6 * m), chi i * Real.log i := by
  have h6 := convolution mask (by simp [mask]) mask_mul (6 * m)
  have h3 := convolution mask (by simp [mask]) mask_mul (3 * m)
  have hc := convolution chi (by norm_num [chi]) chi_mul (6 * m)
  simp_rw [sum_mask] at h6 h3
  simp_rw [sum_chi] at hc
  have hquot6 (d : ℕ) : 6 * m / d / 3 = 2 * m / d := by
    simpa [← Nat.mul_assoc] using quotient (2 * m) d 3 (by decide)
  have hquot3 (d : ℕ) : 3 * m / d / 3 = m / d := quotient m d 3 (by decide)
  simp_rw [hquot6] at h6
  simp_rw [hquot3] at h3
  have hext : ∑ d ∈ Ioc 0 (3 * m), mask d * Λ d *
      ((3 * m / d : ℕ) - (m / d : ℕ) : ℝ) =
      ∑ d ∈ Ioc 0 (6 * m), mask d * Λ d *
        ((3 * m / d : ℕ) - (m / d : ℕ) : ℝ) := by
    apply sum_subset (Ioc_subset_Ioc_right (by omega))
    intro d hd hnot
    have hd0 : 0 < d := (mem_Ioc.mp hd).1
    have hd3 : 3 * m < d := by simp only [mem_Ioc, not_and, not_le] at hnot; omega
    simp [Nat.div_eq_of_lt hd3, Nat.div_eq_of_lt (show m < d by omega)]
  rw [hext] at h3
  change weightedLog (6 * m) = _ at h6
  change weightedLog (3 * m) = _ at h3
  rw [h6, h3, hc, mul_sum, ← sum_sub_distrib, ← sum_sub_distrib]
  apply sum_congr rfl
  intro d hd
  unfold coeff
  ring

private lemma weightedLog_lower (m : ℕ) (hm : 1 ≤ m) :
    4 * m * Real.log 2 - Real.log (6 * m + 1 : ℕ) ≤
      weightedLog (6 * m) - 2 * weightedLog (3 * m) := by
  have hb : (0 : ℝ) < (3 * m).centralBinom := by
    exact_mod_cast Nat.centralBinom_pos (3 * m)
  have hb1 : (0 : ℝ) < m.centralBinom := by exact_mod_cast Nat.centralBinom_pos m
  have hl := Nat.four_pow_le_two_mul_add_one_mul_centralBinom (3 * m)
  have hu := Nat.centralBinom_le_four_pow m
  have hlr := Real.log_le_log (show (0 : ℝ) < (4 : ℕ) ^ (3 * m) by positivity)
    (show ((4 : ℕ) ^ (3 * m) : ℝ) ≤
      ((2 * (3 * m) + 1) * (3 * m).centralBinom : ℕ) by exact_mod_cast hl)
  have hur := Real.log_le_log (show (0 : ℝ) < m.centralBinom from hb1)
    (show (m.centralBinom : ℝ) ≤ (4 ^ m : ℕ) by exact_mod_cast hu)
  push_cast at hlr hur
  rw [Real.log_pow, Real.log_mul (by positivity) hb.ne',
    MetaMathlibExt.log_centralBinom] at hlr
  rw [Real.log_pow, MetaMathlibExt.log_centralBinom] at hur
  have hlog4 : Real.log 4 = 2 * Real.log 2 := by
    rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]
    norm_num
  rw [weightedLog_eq, weightedLog_eq, show 6 * m / 3 = 2 * m by omega,
    show 3 * m / 3 = m by omega]
  norm_num [← Nat.mul_assoc, Nat.mul_div_cancel_left] at hlr ⊢
  rw [hlog4] at hlr hur
  have helog : 2 * (3 * (m : ℝ)) + 1 = 6 * m + 1 := by ring
  rw [helog] at hlr
  linarith

private lemma coeff_sum_lower (m : ℕ) (hm : 1 ≤ m) :
    4 * m * Real.log 2 - Real.log (6 * m + 1 : ℕ) - Real.log (6 * m : ℕ) ≤
      ∑ d ∈ Ioc 0 (6 * m), coeff m d * Λ d := by
  rw [coeff_sum]
  have ht := sum_chi_log (6 * m)
  have hmod : 6 * m % 3 = 0 := by omega
  simp only [hmod, Nat.reduceEqDiff, ite_false] at ht
  have hn : 0 ≤ Real.log (6 * m : ℕ) :=
    Real.log_nonneg (by exact_mod_cast (show 1 ≤ 6 * m by omega))
  linarith [weightedLog_lower m hm]

private lemma coeff_sum_upper (m x : ℕ) (hm : 1 ≤ m) (hx : x ≤ 3 * m + 2)
    (hxm : 3 * m ≤ x)
    (hno : ¬ ∃ p : ℕ, p.Prime ∧ x < p ∧ p < 2 * x ∧ p % 6 = 5) :
    ∑ d ∈ Ioc 0 (6 * m), coeff m d * Λ d ≤
      2 * Chebyshev.psi (6 * m / 7 : ℕ) +
      2 * (Chebyshev.psi (6 * m : ℕ) - Chebyshev.theta (6 * m : ℕ)) +
      4 * Real.log (6 * m : ℕ) := by
  have hpoint (d : ℕ) (hd : d ∈ Ioc 0 (6 * m)) : coeff m d * Λ d ≤
      2 * (if d ≤ 6 * m / 7 then Λ d else 0) +
      2 * (if ¬ d.Prime then Λ d else 0) +
      2 * (if d = 3 * m + 1 then Λ d else 0) +
      2 * (if d = 3 * m + 2 then Λ d else 0) := by
    have hnn : 0 ≤ Λ d := vonMangoldt_nonneg
    have hc := coeff_cases m d
    have hbound := mul_le_mul_of_nonneg_right hc.1 hnn
    by_cases hs : d ≤ 6 * m / 7
    · simp only [hs, ite_true]
      split_ifs <;> linarith only [hbound, hnn]
    by_cases hp : d.Prime
    · by_cases hc0 : coeff m d ≤ 0
      · have hneg := mul_nonpos_of_nonpos_of_nonneg hc0 hnn
        split_ifs <;> linarith only [hneg, hnn]
      have hr := hc.2 (lt_of_not_ge hc0)
      have hr3 := hr.1
      have hrq := hr.2
      have hdpos : 0 < d := (mem_Ioc.mp hd).1
      have hdle : d ≤ 6 * m := (mem_Ioc.mp hd).2
      have hq : 6 * m / d < 7 := by
        rw [Nat.div_lt_iff_lt_mul hdpos]
        have hmul : 6 * m < d * 7 :=
          (Nat.div_lt_iff_lt_mul (by decide : 0 < 7)).mp (Nat.lt_of_not_ge hs)
        omega
      have hone (q : ℕ) (hq : q < 7) (hr : q % 6 = 1) : q = 1 := by omega
      have hq1 : 6 * m / d = 1 := hone _ hq hrq
      have hdlo : 3 * m < d := by
        have he := Nat.div_add_mod (6 * m) d
        have hr := Nat.mod_lt (6 * m) hdpos
        rw [hq1] at he
        omega
      have hde : d ≠ 6 * m := by
        intro he
        have htwo : 2 ∣ d := by rw [he]; omega
        have := (Nat.prime_dvd_prime_iff_eq Nat.prime_two hp).mp htwo
        omega
      have hdlt : d < 6 * m := by omega
      have hr6 : d % 6 = 5 := by have := hp.eq_two_or_odd; omega
      have hdx : d ≤ x := by
        by_contra h
        exact hno ⟨d, hp, by omega, by omega, hr6⟩
      have hstrip : d = 3 * m + 1 ∨ d = 3 * m + 2 := by omega
      have heither : Λ d ≤ (if d = 3 * m + 1 then Λ d else 0) +
          (if d = 3 * m + 2 then Λ d else 0) := by
        rcases hstrip with rfl | rfl <;> simp
      simp only [hs, hp, not_true_eq_false, ite_false]
      linarith only [hbound, heither]
    · simp only [hs, hp, not_false_eq_true, ite_true, ite_false]
      split_ifs <;> linarith only [hbound, hnn]
  have hsum := sum_le_sum hpoint
  rw [sum_add_distrib, sum_add_distrib, sum_add_distrib, ← mul_sum, ← mul_sum,
    ← mul_sum, ← mul_sum] at hsum
  have hsmall : ∑ d ∈ Ioc 0 (6 * m), (if d ≤ 6 * m / 7 then Λ d else 0) =
      Chebyshev.psi (6 * m / 7 : ℕ) := by
    have hf : (Ioc 0 (6 * m)).filter (· ≤ 6 * m / 7) = Ioc 0 (6 * m / 7) := by
      ext d
      simp
      omega
    rw [← sum_filter, hf, Chebyshev.psi, Nat.floor_natCast]
  have hnprime := Chebyshev.psi_sub_theta_eq_sum_not_prime (6 * m : ℕ)
  rw [Nat.floor_natCast, sum_filter] at hnprime
  have hs1 : ∑ d ∈ Ioc 0 (6 * m), (if d = 3 * m + 1 then Λ d else 0) = Λ (3 * m + 1) := by
    rw [sum_ite_eq']
    simp [mem_Ioc]
    omega
  have hs2 : ∑ d ∈ Ioc 0 (6 * m), (if d = 3 * m + 2 then Λ d else 0) = Λ (3 * m + 2) := by
    rw [sum_ite_eq']
    simp [mem_Ioc]
    omega
  rw [hsmall, ← hnprime, hs1, hs2] at hsum
  have hl1 : Λ (3 * m + 1) ≤ Real.log (6 * m : ℕ) :=
    vonMangoldt_le_log.trans (Real.log_le_log (by positivity)
      (by exact_mod_cast (show 3 * m + 1 ≤ 6 * m by omega)))
  have hl2 : Λ (3 * m + 2) ≤ Real.log (6 * m : ℕ) :=
    vonMangoldt_le_log.trans (Real.log_le_log (by positivity)
      (by exact_mod_cast (show 3 * m + 2 ≤ 6 * m by omega)))
  linarith

open MathlibExt.NumberTheory.BreuschWanted.Internal in
private lemma log_small (z : ℝ) (hz : (10 ^ 7 : ℝ) ≤ z) : Real.log z ≤ 0.00006 * z := by
  have hs : (100 : ℝ) ≤ Real.sqrt z := by
    rw [← Real.sqrt_sq (by norm_num : (0 : ℝ) ≤ 100)]
    apply Real.sqrt_le_sqrt
    norm_num at hz ⊢
    linarith
  have hsq := Real.sq_sqrt (show 0 ≤ z by linarith)
  have hmul := mul_le_mul_of_nonneg_right hs (Real.sqrt_nonneg z)
  have hlog := log_le_sqrt06 z hz
  nlinarith

open MathlibExt.NumberTheory.BreuschWanted.Internal in
private lemma large (x : ℕ) (hx : 10000000 ≤ x) :
    ∃ p : ℕ, p.Prime ∧ x < p ∧ p < 2 * x ∧ p % 6 = 5 := by
  by_contra hno
  let m := x / 3
  have hm : 1 ≤ m := by dsimp [m]; omega
  have hxm : 3 * m ≤ x := by dsimp [m]; omega
  have hxhi : x ≤ 3 * m + 2 := by dsimp [m]; omega
  have hN : (10 ^ 7 : ℝ) ≤ (6 * m : ℕ) := by
    exact_mod_cast (show 10 ^ 7 ≤ 6 * m by dsimp [m]; omega)
  have hN1 : (1 : ℝ) ≤ (6 * m : ℕ) := by linarith
  have hs1 : (1 : ℝ) ≤ (6 * m / 7 : ℕ) := by
    exact_mod_cast (show 1 ≤ 6 * m / 7 by dsimp [m]; omega)
  have hsle : (6 * m / 7 : ℕ) ≤ (6 * m : ℕ) / (7 : ℝ) := by
    rw [le_div_iff₀ (by norm_num)]
    exact_mod_cast Nat.div_mul_le_self (6 * m) 7
  have hsN : (6 * m / 7 : ℕ) ≤ (6 * m : ℕ) := by
    exact_mod_cast Nat.div_le_self (6 * m) 7
  have hlogN := log_le_sqrt06 (6 * m : ℕ) hN
  have hsq := Real.sq_sqrt (show (0 : ℝ) ≤ (6 * m : ℕ) by positivity)
  have hlogpos : 0 ≤ Real.log (6 * m : ℕ) := Real.log_nonneg hN1
  have hlows := coeff_sum_lower m hm
  have hupps := coeff_sum_upper m x hm hxhi hxm hno
  have hpsi := Chebyshev.psi_le hs1
  have he := Chebyshev.psi_sub_theta_le hN1
  have hpsi' : Chebyshev.psi (6 * m / 7 : ℕ) ≤
      Real.log 4 * ((6 * m : ℕ) / (7 : ℝ)) +
        2 * Real.sqrt (6 * m : ℕ) * Real.log (6 * m : ℕ) := by
    refine hpsi.trans ?_
    gcongr
  have hlogsmall := log_small (6 * m : ℕ) hN
  have hlogsmall' := log_small (6 * m + 1 : ℕ) (by push_cast; push_cast at hN; linarith)
  have hlog4 : Real.log 4 = 2 * Real.log 2 := by
    rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]
    norm_num
  have herr : 8 * Real.sqrt (6 * m : ℕ) * Real.log (6 * m : ℕ) ≤
      0.048 * (6 * m : ℕ) := by
    nlinarith [mul_le_mul_of_nonneg_left hlogN (Real.sqrt_nonneg (6 * m : ℕ))]
  rw [hlog4] at hpsi'
  have hl2 := log2_gt
  have hmain : (4 * m - 24 * m / 7 : ℝ) * Real.log 2 ≥ (4 * m - 24 * m / 7 : ℝ) * 0.69 := by
    apply mul_le_mul_of_nonneg_left (by linarith)
    have hm0 : (0 : ℝ) ≤ m := by positivity
    linarith
  push_cast at hlows hupps hpsi' he hlogsmall hlogsmall' herr hmain hN
  linarith

private def chain (lo limit : ℕ) : List ℕ → Prop
  | [] => limit ≤ lo
  | p :: ps => p.Prime ∧ p % 6 = 5 ∧ lo < p ∧ p < 2 * (lo + 1) ∧ chain (p - 1) limit ps

private lemma chain_sound (lo limit x : ℕ) (ps : List ℕ) (hc : chain lo limit ps)
    (hlo : lo < x) (hhi : x < limit) :
    ∃ p : ℕ, p.Prime ∧ x < p ∧ p < 2 * x ∧ p % 6 = 5 := by
  induction ps generalizing lo with
  | nil => simp only [chain] at hc; omega
  | cons p ps ih =>
    obtain ⟨hp, hr, hlp, hpl, hps⟩ := hc
    by_cases hxp : x < p
    · exact ⟨p, hp, hxp, by omega, hr⟩
    · exact ih (p - 1) hps (by omega)

private lemma small (x : ℕ) (hx : 7 ≤ x) (hhi : x < 10000000) :
    ∃ p : ℕ, p.Prime ∧ x < p ∧ p < 2 * x ∧ p % 6 = 5 := by
  apply chain_sound 6 10000000 x
    [11, 17, 29, 47, 83, 149, 263, 467, 839, 1499, 2693, 4817, 8669, 15581,
      28031, 50441, 90749, 163337, 293999, 529181, 952487, 1714457, 3086021,
      5554763, 9998561, 17997383] _ (by omega) hhi
  norm_num [chain]

/-- **Breusch's theorem for primes of the form $6k - 1$.** For every natural number $x \ge 7$
there is a prime $p$ with $x < p < 2x$ and $p \equiv 5 \pmod 6$, that is, a prime of the form
$6k - 1$ strictly between $x$ and $2x$.

Source: Elchin Hasanalizade, "Sums of Distinct
Eisenstein Primes", Lemma 2 (citing Breusch). -/
theorem exists_prime_modEq_five_between (x : ℕ)
    (hx : 7 ≤ x) :
    ∃ p : ℕ, p.Prime ∧ x < p ∧ p < 2 * x ∧ p % 6 = 5 := by
  by_cases h : 10000000 ≤ x
  · exact large x h
  · exact small x hx (by omega)


end MathlibExt.NumberTheory.DistinctEisensteinPrimesWanted
