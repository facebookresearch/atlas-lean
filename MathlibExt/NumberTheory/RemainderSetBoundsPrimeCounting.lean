/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Mathlib.NumberTheory.PrimeCounting
import MathlibExt.NumberTheory.PrimeCounting.ExplicitPrimeEstimates
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Analysis.SpecialFunctions.Log.Monotone
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.NumberTheory.Chebyshev

/-!
# An explicit prime-counting bound for sets of remainders

For natural numbers `n ≥ 2`, the number of primes at most `n` is at most `1.3 * n / log n`.
For `n ≥ 65536`, partial summation and explicit bounds on Chebyshev's theta function give
this estimate. Below that threshold, a kernel-checked calculation bounds the prime count
and a rational majorant for the logarithm at opposite ends of consecutive intervals.

## References

* Omkar Baraskar and Ingrid Vukusic, *Bounds for Sets of Remainders*, Journal of Integer
  Sequences 29 (2026), Article 26.1.4, Lemma 7.
* J. B. Rosser and L. Schoenfeld, *Approximate formulas for some functions of prime numbers*,
  Illinois Journal of Mathematics 6 (1962), 64–94, Corollary 1, cited in Lemma 7.
* Sadegh Nazardonyavi and Semyon Yakubovich, *Extremely Abundant Numbers and the Riemann
  Hypothesis*, Journal of Integer Sequences 17 (2014), Article 14.2.8, Lemma 8.
* P. L. Chebyshev, *Mémoire sur les nombres premiers*, Journal de Mathématiques Pures et
  Appliquées 17 (1852), 366–390, p. 379, the source of the theta estimates in Lemma 8.
* The tail argument adapts `primeCounting_upper` and `thetaIntegral_bound` from
  `MathlibExt.NumberTheory.PrimeCounting.LaishramRamanujanPrimeBound`. The theta
  estimates and the bounded primality indicator are shared in
  `MathlibExt.NumberTheory.PrimeCounting.ExplicitPrimeEstimates`.
-/

namespace MetaMathlibExt

open Real Chebyshev MeasureTheory
open ExplicitPrimeEstimates

private lemma log_4096 : log 4096 = 12 * log 2 := by
  rw [show (4096 : ℝ) = 2 ^ 12 by norm_num, log_pow]
  norm_num

private lemma theta_le_114 {x : ℝ} (hx : 4096 ≤ x) : theta x ≤ 1.14 * x := by
  have he : exp 2 ≤ (4096 : ℝ) := by
    rw [← le_log_iff_exp_le (by norm_num), log_4096]
    linarith [log_two_gt_d9]
  have h := log_div_sqrt_antitoneOn he (he.trans hx) hx
  have hs : 64 ≤ √x := (le_sqrt (by norm_num) (by linarith)).2 (by linarith)
  have hx₀ : 0 ≤ x := by linarith
  have hp : (0 : ℝ) < √x := by linarith
  change log x / √x ≤ log 4096 / √4096 at h
  rw [log_4096, show √(4096 : ℝ) = 64 by rw [Real.sqrt_eq_iff_mul_self_eq] <;> norm_num] at h
  have hlog : log x ≤ 0.13 * √x :=
    (div_le_iff₀ hp).mp (h.trans (by linarith [log_two_lt_d9]))
  have hsq := mul_self_le_mul_self (log_nonneg (by linarith : 1 ≤ x)) hlog
  have hsx : 64 * √x ≤ x := by
    calc
      _ ≤ √x * √x := mul_le_mul_of_nonneg_right hs hp.le
      _ = x := mul_self_sqrt hx₀
  nlinarith only [hlog, hsq, hsx, sq_sqrt hx₀, hx, (theta_bounds x (by linarith)).1]

-- On this interval the derivative of `0.16 * t / log t` majorizes the theta integrand.
private lemma theta_integral_le {x : ℝ} (hx : 4096 ≤ x)
    (hint : IntervalIntegrable (fun t ↦ theta t / (t * log t ^ 2)) volume 4096 x) :
    (∫ t in (4096 : ℝ)..x, theta t / (t * log t ^ 2)) ≤
      0.16 * x / log x - 0.16 * 4096 / log 4096 := by
  have hlog {t : ℝ} (ht : 4096 ≤ t) : 8.25 < log t := by
    refine lt_of_lt_of_le ?_ (log_le_log (by norm_num) ht)
    rw [log_4096]
    linarith [log_two_gt_d9]
  let f (t : ℝ) := 0.16 * t / log t
  let f' (t : ℝ) := 0.16 * (log t - 1) / log t ^ 2
  have hf' : IntervalIntegrable f' volume 4096 x := by
    apply ContinuousOn.intervalIntegrable
    intro t ht
    rw [Set.uIcc_of_le hx] at ht
    have htlog := hlog ht.1
    dsimp [f']
    fun_prop (disch := first | positivity | linarith [ht.1])
  have hf (t : ℝ) (ht : t ∈ Set.uIcc 4096 x) : HasDerivAt f (f' t) t := by
    rw [Set.uIcc_of_le hx] at ht
    have ht₀ : 0 < t := by linarith [ht.1]
    have htlog : log t ≠ 0 := by linarith [hlog ht.1]
    convert (((hasDerivAt_id t).div (hasDerivAt_log ht₀.ne') htlog).const_mul 0.16) using 1
    · ext y
      dsimp [f]
      ring
    · dsimp [f']
      field_simp
  change _ ≤ f x - f 4096
  rw [← intervalIntegral.integral_eq_sub_of_hasDerivAt hf hf']
  refine intervalIntegral.integral_mono_on hx hint hf' fun t ht ↦ ?_
  have ht₀ : 0 < t := by linarith [ht.1]
  have htlog : 0 < log t := by linarith [hlog ht.1]
  calc
    _ ≤ (1.14 * t) / (t * log t ^ 2) :=
      div_le_div_of_nonneg_right (theta_le_114 ht.1) (by positivity)
    _ = 1.14 / log t ^ 2 := by field_simp
    _ ≤ f' t := by
      dsimp [f']
      apply div_le_div_of_nonneg_right _ (sq_nonneg _)
      linarith [hlog ht.1]

private lemma primeCounting_large {x : ℝ} (hx : 65536 ≤ x) :
    (Nat.primeCounting ⌊x⌋₊ : ℝ) * log x ≤ 13 / 10 * x := by
  have hx₀ : 0 < x := by linarith
  have hx₂ : 2 ≤ x := by linarith
  have hxbase : 4096 ≤ x := by linarith
  have hlog : 0 < log x := log_pos (by linarith)
  have hlogbase : 0 < log 4096 := log_pos (by norm_num)
  have hbase := primeCounting_eq_theta_div_log_add_integral (by norm_num : (2 : ℝ) ≤ 4096)
  rw [show ⌊(4096 : ℝ)⌋₊ = 4096 by norm_num, primeCounting_4096] at hbase
  have hsmall : (∫ t in (2 : ℝ)..4096, theta t / (t * log t ^ 2)) -
      0.16 * 4096 / log 4096 ≤ 81 := by
    have : 483 * log 4096 ≤ theta 4096 + 0.16 * 4096 := by
      linarith [log_4096, log_two_lt_d9, le_theta_4096]
    apply (mul_le_mul_iff_left₀ hlogbase).mp
    field_simp at hbase ⊢
    linarith
  have hint₁ : IntervalIntegrable (fun t ↦ theta t / (t * log t ^ 2)) volume 2 4096 := by
    rw [intervalIntegrable_iff_integrableOn_Ioc_of_le (by norm_num),
      ← integrableOn_Icc_iff_integrableOn_Ioc]
    exact integrableOn_theta_div_id_mul_log_sq 4096
  have hint₂ : IntervalIntegrable (fun t ↦ theta t / (t * log t ^ 2)) volume 4096 x := by
    rw [intervalIntegrable_iff_integrableOn_Ioc_of_le hxbase,
      ← integrableOn_Icc_iff_integrableOn_Ioc]
    exact (integrableOn_theta_div_id_mul_log_sq x).mono_set (Set.Icc_subset_Icc_left (by norm_num))
  have herror : 81 * log x ≤ 0.03 * x := by
    have he : exp 1 ≤ (65536 : ℝ) := exp_one_lt_three.le.trans (by norm_num)
    have hm := log_div_self_antitoneOn he (he.trans hx) hx
    change log x / x ≤ log 65536 / 65536 at hm
    rw [div_le_div_iff₀ hx₀ (by norm_num),
      show (65536 : ℝ) = 2 ^ 16 by norm_num, log_pow] at hm
    norm_num at hm
    have hb : 16 * log 2 ≤ 12 := by linarith [log_two_lt_d9]
    linarith only [hm, mul_le_mul_of_nonneg_right hb hx₀.le, hx₀.le]
  have hsum : (∫ t in (2 : ℝ)..x, theta t / (t * log t ^ 2)) ≤ 81 + 0.16 * x / log x := by
    rw [← intervalIntegral.integral_add_adjacent_intervals hint₁ hint₂]
    linarith [theta_integral_le hxbase hint₂]
  have hsum' := mul_le_mul_of_nonneg_right hsum hlog.le
  rw [add_mul, div_mul_cancel₀ _ hlog.ne'] at hsum'
  rw [primeCounting_eq_theta_div_log_add_integral hx₂, add_mul, div_mul_cancel₀ _ hlog.ne']
  linarith [(theta_bounds_of_65536_le x hx).1]

-- Put `d = 2 ^ log₂ a` and split `a / d` as `(a + d) / (2 * d) * (2 * a) / (a + d)`.
-- Applying `log z ≤ z - 1` to each positive factor gives a rational upper bound.
private def logUpper (a : ℕ) : ℚ :=
  let d : ℚ := (2 : ℚ) ^ a.log2
  a.log2 * (693148 / 1000000) + ((a + d) / (2 * d) - 1) + (2 * a / (a + d) - 1)

private lemma log_le_logUpper {a : ℕ} (ha : 0 < a) : log a ≤ (logUpper a : ℝ) := by
  have ha₀ : (0 : ℝ) < a := by exact_mod_cast ha
  let d : ℝ := (2 : ℝ) ^ a.log2
  have hd : 0 < d := by dsimp [d]; positivity
  have hsum : 0 < (a : ℝ) + d := by positivity
  have heq : d * (((a : ℝ) + d) / (2 * d)) * (2 * a / (a + d)) = a := by
    field_simp
  have hlog : log a = a.log2 * log 2 + log ((a + d) / (2 * d)) + log (2 * a / (a + d)) := by
    conv_lhs => rw [← heq]
    rw [log_mul (by positivity) (by positivity), log_mul hd.ne' (by positivity)]
    simp [d, log_pow]
  have h₁ := log_le_sub_one_of_pos (show 0 < ((a : ℝ) + d) / (2 * d) by positivity)
  have h₂ := log_le_sub_one_of_pos (show 0 < 2 * (a : ℝ) / (a + d) by positivity)
  have h₃ := mul_le_mul_of_nonneg_left
    (show log 2 ≤ (693148 : ℝ) / 1000000 by linarith [log_two_lt_d9])
    (Nat.cast_nonneg (α := ℝ) a.log2)
  simp only [logUpper, Rat.cast_add, Rat.cast_mul, Rat.cast_div, Rat.cast_sub, Rat.cast_one,
    Rat.cast_natCast, Rat.cast_ofNat, Rat.cast_pow]
  change _ ≤ (a.log2 : ℝ) * (693148 / 1000000) + (((a : ℝ) + d) / (2 * d) - 1) +
    (2 * a / (a + d) - 1)
  linarith only [hlog, h₁, h₂, h₃]

private lemma primeCounting_le_on_block {a b n : ℕ} (ha : 3 ≤ a) (han : a ≤ n) (hnb : n < b)
    (h : (Nat.primeCounting (b - 1) : ℚ) * logUpper a ≤ 13 / 10 * a) :
    (Nat.primeCounting n : ℝ) ≤ 13 / 10 * n / log n := by
  have ha₃ : (3 : ℝ) ≤ a := by exact_mod_cast ha
  have han' : (a : ℝ) ≤ n := by exact_mod_cast han
  have ha₀ : (0 : ℝ) < a := by linarith
  have hn₀ : (0 : ℝ) < n := ha₀.trans_le han'
  have hlog : 0 < log n := log_pos (by linarith)
  have hcount : (Nat.primeCounting n : ℝ) ≤ Nat.primeCounting (b - 1) := by
    exact_mod_cast Nat.monotone_primeCounting (by omega : n ≤ b - 1)
  have hmono := log_div_self_antitoneOn (exp_one_lt_three.le.trans ha₃)
    (exp_one_lt_three.le.trans (ha₃.trans han')) han'
  have hcert : (Nat.primeCounting (b - 1) : ℝ) * (logUpper a : ℝ) ≤ 13 / 10 * a := by
    simpa only [Rat.cast_mul, Rat.cast_div, Rat.cast_ofNat, Rat.cast_natCast] using
      Rat.cast_mono (K := ℝ) h
  apply (le_div_iff₀ hlog).mpr
  apply (div_le_iff₀ hn₀).mp
  rw [mul_div_assoc]
  calc
    _ ≤ (Nat.primeCounting (b - 1) : ℝ) * (log a / a) :=
      mul_le_mul hcount hmono (by positivity) (Nat.cast_nonneg _)
    _ ≤ 13 / 10 := by
      rw [← mul_div_assoc]
      exact (div_le_iff₀ ha₀).mpr
        ((mul_le_mul_of_nonneg_left (log_le_logUpper (by omega)) (Nat.cast_nonneg _)).trans hcert)

-- Extend the running count of primes below `a` by counting the primes in `[a, b)`.
private def countThroughBlock (a b count : ℕ) : ℕ :=
  count + (List.range' a (b - a)).countP (fun p ↦ primeFlag p == 1)

private lemma countThroughBlock_eq {a b : ℕ} (hab : a ≤ b) (hb : b ≤ 65536) :
    countThroughBlock a b (Nat.primeCounting (a - 1)) = Nat.primeCounting (b - 1) := by
  rw [Nat.primeCounting_sub_one, Nat.primeCounting_sub_one]
  change (List.range a).countP _ + (List.range' a (b - a)).countP _ = (List.range b).countP _
  have hsplit : List.range a ++ List.range' a (b - a) = List.range b := by
    simpa only [List.range_eq_range', Nat.zero_add, Nat.add_sub_of_le hab] using
      (List.range'_append_1 (s := 0) (m := a) (n := b - a))
  rw [← hsplit, List.countP_append]
  congr 1
  apply List.countP_congr
  intro p hp
  obtain ⟨i, hi, rfl⟩ := List.mem_range'.mp hp
  rw [primeFlag_eq (by omega)]
  by_cases h : (a + 1 * i).Prime <;> simp [*]

private def nextBlock (a : ℕ) : ℕ := min 65536 (a + max 1 (a / 20))

-- The check succeeds only if it reaches 65536 and all intervening blocks pass.
private def checkBlocks : ℕ → ℕ → ℕ → Bool
  | 0, a, _ => a == 65536
  | fuel + 1, a, count =>
    if a = 65536 then true else
      let b := nextBlock a
      let count' := countThroughBlock a b count
      decide ((count' : ℚ) * logUpper a ≤ 13 / 10 * a) && checkBlocks fuel b count'

private lemma checkBlocks_sound (fuel : ℕ) {a count : ℕ} (ha : 3 ≤ a)
    (hc : count = Nat.primeCounting (a - 1)) (hcheck : checkBlocks fuel a count = true)
    {n : ℕ} (han : a ≤ n) (hn : n < 65536) :
    (Nat.primeCounting n : ℝ) ≤ 13 / 10 * n / log n := by
  induction fuel generalizing a count with
  | zero =>
    simp [checkBlocks] at hcheck
    omega
  | succ fuel ih =>
    have ha' : a ≠ 65536 := by omega
    have hab : a ≤ nextBlock a := le_min (by omega) (Nat.le_add_right ..)
    have hb : nextBlock a ≤ 65536 := min_le_left ..
    have hcount : countThroughBlock a (nextBlock a) count = Nat.primeCounting (nextBlock a - 1) :=
      hc ▸ countThroughBlock_eq hab hb
    simp only [checkBlocks, ite_eq_right ha', Bool.and_eq_true, decide_eq_true_eq] at hcheck
    rcases lt_or_ge n (nextBlock a) with hnb | hbn
    · exact primeCounting_le_on_block ha han hnb (hcount ▸ hcheck.1)
    · exact ih (ha.trans hab) hcount hcheck.2 hbn

set_option maxRecDepth 8192 in
set_option maxHeartbeats 1000000 in
-- Kernel reduction checks the prime counts and rational bounds for all 194 blocks.
private lemma primeCounting_small {n : ℕ} (hn₁ : 3 ≤ n) (hn₂ : n < 65536) :
    (Nat.primeCounting n : ℝ) ≤ 13 / 10 * n / log n := by
  have hcheck : checkBlocks 194 3 1 = true := by decide +kernel
  exact checkBlocks_sound 194 (by decide) (by decide) hcheck hn₁ hn₂

/-- **Upper bound $1.3\, n / \log n$ for the prime-counting function.** For every natural
number $n \ge 2$, the number $\pi(n)$ of primes at most $n$ satisfies
$\pi(n) \le 1.3\, n / \log n$, where $\log$ is the natural logarithm.

Source: Omkar Baraskar and Ingrid Vukusic, *Bounds for Sets of Remainders*, Journal of
Integer Sequences 29 (2026), Article 26.1.4, Lemma 7 (`lem:primecounting_ub`). -/
public theorem primeCounting_le_thirteen_tenths {n : ℕ} (hn : 2 ≤ n) :
    (Nat.primeCounting n : ℝ) ≤ 13 / 10 * n / Real.log n := by
  rcases lt_or_ge n 65536 with hn' | hn'
  · by_cases h : n = 2
    · subst n
      rw [show Nat.primeCounting 2 = 1 by decide, Nat.cast_one, Nat.cast_ofNat,
        le_div_iff₀ (log_pos one_lt_two)]
      linarith [log_two_lt_d9]
    · exact primeCounting_small (by omega) hn'
  · have h := primeCounting_large (by exact_mod_cast hn' : (65536 : ℝ) ≤ n)
    rw [Nat.floor_natCast] at h
    exact (le_div_iff₀ (log_pos (by exact_mod_cast (show 1 < n by omega)))).mpr h

end MetaMathlibExt
