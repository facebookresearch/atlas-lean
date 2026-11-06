/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import Mathlib.Analysis.Convex.Deriv

public import Mathlib.Analysis.SpecialFunctions.Gamma.Basic

import Mathlib.Analysis.Asymptotics.Lemmas
import Mathlib.Analysis.PSeries
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Analysis.SpecialFunctions.Gamma.BohrMollerup
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import MathlibExt.Analysis.SpecialFunctions.Gamma.Digamma

/-!
# Ramanujan's centered digamma asymptotic

This file proves the sixth-order centered digamma expansion and uses it to derive Ramanujan's
eighth-order asymptotic formula for a complex power of `(x + 1 / 2) / exp (ψ (x + 1))`.
-/

@[expose] public section

namespace MathlibExt.Analysis.Ramanujan.Part1Ch8

namespace Entry15Doublegamma

open scoped Nat Real BigOperators Interval Polynomial ContDiff
open Asymptotics Filter Finset Complex Topology MeasureTheory

noncomputable section

def chapter8RealDigamma (x : ℝ) : ℝ :=
  deriv Real.Gamma x / Real.Gamma x

private theorem ch8Entry15_digamma_ofReal {x : ℝ} (hx : 0 < x) :
    Complex.digamma (x : ℂ) = (chapter8RealDigamma x : ℂ) := by
  rw [Complex.digamma_def, logDeriv_apply, Complex.deriv_Gamma_ofReal x hx,
    Complex.Gamma_ofReal]
  unfold chapter8RealDigamma
  exact (Complex.ofReal_div _ _).symm

/-- The real digamma recurrence on the positive half-line. -/
private theorem ch8Entry15_chapter8RealDigamma_add_one {x : ℝ} (hx : 0 < x) :
    chapter8RealDigamma (x + 1) = chapter8RealDigamma x + 1 / x := by
  have hrec := Complex.digamma_apply_add_one (x : ℂ) (fun m hm => by
    have hre := congrArg Complex.re hm
    simp only [Complex.ofReal_re, Complex.neg_re, Complex.natCast_re] at hre
    have hm0 : (0 : ℝ) ≤ m := Nat.cast_nonneg m
    linarith)
  rw [← Complex.ofReal_one, ← Complex.ofReal_add] at hrec
  rw [ch8Entry15_digamma_ofReal hx,
    ch8Entry15_digamma_ofReal (by linarith : 0 < x + 1)] at hrec
  have hr : chapter8RealDigamma (x + 1) = chapter8RealDigamma x + x⁻¹ := by
    exact_mod_cast hrec
  simpa only [one_div] using hr

private theorem ch8Entry15_hasDerivAt_logGamma {x : ℝ} (hx : 0 < x) :
    HasDerivAt (Real.log ∘ Real.Gamma) (chapter8RealDigamma x) x := by
  have hdiff : DifferentiableAt ℝ Real.Gamma x :=
    Real.differentiableAt_Gamma (fun m hm => by
      have hm0 : (0 : ℝ) ≤ m := Nat.cast_nonneg m
      linarith)
  exact hdiff.hasDerivAt.log (Real.Gamma_pos_of_pos hx).ne'

private theorem ch8Entry15_slope_logGamma_add_one {x : ℝ} (hx : 0 < x) :
    slope (Real.log ∘ Real.Gamma) x (x + 1) = Real.log x := by
  rw [slope_def_field]
  have hGamma : Real.Gamma (x + 1) = x * Real.Gamma x :=
    Real.Gamma_add_one hx.ne'
  have hlog : Real.log (x * Real.Gamma x) = Real.log x + Real.log (Real.Gamma x) :=
    Real.log_mul hx.ne' (Real.Gamma_pos_of_pos hx).ne'
  simp only [Function.comp_apply]
  rw [hGamma, hlog]
  ring

/-- Secant-slope bounds for the real digamma function on `(1, ∞)`. -/
private theorem ch8Entry15_chapter8RealDigamma_bounds {x : ℝ} (hx : 1 < x) :
    Real.log (x - 1) ≤ chapter8RealDigamma x ∧ chapter8RealDigamma x ≤ Real.log x := by
  have hxm1 : 0 < x - 1 := by linarith
  have hx0 : 0 < x := by linarith
  have hder := ch8Entry15_hasDerivAt_logGamma hx0
  have hlo := Real.convexOn_log_Gamma.slope_le_of_hasDerivAt
    (show x - 1 ∈ Set.Ioi (0 : ℝ) by exact hxm1)
    (show x ∈ Set.Ioi (0 : ℝ) by exact hx0) (by linarith) hder
  have hhi := Real.convexOn_log_Gamma.le_slope_of_hasDerivAt
    (show x ∈ Set.Ioi (0 : ℝ) by exact hx0)
    (show x + 1 ∈ Set.Ioi (0 : ℝ) by exact add_pos hx0 zero_lt_one)
    (by linarith) hder
  have hslo := ch8Entry15_slope_logGamma_add_one hxm1
  rw [show (x - 1) + 1 = x by ring] at hslo
  rw [hslo] at hlo
  rw [ch8Entry15_slope_logGamma_add_one hx0] at hhi
  exact ⟨hlo, hhi⟩

/-- The real digamma function differs from `log` by a term tending to zero at infinity. -/
private theorem ch8Entry15_tendsto_chapter8RealDigamma_sub_log :
    Tendsto (fun x : ℝ => chapter8RealDigamma x - Real.log x) atTop (𝓝 0) := by
  have hlo : Tendsto (fun x : ℝ => Real.log (x - 1) - Real.log x) atTop (𝓝 0) := by
    simpa only [sub_eq_add_neg] using Real.tendsto_log_comp_add_sub_log (-1)
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' hlo tendsto_const_nhds ?_ ?_
  · filter_upwards [eventually_gt_atTop (1 : ℝ)] with x hx
    linarith [ch8Entry15_chapter8RealDigamma_bounds hx |>.1]
  · filter_upwards [eventually_gt_atTop (1 : ℝ)] with x hx
    linarith [ch8Entry15_chapter8RealDigamma_bounds hx |>.2]

private def ch8Entry15_logTaylor (u : ℝ) : ℝ :=
  u - u ^ 2 / 2 + u ^ 3 / 3 - u ^ 4 / 4 + u ^ 5 / 5 - u ^ 6 / 6 +
    u ^ 7 / 7 - u ^ 8 / 8

private def ch8Entry15_rationalStep (u : ℝ) : ℝ :=
  u / (1 + u / 2) + 1 / 24 * (u ^ 2 - u ^ 2 / (1 + u) ^ 2) -
    7 / 960 * (u ^ 4 - u ^ 4 / (1 + u) ^ 4) +
    31 / 8064 * (u ^ 6 - u ^ 6 / (1 + u) ^ 6)

private def ch8Entry15_rationalNumerator (u : ℝ) : ℝ :=
  1661 / 5760 + 793 / 576 * u + 5719 / 1920 * u ^ 2 + 2561 / 720 * u ^ 3 +
    19375 / 8064 * u ^ 4 + 6 / 7 * u ^ 5 + 1 / 8 * u ^ 6

private def ch8Entry15_remainder (y : ℝ) : ℝ :=
  chapter8RealDigamma (y + 1 / 2) - Real.log y - 1 / (24 * y ^ 2) +
    7 / (960 * y ^ 4) - 31 / (8064 * y ^ 6)

private def ch8Entry15_step (y : ℝ) : ℝ :=
  ch8Entry15_remainder y - ch8Entry15_remainder (y + 1)

private theorem ch8Entry15_step_eq {y : ℝ} (hy : 0 < y) :
    ch8Entry15_step y =
      Real.log (1 + 1 / y) - ch8Entry15_rationalStep (1 / y) := by
  have hyh : 0 < y + 1 / 2 := by linarith
  have hrec := ch8Entry15_chapter8RealDigamma_add_one hyh
  have harg : y + 1 + 1 / 2 = (y + 1 / 2) + 1 := by ring
  have hrec' : chapter8RealDigamma (y + 1 + 1 / 2) =
      chapter8RealDigamma (y + 1 / 2) + 1 / (y + 1 / 2) := by
    rw [harg]
    exact hrec
  have hone : 0 < 1 + 1 / y := by positivity
  have hfac : y + 1 = y * (1 + 1 / y) := by
    field_simp
  have hlog : Real.log (y + 1) - Real.log y = Real.log (1 + 1 / y) := by
    rw [hfac, Real.log_mul hy.ne' hone.ne', add_sub_cancel_left]
  unfold ch8Entry15_step ch8Entry15_remainder ch8Entry15_rationalStep
  rw [hrec', ← hlog]
  field_simp
  ring

private theorem ch8Entry15_logTaylor_sum (u : ℝ) :
    (∑ i ∈ Finset.range 8, (-u) ^ (i + 1) / ((i : ℝ) + 1)) + Real.log (1 - -u) =
      Real.log (1 + u) - ch8Entry15_logTaylor u := by
  norm_num [Finset.sum_range_succ, ch8Entry15_logTaylor]
  ring

private theorem ch8Entry15_logTaylor_bound {u : ℝ} (hu0 : 0 ≤ u) (hu : u ≤ 1 / 2) :
    |Real.log (1 + u) - ch8Entry15_logTaylor u| ≤ 2 * u ^ 9 := by
  have habs : |-u| < 1 := by
    rw [abs_neg, abs_of_nonneg hu0]
    linarith
  have h := Real.abs_log_sub_add_sum_range_le habs 8
  rw [ch8Entry15_logTaylor_sum, abs_neg, abs_of_nonneg hu0] at h
  have hden : 0 < 1 - u := by linarith
  have hp : 0 ≤ u ^ 9 := pow_nonneg hu0 9
  have hfrac : u ^ 9 / (1 - u) ≤ 2 * u ^ 9 := by
    rw [div_le_iff₀ hden]
    nlinarith
  exact h.trans hfrac

private theorem ch8Entry15_rational_identity {u : ℝ} (hu1 : u + 1 ≠ 0)
    (hu2 : u + 2 ≠ 0) :
    (ch8Entry15_logTaylor u - ch8Entry15_rationalStep u) * (u + 2) * (u + 1) ^ 6 =
      -u ^ 9 * ch8Entry15_rationalNumerator u := by
  have hu1' : 1 + u ≠ 0 := by simpa only [add_comm] using hu1
  have hu2' : 2 + u ≠ 0 := by simpa only [add_comm] using hu2
  have hhalf : 1 + u / 2 ≠ 0 := by
    intro h
    apply hu2
    field_simp at h
    linarith
  unfold ch8Entry15_logTaylor ch8Entry15_rationalStep ch8Entry15_rationalNumerator
  field_simp [hu1, hu1', hu2, hu2', hhalf]
  ring

private theorem ch8Entry15_rationalNumerator_bounds {u : ℝ} (hu0 : 0 ≤ u)
    (hu : u ≤ 1 / 2) :
    0 ≤ ch8Entry15_rationalNumerator u ∧ ch8Entry15_rationalNumerator u ≤ 12 := by
  constructor
  · unfold ch8Entry15_rationalNumerator
    positivity
  · have hu1 : u ≤ 1 := by linarith
    have h1 : u ≤ 1 := hu1
    have h2 : u ^ 2 ≤ 1 := pow_le_one₀ hu0 hu1
    have h3 : u ^ 3 ≤ 1 := pow_le_one₀ hu0 hu1
    have h4 : u ^ 4 ≤ 1 := pow_le_one₀ hu0 hu1
    have h5 : u ^ 5 ≤ 1 := pow_le_one₀ hu0 hu1
    have h6 : u ^ 6 ≤ 1 := pow_le_one₀ hu0 hu1
    unfold ch8Entry15_rationalNumerator
    norm_num at ⊢
    linarith

private theorem ch8Entry15_rationalStep_bound {u : ℝ} (hu0 : 0 ≤ u) (hu : u ≤ 1 / 2) :
    |ch8Entry15_logTaylor u - ch8Entry15_rationalStep u| ≤ 12 * u ^ 9 := by
  have hpow : 1 ≤ (u + 1) ^ 6 := one_le_pow₀ (by linarith)
  have hD : 1 ≤ (u + 2) * (u + 1) ^ 6 := by
    calc
      (1 : ℝ) = 1 * 1 := by ring
      _ ≤ (u + 2) * (u + 1) ^ 6 :=
        mul_le_mul (by linarith) hpow (by norm_num) (by linarith)
  have hDpos : 0 < (u + 2) * (u + 1) ^ 6 := lt_of_lt_of_le zero_lt_one hD
  have hid := ch8Entry15_rational_identity (u := u) (by linarith) (by linarith)
  have hq : ch8Entry15_logTaylor u - ch8Entry15_rationalStep u =
      (-u ^ 9 * ch8Entry15_rationalNumerator u) / ((u + 2) * (u + 1) ^ 6) := by
    apply (eq_div_iff hDpos.ne').2
    simpa only [mul_assoc] using hid
  have hA := ch8Entry15_rationalNumerator_bounds hu0 hu
  have hnum : -u ^ 9 * ch8Entry15_rationalNumerator u ≤ 0 :=
    mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr (pow_nonneg hu0 9)) hA.1
  rw [hq, abs_div, abs_of_nonpos hnum, abs_of_pos hDpos]
  simp only [neg_mul, neg_neg]
  apply (div_le_iff₀ hDpos).2
  calc
    u ^ 9 * ch8Entry15_rationalNumerator u ≤ u ^ 9 * 12 :=
      mul_le_mul_of_nonneg_left hA.2 (pow_nonneg hu0 9)
    _ ≤ (u ^ 9 * 12) * ((u + 2) * (u + 1) ^ 6) :=
      le_mul_of_one_le_right (by positivity) hD
    _ = 12 * u ^ 9 * ((u + 2) * (u + 1) ^ 6) := by ring

private theorem ch8Entry15_step_bound {y : ℝ} (hy : 2 ≤ y) :
    |ch8Entry15_step y| ≤ 14 / y ^ 9 := by
  have hy0 : 0 < y := by linarith
  have hu0 : 0 ≤ 1 / y := by positivity
  have hu : 1 / y ≤ (1 / 2 : ℝ) := by
    rw [div_le_iff₀ hy0]
    linarith
  rw [ch8Entry15_step_eq hy0]
  calc
    |Real.log (1 + 1 / y) - ch8Entry15_rationalStep (1 / y)| =
        |(Real.log (1 + 1 / y) - ch8Entry15_logTaylor (1 / y)) +
          (ch8Entry15_logTaylor (1 / y) - ch8Entry15_rationalStep (1 / y))| := by
            congr 1
            ring
    _ ≤ |Real.log (1 + 1 / y) - ch8Entry15_logTaylor (1 / y)| +
        |ch8Entry15_logTaylor (1 / y) - ch8Entry15_rationalStep (1 / y)| :=
      abs_add_le _ _
    _ ≤ 2 * (1 / y) ^ 9 + 12 * (1 / y) ^ 9 :=
      add_le_add (ch8Entry15_logTaylor_bound hu0 hu)
        (ch8Entry15_rationalStep_bound hu0 hu)
    _ = 14 / y ^ 9 := by
      field_simp
      ring

private theorem ch8Entry15_inv_pow_le_diff {t : ℝ} (ht : 1 ≤ t) :
    1 / t ^ 9 ≤ 256 * (1 / t ^ 8 - 1 / (t + 1) ^ 8) := by
  have ht0 : 0 < t := lt_of_lt_of_le zero_lt_one ht
  have hdiff : t ^ 7 ≤ (t + 1) ^ 8 - t ^ 8 := by
    ring_nf
    nlinarith [pow_nonneg ht0.le 1, pow_nonneg ht0.le 2, pow_nonneg ht0.le 3,
      pow_nonneg ht0.le 4, pow_nonneg ht0.le 5, pow_nonneg ht0.le 6,
      pow_nonneg ht0.le 7]
  have hpow : (t + 1) ^ 8 ≤ 256 * t ^ 8 := by
    have h : (t + 1) ^ 8 ≤ (2 * t) ^ 8 :=
      pow_le_pow_left₀ (by positivity) (by linarith) 8
    nlinarith [h]
  have hmain : (t + 1) ^ 8 ≤ 256 * t * ((t + 1) ^ 8 - t ^ 8) := by
    calc
      (t + 1) ^ 8 ≤ 256 * t ^ 8 := hpow
      _ = 256 * t * t ^ 7 := by ring
      _ ≤ 256 * t * ((t + 1) ^ 8 - t ^ 8) :=
        mul_le_mul_of_nonneg_left hdiff (by positivity)
  field_simp
  nlinarith

private theorem ch8Entry15_summable_inv_pow {y : ℝ} (hy : 2 ≤ y) :
    Summable (fun j : ℕ => 1 / (y + j) ^ 9) ∧
      ∑' j : ℕ, 1 / (y + j) ^ 9 ≤ 256 / y ^ 8 := by
  have hnonneg : ∀ j : ℕ, 0 ≤ 1 / (y + j) ^ 9 := fun j => by positivity
  have hpartial : ∀ N : ℕ, ∑ j ∈ Finset.range N, 1 / (y + j) ^ 9 ≤ 256 / y ^ 8 := by
    intro N
    calc
      ∑ j ∈ Finset.range N, 1 / (y + j) ^ 9 ≤
          ∑ j ∈ Finset.range N,
            256 * (1 / (y + j) ^ 8 - 1 / (y + (j + 1 : ℕ)) ^ 8) := by
        apply Finset.sum_le_sum
        intro j _
        have hj0 : (0 : ℝ) ≤ j := Nat.cast_nonneg j
        have h := ch8Entry15_inv_pow_le_diff (t := y + j) (by linarith)
        simpa only [Nat.cast_add, Nat.cast_one, add_assoc] using h
      _ = 256 * (1 / y ^ 8 - 1 / (y + N) ^ 8) := by
        rw [← Finset.mul_sum, Finset.sum_range_sub']
        norm_num
      _ = 256 / y ^ 8 - 256 / (y + N) ^ 8 := by ring
      _ ≤ 256 / y ^ 8 := by
        have : 0 ≤ 256 / (y + N) ^ 8 := by positivity
        linarith
  have hsum := summable_of_sum_range_le hnonneg hpartial
  exact ⟨hsum, hsum.tsum_le_of_sum_range_le hpartial⟩

private theorem ch8Entry15_remainder_tendsto :
    Tendsto ch8Entry15_remainder atTop (𝓝 0) := by
  have hshift : Tendsto (fun y : ℝ => y + 1 / 2) atTop atTop :=
    tendsto_atTop_add_const_right atTop (1 / 2) tendsto_id
  have hlog := Real.tendsto_log_comp_add_sub_log (1 / 2)
  have hbase : Tendsto
      (fun y : ℝ => chapter8RealDigamma (y + 1 / 2) - Real.log y) atTop (𝓝 0) := by
    simpa only [Function.comp_apply, sub_add_sub_cancel, add_zero] using
      (ch8Entry15_tendsto_chapter8RealDigamma_sub_log.comp hshift).add hlog
  have hinv : Tendsto (fun y : ℝ => 1 / y) atTop (𝓝 0) := by
    simpa only [one_div] using (tendsto_inv_atTop_zero :
      Tendsto (fun y : ℝ => y⁻¹) atTop (𝓝 0))
  have h := (((hbase.sub ((hinv.pow 2).const_mul (1 / 24))).add
    ((hinv.pow 4).const_mul (7 / 960))).sub ((hinv.pow 6).const_mul (31 / 8064)))
  have hfun : ch8Entry15_remainder = fun x : ℝ =>
      chapter8RealDigamma (x + 1 / 2) - Real.log x - 1 / 24 * (1 / x) ^ 2 +
        7 / 960 * (1 / x) ^ 4 - 31 / 8064 * (1 / x) ^ 6 := by
    funext x
    unfold ch8Entry15_remainder
    norm_num [one_div, mul_inv_rev, inv_pow]
    ring
  rw [hfun]
  simpa using h

private theorem ch8Entry15_sum_step (y : ℝ) (N : ℕ) :
    ∑ j ∈ Finset.range N, ch8Entry15_step (y + j) =
      ch8Entry15_remainder y - ch8Entry15_remainder (y + N) := by
  simpa only [ch8Entry15_step, Nat.cast_add, Nat.cast_one, add_assoc, Nat.cast_zero,
    add_zero] using Finset.sum_range_sub' (fun j : ℕ => ch8Entry15_remainder (y + j)) N

private theorem ch8Entry15_summable_step {y : ℝ} (hy : 2 ≤ y) :
    Summable (fun j : ℕ => ch8Entry15_step (y + j)) := by
  have hp := (ch8Entry15_summable_inv_pow hy).1
  have hmajor : Summable (fun j : ℕ => 14 * (1 / (y + j) ^ 9)) := hp.mul_left 14
  exact Summable.of_norm_bounded hmajor (fun j => by
    have hj0 : (0 : ℝ) ≤ j := Nat.cast_nonneg j
    have hb := ch8Entry15_step_bound (y := y + j) (by linarith)
    simpa only [Real.norm_eq_abs, div_eq_mul_inv, one_mul] using hb)

private theorem ch8Entry15_remainder_eq_tsum {y : ℝ} (hy : 2 ≤ y) :
    ch8Entry15_remainder y = ∑' j : ℕ, ch8Entry15_step (y + j) := by
  have hstep := ch8Entry15_summable_step hy
  have harg : Tendsto (fun N : ℕ => y + (N : ℝ)) atTop atTop :=
    tendsto_atTop_add_const_left atTop y tendsto_natCast_atTop_atTop
  have hrem := ch8Entry15_remainder_tendsto.comp harg
  have hpartial : Tendsto
      (fun N : ℕ => ∑ j ∈ Finset.range N, ch8Entry15_step (y + j))
      atTop (𝓝 (ch8Entry15_remainder y)) := by
    have hc : Tendsto (fun _ : ℕ => ch8Entry15_remainder y) atTop
        (𝓝 (ch8Entry15_remainder y)) := tendsto_const_nhds
    simpa only [Function.comp_apply, sub_zero, ch8Entry15_sum_step] using hc.sub hrem
  exact tendsto_nhds_unique hpartial hstep.tendsto_sum_tsum_nat

private theorem ch8Entry15_remainder_bound {y : ℝ} (hy : 2 ≤ y) :
    |ch8Entry15_remainder y| ≤ 3584 / y ^ 8 := by
  rw [ch8Entry15_remainder_eq_tsum hy]
  have hp := (ch8Entry15_summable_inv_pow hy).1
  have hpBound := (ch8Entry15_summable_inv_pow hy).2
  have hstep := ch8Entry15_summable_step hy
  have hmajor : Summable (fun j : ℕ => 14 * (1 / (y + j) ^ 9)) := hp.mul_left 14
  have hle : ∀ j : ℕ, ‖ch8Entry15_step (y + j)‖ ≤ 14 * (1 / (y + j) ^ 9) :=
    fun j => by
      have hj0 : (0 : ℝ) ≤ j := Nat.cast_nonneg j
      have hb := ch8Entry15_step_bound (y := y + j) (by linarith)
      simpa only [Real.norm_eq_abs, div_eq_mul_inv, one_mul] using hb
  calc
    |∑' j : ℕ, ch8Entry15_step (y + j)| = ‖∑' j : ℕ, ch8Entry15_step (y + j)‖ :=
      (Real.norm_eq_abs _).symm
    _ ≤ ∑' j : ℕ, ‖ch8Entry15_step (y + j)‖ := norm_tsum_le_tsum_norm hstep.norm
    _ ≤ ∑' j : ℕ, 14 * (1 / (y + j) ^ 9) :=
      hstep.norm.tsum_le_tsum hle hmajor
    _ = 14 * ∑' j : ℕ, 1 / (y + j) ^ 9 := tsum_mul_left
    _ ≤ 14 * (256 / y ^ 8) := mul_le_mul_of_nonneg_left hpBound (by norm_num)
    _ = 3584 / y ^ 8 := by ring

/-- The centered real digamma expansion through `y⁻⁶`, with remainder `O(y⁻⁸)`. -/
private theorem ch8Entry15_isBigO_chapter8RealDigamma_add_half_sub_log :
    (fun y : ℝ => chapter8RealDigamma (y + 1 / 2) - Real.log y - 1 / (24 * y ^ 2) +
      7 / (960 * y ^ 4) - 31 / (8064 * y ^ 6)) =O[atTop]
      (fun y : ℝ => 1 / y ^ 8) := by
  refine IsBigO.of_bound 3584 ?_
  filter_upwards [eventually_ge_atTop (2 : ℝ)] with y hy
  change ‖ch8Entry15_remainder y‖ ≤ 3584 * ‖(1 / y ^ 8 : ℝ)‖
  have hg : 0 ≤ (1 / y ^ 8 : ℝ) := by positivity
  rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg hg]
  simpa only [div_eq_mul_inv, one_mul] using ch8Entry15_remainder_bound hy

def chapter8Entry15A (x : ℝ) : ℝ :=
  Real.exp (chapter8RealDigamma (x + 1))

/-- Ramanujan's auxiliary quantity `a(x) = exp (ψ(x+1))` tends to infinity. -/
private theorem ch8Entry15_tendsto_chapter8Entry15A :
    Tendsto chapter8Entry15A atTop atTop := by
  have hpsi : Tendsto chapter8RealDigamma atTop atTop := by
    have h := ch8Entry15_tendsto_chapter8RealDigamma_sub_log.add_atTop
      Real.tendsto_log_atTop
    simpa only [sub_add_cancel] using h
  have hshift : Tendsto (fun x : ℝ => x + 1) atTop atTop :=
    tendsto_atTop_add_const_right atTop 1 tendsto_id
  exact Real.tendsto_exp_atTop.comp (hpsi.comp hshift)

def chapter8Entry15Approx (n : ℂ) (x : ℝ) : ℂ :=
  let a : ℂ := chapter8Entry15A x
  1 - n / (6 * a ^ 2) + (10 * n ^ 2 + 11 * n) / (720 * a ^ 4) -
    (70 * n ^ 3 + 231 * n ^ 2 + 891 * n) / (90720 * a ^ 6)

def chapter8Entry15Power (n : ℂ) (x : ℝ) : ℂ :=
  Complex.cpow ((((x + 1 / 2) / chapter8Entry15A x : ℝ) : ℂ)) (4 * n)

private def ch8Entry15Q (x : ℝ) : ℂ :=
  ((1 / (x + 1 / 2) ^ 2 : ℝ) : ℂ)

private def ch8Entry15D (x : ℝ) : ℂ :=
  ((chapter8RealDigamma (x + 1) - Real.log (x + 1 / 2) : ℝ) : ℂ)

private def ch8Entry15P (x : ℝ) : ℂ :=
  ((1 / (24 * (x + 1 / 2) ^ 2) - 7 / (960 * (x + 1 / 2) ^ 4) +
    31 / (8064 * (x + 1 / 2) ^ 6) : ℝ) : ℂ)

private def ch8Entry15S (x : ℝ) : ℂ :=
  ch8Entry15Q x * Complex.exp (-2 * ch8Entry15D x)

private theorem ch8Entry15_tendsto_q :
    Tendsto ch8Entry15Q atTop (𝓝 0) := by
  have hshift : Tendsto (fun x : ℝ => x + 1 / 2) atTop atTop :=
    tendsto_atTop_add_const_right atTop (1 / 2) tendsto_id
  have hinv : Tendsto (fun x : ℝ => 1 / (x + 1 / 2)) atTop (𝓝 0) := by
    simpa only [one_div, Function.comp_def] using
      (tendsto_inv_atTop_zero.comp hshift :
        Tendsto (fun x : ℝ => (x + 1 / 2)⁻¹) atTop (𝓝 0))
  have hreal : Tendsto (fun x : ℝ => (1 / (x + 1 / 2)) ^ 2) atTop (𝓝 0) := by
    simpa using hinv.pow 2
  have hc := Complex.continuous_ofReal.tendsto 0 |>.comp hreal
  refine Tendsto.congr' ?_ hc
  filter_upwards with x
  unfold ch8Entry15Q
  simp

private theorem ch8Entry15_p_eq (x : ℝ) :
    ch8Entry15P x = ch8Entry15Q x / 24 - 7 * ch8Entry15Q x ^ 2 / 960 +
      31 * ch8Entry15Q x ^ 3 / 8064 := by
  by_cases h : x + 1 / 2 = 0
  · have hx : x = -1 / 2 := by linarith
    norm_num [ch8Entry15P, ch8Entry15Q, hx]
  · unfold ch8Entry15P ch8Entry15Q
    push_cast
    field_simp [h]

private theorem ch8Entry15_q_pow_add_isBigO (m n : ℕ) :
    (fun x : ℝ => ch8Entry15Q x ^ (m + n)) =O[atTop]
      (fun x => ch8Entry15Q x ^ m) := by
  have hb := (ch8Entry15_tendsto_q.pow n).isBigO_one ℂ
  have h := (isBigO_refl (fun x : ℝ => ch8Entry15Q x ^ m) atTop).mul hb
  simpa only [pow_add, mul_one] using h

private theorem ch8Entry15_d_sub_p_isBigO :
    (fun x : ℝ => ch8Entry15D x - ch8Entry15P x) =O[atTop]
      (fun x => ch8Entry15Q x ^ 4) := by
  refine IsBigO.of_bound 3584 ?_
  filter_upwards [eventually_ge_atTop (2 : ℝ)] with x hx
  have hb := ch8Entry15_remainder_bound (y := x + 1 / 2) (by linarith)
  have hxp : 0 < x + 1 / 2 := by linarith
  have heq : ch8Entry15D x - ch8Entry15P x =
      (ch8Entry15_remainder (x + 1 / 2) : ℂ) := by
    unfold ch8Entry15D ch8Entry15P ch8Entry15_remainder
    rw [← Complex.ofReal_sub]
    congr 1
    ring_nf
  have hq : ch8Entry15Q x ^ 4 = ((1 / (x + 1 / 2) ^ 8 : ℝ) : ℂ) := by
    unfold ch8Entry15Q
    push_cast
    norm_num [div_pow, pow_mul]
    ring
  rw [heq, hq, Complex.norm_real, Complex.norm_real]
  change |ch8Entry15_remainder (x + 1 / 2)| ≤
    3584 * |(1 / (x + 1 / 2) ^ 8 : ℝ)|
  have hnonneg : 0 ≤ (1 / (x + 1 / 2) ^ 8 : ℝ) := by positivity
  rw [abs_of_nonneg hnonneg]
  simpa only [div_eq_mul_inv, one_mul] using hb

private theorem ch8Entry15_tendsto_p :
    Tendsto ch8Entry15P atTop (𝓝 0) := by
  have hq := ch8Entry15_tendsto_q
  have h := ((hq.const_mul (1 / 24)).sub
    ((hq.pow 2).const_mul (7 / 960))).add ((hq.pow 3).const_mul (31 / 8064))
  have hpoly : Tendsto (fun x : ℝ => ch8Entry15Q x / 24 -
      7 * ch8Entry15Q x ^ 2 / 960 + 31 * ch8Entry15Q x ^ 3 / 8064)
      atTop (𝓝 0) := by
    convert h using 1
    · ext x
      ring
    · norm_num
  exact Tendsto.congr' (Eventually.of_forall fun x => (ch8Entry15_p_eq x).symm) hpoly

private theorem ch8Entry15_tendsto_d :
    Tendsto ch8Entry15D atTop (𝓝 0) := by
  have hq4 : Tendsto (fun x : ℝ => ch8Entry15Q x ^ 4) atTop (𝓝 0) := by
    simpa using ch8Entry15_tendsto_q.pow 4
  have herr := ch8Entry15_d_sub_p_isBigO.trans_tendsto hq4
  have h := herr.add ch8Entry15_tendsto_p
  simpa only [sub_add_cancel, zero_add] using h

private theorem ch8Entry15_p_isBigO_q :
    ch8Entry15P =O[atTop] ch8Entry15Q := by
  have hb : Tendsto (fun x : ℝ => 1 / 24 - 7 / 960 * ch8Entry15Q x +
      31 / 8064 * ch8Entry15Q x ^ 2) atTop (𝓝 (1 / 24)) := by
    have hc : Tendsto (fun _ : ℝ => (1 / 24 : ℂ)) atTop (𝓝 (1 / 24)) :=
      tendsto_const_nhds
    have h := hc.sub
      (ch8Entry15_tendsto_q.const_mul (7 / 960)) |>.add
        ((ch8Entry15_tendsto_q.pow 2).const_mul (31 / 8064))
    convert h using 1
    norm_num
  have h := (isBigO_refl ch8Entry15Q atTop).mul (hb.isBigO_one ℂ)
  convert h using 1
  · ext x
    rw [ch8Entry15_p_eq]
    ring
  · ext x
    ring

private theorem ch8Entry15_d_isBigO_q :
    ch8Entry15D =O[atTop] ch8Entry15Q := by
  have hq4q : (fun x : ℝ => ch8Entry15Q x ^ 4) =O[atTop] ch8Entry15Q := by
    simpa using ch8Entry15_q_pow_add_isBigO 1 3
  have herr := ch8Entry15_d_sub_p_isBigO.trans
    hq4q
  have h := herr.add ch8Entry15_p_isBigO_q
  convert h using 1
  ext x
  ring

private theorem ch8Entry15_p_sub_linear_isBigO :
    (fun x : ℝ => ch8Entry15P x - ch8Entry15Q x / 24) =O[atTop]
      (fun x => ch8Entry15Q x ^ 2) := by
  have hb : Tendsto (fun x : ℝ => -7 / 960 + 31 / 8064 * ch8Entry15Q x)
      atTop (𝓝 (-7 / 960)) := by
    have hc : Tendsto (fun _ : ℝ => (-7 / 960 : ℂ)) atTop (𝓝 (-7 / 960)) :=
      tendsto_const_nhds
    convert hc.add (ch8Entry15_tendsto_q.const_mul (31 / 8064)) using 1
    norm_num
  have h := (isBigO_refl (fun x : ℝ => ch8Entry15Q x ^ 2) atTop).mul
    (hb.isBigO_one ℂ)
  convert h using 1
  · ext x
    rw [ch8Entry15_p_eq]
    ring
  · ext x
    ring

private theorem ch8Entry15_p_sq_isBigO :
    (fun x : ℝ => ch8Entry15P x ^ 2 - ch8Entry15Q x ^ 2 / 24 ^ 2 +
      14 * ch8Entry15Q x ^ 3 / (24 * 960)) =O[atTop]
      (fun x => ch8Entry15Q x ^ 4) := by
  have he : (fun x : ℝ => (ch8Entry15P x - ch8Entry15Q x / 24) -
      (-7 / 960) * ch8Entry15Q x ^ 2) =O[atTop]
      (fun x => ch8Entry15Q x ^ 3) := by
    have h := isBigO_const_mul_self (31 / 8064 : ℂ)
      (fun x : ℝ => ch8Entry15Q x ^ 3) atTop
    convert h using 1
    ext x
    rw [ch8Entry15_p_eq]
    ring
  have hlin := isBigO_const_mul_self (2 / 24 : ℂ) ch8Entry15Q atTop
  have hfirst := hlin.mul he
  have hfirst' : (fun x : ℝ => (2 / 24) * ch8Entry15Q x *
      ((ch8Entry15P x - ch8Entry15Q x / 24) -
        (-7 / 960) * ch8Entry15Q x ^ 2)) =O[atTop]
      (fun x => ch8Entry15Q x ^ 4) := by
    convert hfirst using 1
    ext x
    ring
  have hsq := ch8Entry15_p_sub_linear_isBigO.pow 2
  have hsq' : (fun x : ℝ => (ch8Entry15P x - ch8Entry15Q x / 24) ^ 2) =O[atTop]
      (fun x => ch8Entry15Q x ^ 4) := by
    convert hsq using 1
    ext x
    ring
  have h := hfirst'.add hsq'
  convert h using 1
  · ext x
    rw [ch8Entry15_p_eq]
    ring

private theorem ch8Entry15_p_cube_isBigO :
    (fun x : ℝ => ch8Entry15P x ^ 3 - ch8Entry15Q x ^ 3 / 24 ^ 3) =O[atTop]
      (fun x => ch8Entry15Q x ^ 4) := by
  have hlinear : (fun x : ℝ => ch8Entry15Q x / 24) =O[atTop] ch8Entry15Q := by
    convert isBigO_const_mul_self (1 / 24 : ℂ) ch8Entry15Q atTop using 1
    ext x
    ring
  have hbracket : (fun x : ℝ => ch8Entry15P x ^ 2 +
      ch8Entry15P x * (ch8Entry15Q x / 24) + (ch8Entry15Q x / 24) ^ 2)
      =O[atTop] (fun x => ch8Entry15Q x ^ 2) := by
    have hmul : (fun x : ℝ => ch8Entry15P x * (ch8Entry15Q x / 24))
        =O[atTop] (fun x => ch8Entry15Q x ^ 2) := by
      convert ch8Entry15_p_isBigO_q.mul hlinear using 1
      ext x
      ring
    have h := (ch8Entry15_p_isBigO_q.pow 2).add hmul |>.add (hlinear.pow 2)
    exact h
  have h := ch8Entry15_p_sub_linear_isBigO.mul hbracket
  convert h using 1
  · ext x
    ring
  · ext x
    ring

private def ch8Entry15Cubic (c z : ℂ) : ℂ :=
  1 + c * z + (c * z) ^ 2 / 2 + (c * z) ^ 3 / 6

private def ch8Entry15ExpPoly (c : ℂ) (x : ℝ) : ℂ :=
  let q := ch8Entry15Q x
  1 + (c / 24) * q + (-7 * c / 960 + c ^ 2 / (2 * 24 ^ 2)) * q ^ 2 +
    (31 * c / 8064 - 7 * c ^ 2 / (24 * 960) + c ^ 3 / (6 * 24 ^ 3)) * q ^ 3

private theorem ch8Entry15_exp_sub_cubic_isBigO (c : ℂ) :
    (fun x : ℝ => Complex.exp (c * ch8Entry15D x) -
      ch8Entry15Cubic c (ch8Entry15D x)) =O[atTop]
      (fun x => ch8Entry15Q x ^ 4) := by
  have hcd : Tendsto (fun x : ℝ => c * ch8Entry15D x) atTop (𝓝 0) := by
    simpa using ch8Entry15_tendsto_d.const_mul c
  have ht := (Complex.exp_sub_sum_range_isBigO_pow 4).comp_tendsto hcd
  have ht' : (fun x : ℝ => Complex.exp (c * ch8Entry15D x) -
      ch8Entry15Cubic c (ch8Entry15D x)) =O[atTop]
      (fun x => (c * ch8Entry15D x) ^ 4) := by
    convert ht using 1
    · ext x
      norm_num [ch8Entry15Cubic, Finset.sum_range_succ]
    · ext x
      rfl
  have hcdO : (fun x : ℝ => c * ch8Entry15D x) =O[atTop] ch8Entry15Q :=
    (isBigO_const_mul_self c ch8Entry15D atTop).trans ch8Entry15_d_isBigO_q
  exact ht'.trans (hcdO.pow 4)

private def ch8Entry15CubicDiffFactor (c : ℂ) (x : ℝ) : ℂ :=
  c + c ^ 2 / 2 * (ch8Entry15D x + ch8Entry15P x) +
    c ^ 3 / 6 * (ch8Entry15D x ^ 2 + ch8Entry15D x * ch8Entry15P x +
      ch8Entry15P x ^ 2)

private theorem ch8Entry15_cubic_d_sub_p_isBigO (c : ℂ) :
    (fun x : ℝ => ch8Entry15Cubic c (ch8Entry15D x) -
      ch8Entry15Cubic c (ch8Entry15P x)) =O[atTop]
      (fun x => ch8Entry15Q x ^ 4) := by
  have hlinear := ch8Entry15_tendsto_d.add ch8Entry15_tendsto_p
  have hquadratic := (ch8Entry15_tendsto_d.pow 2).add
    (ch8Entry15_tendsto_d.mul ch8Entry15_tendsto_p) |>.add
      (ch8Entry15_tendsto_p.pow 2)
  have hc : Tendsto (fun _ : ℝ => c) atTop (𝓝 c) := tendsto_const_nhds
  have hfactor : Tendsto (ch8Entry15CubicDiffFactor c) atTop (𝓝 c) := by
    have h := hc.add (hlinear.const_mul (c ^ 2 / 2)) |>.add
      (hquadratic.const_mul (c ^ 3 / 6))
    convert h using 1
    · ext x
      unfold ch8Entry15CubicDiffFactor
      ring
    · norm_num
  have h := ch8Entry15_d_sub_p_isBigO.mul (hfactor.isBigO_one ℂ)
  convert h using 1
  · ext x
    unfold ch8Entry15Cubic ch8Entry15CubicDiffFactor
    ring
  · ext x
    ring

private theorem ch8Entry15_cubic_p_sub_expPoly_isBigO (c : ℂ) :
    (fun x : ℝ => ch8Entry15Cubic c (ch8Entry15P x) -
      ch8Entry15ExpPoly c x) =O[atTop] (fun x => ch8Entry15Q x ^ 4) := by
  have hsq := ch8Entry15_p_sq_isBigO.const_mul_left (c ^ 2 / 2)
  have hcube := ch8Entry15_p_cube_isBigO.const_mul_left (c ^ 3 / 6)
  have h := hsq.add hcube
  convert h using 1
  ext x
  rw [ch8Entry15_p_eq]
  unfold ch8Entry15Cubic ch8Entry15ExpPoly
  ring

private theorem ch8Entry15_exp_sub_expPoly_isBigO (c : ℂ) :
    (fun x : ℝ => Complex.exp (c * ch8Entry15D x) - ch8Entry15ExpPoly c x)
      =O[atTop] (fun x => ch8Entry15Q x ^ 4) := by
  have h := (ch8Entry15_exp_sub_cubic_isBigO c).add
    (ch8Entry15_cubic_d_sub_p_isBigO c) |>.add
      (ch8Entry15_cubic_p_sub_expPoly_isBigO c)
  convert h using 1
  ext x
  ring

private def ch8Entry15SPoly (x : ℝ) : ℂ :=
  ch8Entry15Q x - ch8Entry15Q x ^ 2 / 12 + 13 * ch8Entry15Q x ^ 3 / 720

private theorem ch8Entry15_tendsto_s :
    Tendsto ch8Entry15S atTop (𝓝 0) := by
  have he : Tendsto (fun x : ℝ => Complex.exp (-2 * ch8Entry15D x)) atTop (𝓝 1) := by
    simpa using (ch8Entry15_tendsto_d.const_mul (-2)).cexp
  unfold ch8Entry15S
  simpa only [zero_mul] using ch8Entry15_tendsto_q.mul he

private theorem ch8Entry15_s_isBigO_q :
    ch8Entry15S =O[atTop] ch8Entry15Q := by
  have he : Tendsto (fun x : ℝ => Complex.exp (-2 * ch8Entry15D x)) atTop (𝓝 1) := by
    simpa using (ch8Entry15_tendsto_d.const_mul (-2)).cexp
  have h := (isBigO_refl ch8Entry15Q atTop).mul (he.isBigO_one ℂ)
  convert h using 1
  · ext x
    rfl
  · ext x
    ring

private theorem ch8Entry15_s_sub_sPoly_isBigO :
    (fun x : ℝ => ch8Entry15S x - ch8Entry15SPoly x) =O[atTop]
      (fun x => ch8Entry15Q x ^ 4) := by
  have hmul := (isBigO_refl ch8Entry15Q atTop).mul
    (ch8Entry15_exp_sub_expPoly_isBigO (-2))
  have hmul5 : (fun x : ℝ => ch8Entry15Q x *
      (Complex.exp (-2 * ch8Entry15D x) - ch8Entry15ExpPoly (-2) x))
      =O[atTop] (fun x => ch8Entry15Q x ^ 5) := by
    convert hmul using 1
    ext x
    ring
  have hmul4 := hmul5.trans (ch8Entry15_q_pow_add_isBigO 4 1)
  have htrunc : (fun x : ℝ => ch8Entry15Q x * ch8Entry15ExpPoly (-2) x -
      ch8Entry15SPoly x) =O[atTop] (fun x => ch8Entry15Q x ^ 4) := by
    have h := isBigO_const_mul_self
      ((31 * (-2) / 8064 - 7 * (-2 : ℂ) ^ 2 / (24 * 960) +
        (-2 : ℂ) ^ 3 / (6 * 24 ^ 3))) (fun x : ℝ => ch8Entry15Q x ^ 4) atTop
    convert h using 1
    ext x
    unfold ch8Entry15ExpPoly ch8Entry15SPoly
    ring
  have h := hmul4.add htrunc
  convert h using 1
  ext x
  unfold ch8Entry15S
  ring

private theorem ch8Entry15_s_sub_q_isBigO :
    (fun x : ℝ => ch8Entry15S x - ch8Entry15Q x) =O[atTop]
      (fun x => ch8Entry15Q x ^ 2) := by
  have hrem := ch8Entry15_s_sub_sPoly_isBigO.trans
    (ch8Entry15_q_pow_add_isBigO 2 2)
  have hb : Tendsto (fun x : ℝ => -1 / 12 + 13 / 720 * ch8Entry15Q x)
      atTop (𝓝 (-1 / 12)) := by
    have hc : Tendsto (fun _ : ℝ => (-1 / 12 : ℂ)) atTop (𝓝 (-1 / 12)) :=
      tendsto_const_nhds
    convert hc.add (ch8Entry15_tendsto_q.const_mul (13 / 720)) using 1
    norm_num
  have hpoly := (isBigO_refl (fun x : ℝ => ch8Entry15Q x ^ 2) atTop).mul
    (hb.isBigO_one ℂ)
  have hpoly' : (fun x : ℝ => ch8Entry15SPoly x - ch8Entry15Q x) =O[atTop]
      (fun x => ch8Entry15Q x ^ 2) := by
    convert hpoly using 1
    · ext x
      unfold ch8Entry15SPoly
      ring
    · ext x
      ring
  have h := hrem.add hpoly'
  convert h using 1
  ext x
  ring

private theorem ch8Entry15_tendsto_sPoly :
    Tendsto ch8Entry15SPoly atTop (𝓝 0) := by
  have hq := ch8Entry15_tendsto_q
  have h := hq.sub ((hq.pow 2).const_mul (1 / 12)) |>.add
    ((hq.pow 3).const_mul (13 / 720))
  convert h using 1
  · ext x
    unfold ch8Entry15SPoly
    ring
  · norm_num

private theorem ch8Entry15_s_sq_isBigO :
    (fun x : ℝ => ch8Entry15S x ^ 2 -
      (ch8Entry15Q x ^ 2 - ch8Entry15Q x ^ 3 / 6)) =O[atTop]
      (fun x => ch8Entry15Q x ^ 4) := by
  have hsum : Tendsto (fun x : ℝ => ch8Entry15S x + ch8Entry15SPoly x)
      atTop (𝓝 0) := by
    simpa using ch8Entry15_tendsto_s.add ch8Entry15_tendsto_sPoly
  have hdiff := ch8Entry15_s_sub_sPoly_isBigO.mul (hsum.isBigO_one ℂ)
  have hdiff' : (fun x : ℝ => ch8Entry15S x ^ 2 - ch8Entry15SPoly x ^ 2)
      =O[atTop] (fun x => ch8Entry15Q x ^ 4) := by
    convert hdiff using 1
    · ext x
      ring
    · ext x
      ring
  have hb : Tendsto (fun x : ℝ => (1 / 12 : ℂ) ^ 2 + 26 / 720 +
      2 * (-1 / 12) * (13 / 720) * ch8Entry15Q x +
      (13 / 720) ^ 2 * ch8Entry15Q x ^ 2)
      atTop (𝓝 ((1 / 12 : ℂ) ^ 2 + 26 / 720)) := by
    have hq := ch8Entry15_tendsto_q
    convert tendsto_const_nhds.add
      (hq.const_mul (2 * (-1 / 12) * (13 / 720))) |>.add
        ((hq.pow 2).const_mul ((13 / 720) ^ 2)) using 1
    norm_num
  have hpoly := (isBigO_refl (fun x : ℝ => ch8Entry15Q x ^ 4) atTop).mul
    (hb.isBigO_one ℂ)
  have hpoly' : (fun x : ℝ => ch8Entry15SPoly x ^ 2 -
      (ch8Entry15Q x ^ 2 - ch8Entry15Q x ^ 3 / 6)) =O[atTop]
      (fun x => ch8Entry15Q x ^ 4) := by
    convert hpoly using 1
    · ext x
      unfold ch8Entry15SPoly
      ring
    · ext x
      ring
  have h := hdiff'.add hpoly'
  convert h using 1
  ext x
  ring

private theorem ch8Entry15_s_cube_isBigO :
    (fun x : ℝ => ch8Entry15S x ^ 3 - ch8Entry15Q x ^ 3) =O[atTop]
      (fun x => ch8Entry15Q x ^ 4) := by
  have hbracket : (fun x : ℝ => ch8Entry15S x ^ 2 +
      ch8Entry15S x * ch8Entry15Q x + ch8Entry15Q x ^ 2) =O[atTop]
      (fun x => ch8Entry15Q x ^ 2) := by
    have hmul : (fun x : ℝ => ch8Entry15S x * ch8Entry15Q x) =O[atTop]
        (fun x => ch8Entry15Q x ^ 2) := by
      convert ch8Entry15_s_isBigO_q.mul (isBigO_refl ch8Entry15Q atTop) using 1
      ext x
      ring
    exact (ch8Entry15_s_isBigO_q.pow 2).add hmul |>.add
      ((isBigO_refl ch8Entry15Q atTop).pow 2)
  have h := ch8Entry15_s_sub_q_isBigO.mul hbracket
  convert h using 1
  · ext x
    ring
  · ext x
    ring

private def ch8Entry15ApproxS (n : ℂ) (x : ℝ) : ℂ :=
  1 - n / 6 * ch8Entry15S x + (10 * n ^ 2 + 11 * n) / 720 * ch8Entry15S x ^ 2 -
    (70 * n ^ 3 + 231 * n ^ 2 + 891 * n) / 90720 * ch8Entry15S x ^ 3

private theorem ch8Entry15_approxS_sub_expPoly_isBigO (n : ℂ) :
    (fun x : ℝ => ch8Entry15ApproxS n x - ch8Entry15ExpPoly (-4 * n) x)
      =O[atTop] (fun x => ch8Entry15Q x ^ 4) := by
  have h1 := ch8Entry15_s_sub_sPoly_isBigO.const_mul_left (-n / 6)
  have h2 := ch8Entry15_s_sq_isBigO.const_mul_left ((10 * n ^ 2 + 11 * n) / 720)
  have h3 := ch8Entry15_s_cube_isBigO.const_mul_left
    (-(70 * n ^ 3 + 231 * n ^ 2 + 891 * n) / 90720)
  have h := h1.add h2 |>.add h3
  convert h using 1
  ext x
  unfold ch8Entry15ApproxS ch8Entry15ExpPoly ch8Entry15SPoly
  ring

private theorem ch8Entry15_exp_sub_approxS_isBigO (n : ℂ) :
    (fun x : ℝ => Complex.exp ((-4 * n) * ch8Entry15D x) - ch8Entry15ApproxS n x)
      =O[atTop] (fun x => ch8Entry15Q x ^ 4) := by
  have hneg := (ch8Entry15_approxS_sub_expPoly_isBigO n).const_mul_left (-1)
  have h := (ch8Entry15_exp_sub_expPoly_isBigO (-4 * n)).add hneg
  convert h using 1
  ext x
  ring

private theorem ch8Entry15_q_pow_four_isBigO_s_pow_four :
    (fun x : ℝ => ch8Entry15Q x ^ 4) =O[atTop]
      (fun x => ch8Entry15S x ^ 4) := by
  have he : Tendsto (fun x : ℝ => Complex.exp (8 * ch8Entry15D x)) atTop (𝓝 1) := by
    simpa using (ch8Entry15_tendsto_d.const_mul 8).cexp
  have h := (isBigO_refl (fun x : ℝ => ch8Entry15S x ^ 4) atTop).mul
    (he.isBigO_one ℂ)
  convert h using 1
  · ext x
    unfold ch8Entry15S
    rw [mul_pow, ← Complex.exp_nat_mul]
    calc
      ch8Entry15Q x ^ 4 = ch8Entry15Q x ^ 4 * 1 := by ring
      _ = ch8Entry15Q x ^ 4 *
          (Complex.exp ((4 : ℂ) * (-2 * ch8Entry15D x)) *
            Complex.exp (8 * ch8Entry15D x)) := by
        rw [← Complex.exp_add]
        ring_nf
        simp
      _ = ch8Entry15Q x ^ 4 * Complex.exp ((4 : ℂ) * (-2 * ch8Entry15D x)) *
          Complex.exp (8 * ch8Entry15D x) := by ring
  · ext x
    ring

private theorem ch8Entry15_s_eq_inv_a_sq {x : ℝ} (hx : -1 / 2 < x) :
    ch8Entry15S x = (1 : ℂ) / (chapter8Entry15A x : ℂ) ^ 2 := by
  have hy : 0 < x + 1 / 2 := by linarith
  let p := chapter8RealDigamma (x + 1)
  let y := x + 1 / 2
  have hy' : 0 < y := by simpa [y] using hy
  have hp2 : Real.exp (2 * p) = Real.exp p ^ 2 := by
    simpa using Real.exp_nat_mul p 2
  have hy2 : Real.exp (2 * Real.log y) = y ^ 2 := by
    rw [show Real.exp (2 * Real.log y) = Real.exp (Real.log y) ^ 2 by
      simpa using Real.exp_nat_mul (Real.log y) 2, Real.exp_log hy']
  have hreal : 1 / y ^ 2 * Real.exp (-2 * (p - Real.log y)) =
      1 / Real.exp p ^ 2 := by
    calc
      1 / y ^ 2 * Real.exp (-2 * (p - Real.log y)) =
          1 / y ^ 2 * (Real.exp (-2 * p) * Real.exp (2 * Real.log y)) := by
        rw [← Real.exp_add]
        congr 2
        ring
      _ = 1 / y ^ 2 * ((Real.exp p ^ 2)⁻¹ * y ^ 2) := by
        rw [show -2 * p = -(2 * p) by ring, Real.exp_neg, hp2, hy2]
      _ = 1 / Real.exp p ^ 2 := by
        field_simp [hy'.ne', Real.exp_ne_zero]
  have hc := congrArg Complex.ofReal hreal
  unfold ch8Entry15S ch8Entry15Q ch8Entry15D chapter8Entry15A
  change ((1 / y ^ 2 : ℝ) : ℂ) * Complex.exp (-2 * ((p - Real.log y : ℝ) : ℂ)) =
    (1 : ℂ) / ((Real.exp p : ℝ) : ℂ) ^ 2
  push_cast at hc
  simpa [Complex.ofReal_exp] using hc

private theorem ch8Entry15_power_eq_exp (n : ℂ) {x : ℝ} (hx : -1 / 2 < x) :
    chapter8Entry15Power n x = Complex.exp ((-4 * n) * ch8Entry15D x) := by
  have hy : 0 < x + 1 / 2 := by linarith
  have ha : 0 < chapter8Entry15A x := Real.exp_pos _
  have hb : 0 < (x + 1 / 2) / chapter8Entry15A x := div_pos hy ha
  have hb0 : ((((x + 1 / 2) / chapter8Entry15A x : ℝ) : ℂ)) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr hb.ne'
  have hlog : Real.log ((x + 1 / 2) / chapter8Entry15A x) =
      -(chapter8RealDigamma (x + 1) - Real.log (x + 1 / 2)) := by
    unfold chapter8Entry15A
    rw [Real.log_div hy.ne' (Real.exp_ne_zero _), Real.log_exp]
    ring
  unfold chapter8Entry15Power
  rw [Complex.cpow_eq_pow, Complex.cpow_def_of_ne_zero hb0,
    ← Complex.ofReal_log hb.le, hlog]
  unfold ch8Entry15D
  push_cast
  congr 1
  ring

private theorem ch8Entry15_approxS_eq_approx (n : ℂ) {x : ℝ} (hx : -1 / 2 < x) :
    ch8Entry15ApproxS n x = chapter8Entry15Approx n x := by
  have hs := ch8Entry15_s_eq_inv_a_sq hx
  have ha : (chapter8Entry15A x : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr (Real.exp_ne_zero _)
  unfold ch8Entry15ApproxS chapter8Entry15Approx
  dsimp
  rw [hs]
  field_simp [ha]

private theorem ch8Entry15_s_pow_four_eq_inv_a_pow_eight {x : ℝ} (hx : -1 / 2 < x) :
    ch8Entry15S x ^ 4 = (1 : ℂ) / (chapter8Entry15A x : ℂ) ^ 8 := by
  rw [ch8Entry15_s_eq_inv_a_sq hx]
  have ha : (chapter8Entry15A x : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr (Real.exp_ne_zero _)
  field_simp [ha]

/-- **Ramanujan's asymptotic expansion of $((x + 1/2)/e^{\psi(x+1)})^{4n}$.** For real $x$ let
$\psi(x) = \Gamma'(x)/\Gamma(x)$ and $a(x) = e^{\psi(x+1)}$. Then $a(x) \to \infty$ as
$x \to \infty$, and for every complex number $n$,
$$\left(\frac{x + 1/2}{a(x)}\right)^{4n} = 1 - \frac{n}{6 a(x)^2} +
\frac{10 n^2 + 11 n}{720 a(x)^4} - \frac{70 n^3 + 231 n^2 + 891 n}{90720 a(x)^6} +
O\left(\frac{1}{a(x)^8}\right)$$
as $x \to \infty$ through the real numbers, where the power is the principal complex power.

Proof: Convexity of `log Γ` gives crude digamma bounds. A telescoped centered expansion and
Taylor's formula for the complex exponential then give the stated coefficients and remainder.

Proves `Wanted` entry `ramanujan_part1_ch8_entry15_doublegamma`.

Source: Bruce C. Berndt, Ramanujan's Notebooks, Part I, Chapter 8.
-/
theorem ramanujan_part1_ch8_entry15_doublegamma (n : ℂ) :
    Tendsto chapter8Entry15A atTop atTop ∧
      IsBigO atTop
        (fun x : ℝ => chapter8Entry15Power n x - chapter8Entry15Approx n x)
        (fun x : ℝ => (1 : ℂ) / (chapter8Entry15A x : ℂ) ^ 8) := by
  refine ⟨ch8Entry15_tendsto_chapter8Entry15A, ?_⟩
  have hcore := (ch8Entry15_exp_sub_approxS_isBigO n).trans
    ch8Entry15_q_pow_four_isBigO_s_pow_four
  refine hcore.congr' ?_ ?_
  · filter_upwards [eventually_gt_atTop (-1 / 2 : ℝ)] with x hx
    rw [ch8Entry15_power_eq_exp n hx, ← ch8Entry15_approxS_eq_approx n hx]
  · filter_upwards [eventually_gt_atTop (-1 / 2 : ℝ)] with x hx
    exact ch8Entry15_s_pow_four_eq_inv_a_pow_eight hx

end

end Entry15Doublegamma

end MathlibExt.Analysis.Ramanujan.Part1Ch8
