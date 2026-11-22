/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module


public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Inverse
public import Mathlib.Topology.Algebra.InfiniteSum.Basic

import Mathlib.Analysis.SpecialFunctions.Integrals.Log
import Mathlib.Analysis.PSeries
import Mathlib.Analysis.Calculus.SmoothSeries
import Mathlib.Analysis.Complex.Exponential
import Mathlib.Analysis.Normed.Group.Tannery
import Mathlib.Analysis.SumOverResidueClass
import Mathlib.Analysis.SpecialFunctions.Complex.LogBounds
import Mathlib.Analysis.SpecialFunctions.Log.NegMulLog
import Mathlib.Analysis.SpecialFunctions.Trigonometric.InverseDeriv
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Sinc
import Mathlib.MeasureTheory.Integral.IntervalIntegral.IntegrationByParts
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.NumberTheory.ZetaValues
import Mathlib.Algebra.BigOperators.Fin

/-!
# Bhandari's arcsine-over-sine integral

This file evaluates an integral involving `arcsin (sin x ^ 2)` in terms of Catalan's constant
and two reciprocal-square series.
-/

@[expose] public section

namespace MetaMathlibExt

open Filter MeasureTheory Topology
open scoped BigOperators Interval

noncomputable section

private def adsHalfArcsinSinSq (x : ℝ) : ℝ :=
  Real.arcsin (Real.sin x ^ 2) / 2

private def adsHalfArcsinSinSqDeriv (x : ℝ) : ℝ :=
  Real.sin x / Real.sqrt (1 + Real.sin x ^ 2)

private def adsRawIntegrand (x : ℝ) : ℝ :=
  2 * x * Real.sqrt (1 + Real.sin (2 * x)) / Real.sin (2 * x)

private def adsJIntegrand (x : ℝ) : ℝ :=
  x * (1 / Real.cos x + 1 / Real.sin x)

private def adsLogTanIntegral (a : ℝ) : ℝ :=
  ∫ x in (0 : ℝ)..a, Real.log (Real.tan x)

private def adsLogTanHalf (x : ℝ) : ℝ :=
  Real.log (Real.tan (x / 2))

private def adsLogTanShift (x : ℝ) : ℝ :=
  Real.log (Real.tan (x / 2 + Real.pi / 4))

private def adsLogTanProducts (x : ℝ) : ℝ :=
  x * adsLogTanHalf x + x * adsLogTanShift x

private lemma ads_halfArcsinSinSq_hasDerivAt {x : ℝ}
    (hx : x ∈ Set.Ioo 0 (Real.pi / 2)) :
    HasDerivAt adsHalfArcsinSinSq (adsHalfArcsinSinSqDeriv x) x := by
  rw [Set.mem_Ioo] at hx
  have hcos : 0 < Real.cos x :=
    Real.cos_pos_of_mem_Ioo ⟨by linarith [Real.pi_pos], hx.2⟩
  have hsin_sq_lt : Real.sin x ^ 2 < 1 := by
    nlinarith [Real.sin_sq_add_cos_sq x, sq_pos_of_pos hcos]
  have hne_neg : Real.sin x ^ 2 ≠ -1 := by
    nlinarith [sq_nonneg (Real.sin x)]
  have hne_one : Real.sin x ^ 2 ≠ 1 := ne_of_lt hsin_sq_lt
  have hinner := (Real.hasDerivAt_sin x).pow 2
  have hcomp := (Real.hasDerivAt_arcsin hne_neg hne_one).comp x hinner
  have hfactor : 1 - (Real.sin x ^ 2) ^ 2 =
      Real.cos x ^ 2 * (1 + Real.sin x ^ 2) := by
    nlinarith [Real.sin_sq_add_cos_sq x]
  have hsqrt : Real.sqrt (1 - (Real.sin x ^ 2) ^ 2) =
      Real.cos x * Real.sqrt (1 + Real.sin x ^ 2) := by
    rw [hfactor, Real.sqrt_mul (sq_nonneg (Real.cos x)), Real.sqrt_sq hcos.le]
  rw [hsqrt] at hcomp
  have hsqrt_pos : 0 < Real.sqrt (1 + Real.sin x ^ 2) := by positivity
  have hfun : adsHalfArcsinSinSq =
      fun y => (Real.arcsin ∘ (Real.sin ^ 2)) y / 2 := by
    funext y
    simp [adsHalfArcsinSinSq, Function.comp_apply]
  rw [hfun]
  change HasDerivAt _ (Real.sin x / Real.sqrt (1 + Real.sin x ^ 2)) x
  convert hcomp.div_const 2 using 1
  simp only [Nat.cast_ofNat, Nat.reduceSub, pow_one]
  field_simp [ne_of_gt hcos, ne_of_gt hsqrt_pos]

private lemma ads_halfArcsinSinSq_continuous : Continuous adsHalfArcsinSinSq := by
  exact (Real.continuous_arcsin.comp (Real.continuous_sin.pow 2)).div_const 2

private lemma ads_halfArcsinSinSq_endpoints :
    adsHalfArcsinSinSq 0 = 0 ∧
      adsHalfArcsinSinSq (Real.pi / 2) = Real.pi / 4 := by
  constructor
  · simp [adsHalfArcsinSinSq]
  · rw [adsHalfArcsinSinSq, Real.sin_pi_div_two, one_pow, Real.arcsin_one]
    ring

private lemma ads_halfArcsinSinSqDeriv_nonneg {x : ℝ}
    (hx : x ∈ Set.Ioo 0 (Real.pi / 2)) :
    0 ≤ adsHalfArcsinSinSqDeriv x := by
  rw [Set.mem_Ioo] at hx
  unfold adsHalfArcsinSinSqDeriv
  exact div_nonneg
    (le_of_lt (Real.sin_pos_of_pos_of_lt_pi hx.1 (by linarith [hx.2, Real.pi_pos])))
    (Real.sqrt_nonneg _)

private lemma ads_substitution_integrand_eq {x : ℝ}
    (hx : x ∈ Set.Ioo 0 (Real.pi / 2)) :
    (adsRawIntegrand ∘ adsHalfArcsinSinSq) x * adsHalfArcsinSinSqDeriv x =
      Real.arcsin (Real.sin x ^ 2) / Real.sin x := by
  rw [Set.mem_Ioo] at hx
  have hsin : 0 < Real.sin x :=
    Real.sin_pos_of_pos_of_lt_pi hx.1 (by linarith [hx.2, Real.pi_pos])
  have hcos : 0 < Real.cos x :=
    Real.cos_pos_of_mem_Ioo ⟨by linarith [Real.pi_pos, hx.1], hx.2⟩
  have hsin_sq_le : Real.sin x ^ 2 ≤ 1 := by
    nlinarith [Real.sin_sq_add_cos_sq x, sq_nonneg (Real.cos x)]
  have hsin_arcsin : Real.sin (Real.arcsin (Real.sin x ^ 2)) = Real.sin x ^ 2 :=
    Real.sin_arcsin (by nlinarith [sq_nonneg (Real.sin x)]) hsin_sq_le
  have hsqrt : 0 < Real.sqrt (1 + Real.sin x ^ 2) := by positivity
  simp only [Function.comp_apply, adsRawIntegrand, adsHalfArcsinSinSqDeriv,
    adsHalfArcsinSinSq]
  rw [show 2 * (Real.arcsin (Real.sin x ^ 2) / 2) =
    Real.arcsin (Real.sin x ^ 2) by ring, hsin_arcsin]
  field_simp [ne_of_gt hsin, ne_of_gt hsqrt]

private lemma ads_integral_eq_raw :
    (∫ x in (0 : ℝ)..(Real.pi / 2),
      Real.arcsin (Real.sin x ^ 2) / Real.sin x) =
      ∫ x in (0 : ℝ)..(Real.pi / 4), adsRawIntegrand x := by
  have hpi : (0 : ℝ) ≤ Real.pi / 2 := by positivity
  have hchange := intervalIntegral.integral_comp_mul_deriv_of_deriv_nonneg
    (a := (0 : ℝ)) (b := Real.pi / 2) (f := adsHalfArcsinSinSq)
    (f' := adsHalfArcsinSinSqDeriv) (g := adsRawIntegrand)
    ads_halfArcsinSinSq_continuous.continuousOn
    (fun x hx => ads_halfArcsinSinSq_hasDerivAt (by
      simpa [min_eq_left hpi, max_eq_right hpi] using hx))
    (fun x hx => ads_halfArcsinSinSqDeriv_nonneg (by
      simpa [min_eq_left hpi, max_eq_right hpi] using hx))
  rw [ads_halfArcsinSinSq_endpoints.1, ads_halfArcsinSinSq_endpoints.2] at hchange
  calc
    (∫ x in (0 : ℝ)..(Real.pi / 2),
        Real.arcsin (Real.sin x ^ 2) / Real.sin x) =
        ∫ x in (0 : ℝ)..(Real.pi / 2),
          (adsRawIntegrand ∘ adsHalfArcsinSinSq) x *
            adsHalfArcsinSinSqDeriv x := by
      apply intervalIntegral.integral_congr_codiscreteWithin
      filter_upwards [Filter.self_mem_codiscreteWithin
        (Set.uIoc (0 : ℝ) (Real.pi / 2)),
        compl_singleton_mem_codiscreteWithin (s := Set.uIoc (0 : ℝ) (Real.pi / 2))
          (Real.pi / 2)] with x hx hne
      rw [Set.uIoc_of_le (by positivity), Set.mem_Ioc] at hx
      simp only [Set.mem_compl_iff, Set.mem_singleton_iff] at hne
      exact (ads_substitution_integrand_eq
        ⟨hx.1, lt_of_le_of_ne hx.2 hne⟩).symm
    _ = ∫ x in (0 : ℝ)..(Real.pi / 4), adsRawIntegrand x := hchange

private lemma ads_sqrt_one_add_sin_two_mul {x : ℝ}
    (hx : x ∈ Set.Icc 0 (Real.pi / 4)) :
    Real.sqrt (1 + Real.sin (2 * x)) = Real.sin x + Real.cos x := by
  rw [Set.mem_Icc] at hx
  have hsin : 0 ≤ Real.sin x :=
    Real.sin_nonneg_of_nonneg_of_le_pi hx.1 (by linarith [hx.2, Real.pi_pos])
  have hcos : 0 ≤ Real.cos x := le_of_lt (Real.cos_pos_of_mem_Ioo
    ⟨by linarith [hx.1, Real.pi_pos], by linarith [hx.2, Real.pi_pos]⟩)
  have hsq : 1 + Real.sin (2 * x) = (Real.sin x + Real.cos x) ^ 2 := by
    rw [Real.sin_two_mul]
    nlinarith [Real.sin_sq_add_cos_sq x]
  rw [hsq, Real.sqrt_sq_eq_abs, abs_of_nonneg (add_nonneg hsin hcos)]

private lemma ads_rawIntegrand_eq_j {x : ℝ}
    (hx : x ∈ Set.Ioc 0 (Real.pi / 4)) :
    adsRawIntegrand x = adsJIntegrand x := by
  rw [Set.mem_Ioc] at hx
  have hsin : 0 < Real.sin x :=
    Real.sin_pos_of_pos_of_lt_pi hx.1 (by linarith [hx.2, Real.pi_pos])
  have hcos : 0 < Real.cos x := Real.cos_pos_of_mem_Ioo
    ⟨by linarith [hx.1, Real.pi_pos], by linarith [hx.2, Real.pi_pos]⟩
  rw [adsRawIntegrand, adsJIntegrand,
    ads_sqrt_one_add_sin_two_mul ⟨le_of_lt hx.1, hx.2⟩, Real.sin_two_mul]
  field_simp [ne_of_gt hsin, ne_of_gt hcos]

private lemma ads_integral_eq_j :
    (∫ x in (0 : ℝ)..(Real.pi / 2),
      Real.arcsin (Real.sin x ^ 2) / Real.sin x) =
      ∫ x in (0 : ℝ)..(Real.pi / 4), adsJIntegrand x := by
  rw [ads_integral_eq_raw]
  apply intervalIntegral.integral_congr_codiscreteWithin
  filter_upwards [Filter.self_mem_codiscreteWithin
    (Set.uIoc (0 : ℝ) (Real.pi / 4))] with x hx
  rw [Set.uIoc_of_le (by positivity)] at hx
  exact ads_rawIntegrand_eq_j hx

private lemma ads_logTanHalf_hasDerivAt {x : ℝ}
    (hx : x ∈ Set.Ioo 0 (Real.pi / 2)) :
    HasDerivAt adsLogTanHalf (1 / Real.sin x) x := by
  rw [Set.mem_Ioo] at hx
  have hu : x / 2 ∈ Set.Ioo 0 (Real.pi / 2) := by
    constructor <;> linarith [hx.1, hx.2]
  have hsin : 0 < Real.sin (x / 2) :=
    Real.sin_pos_of_pos_of_lt_pi hu.1 (by linarith [hu.2, Real.pi_pos])
  have hcos : 0 < Real.cos (x / 2) := Real.cos_pos_of_mem_Ioo
    ⟨by linarith [hu.1, Real.pi_pos], hu.2⟩
  have htan : 0 < Real.tan (x / 2) := by
    rw [Real.tan_eq_sin_div_cos]
    exact div_pos hsin hcos
  have hinner : HasDerivAt (fun y : ℝ => y / 2) (1 / 2) x :=
    (hasDerivAt_id x).div_const 2
  have htan_deriv := (Real.hasDerivAt_tan (ne_of_gt hcos)).comp x hinner
  have hlog := (Real.hasDerivAt_log (ne_of_gt htan)).comp x htan_deriv
  have hsin_two : Real.sin x = 2 * Real.sin (x / 2) * Real.cos (x / 2) := by
    nth_rewrite 1 [show x = 2 * (x / 2) by ring]
    rw [Real.sin_two_mul]
  have hval : (Real.tan (x / 2))⁻¹ *
      (1 / Real.cos (x / 2) ^ 2 * (1 / 2)) = 1 / Real.sin x := by
    rw [Real.tan_eq_sin_div_cos, hsin_two]
    field_simp [ne_of_gt hsin, ne_of_gt hcos]
  rw [hval] at hlog
  have hfun : adsLogTanHalf = Real.log ∘ Real.tan ∘ fun y : ℝ => y / 2 := by
    funext y
    rfl
  rw [hfun]
  exact hlog

private lemma ads_logTanShift_hasDerivAt {x : ℝ}
    (hx : x ∈ Set.Ioo 0 (Real.pi / 2)) :
    HasDerivAt adsLogTanShift (1 / Real.cos x) x := by
  rw [Set.mem_Ioo] at hx
  let u := x / 2 + Real.pi / 4
  have hu : u ∈ Set.Ioo 0 (Real.pi / 2) := by
    dsimp [u]
    constructor <;> linarith [hx.1, hx.2, Real.pi_pos]
  have hsin : 0 < Real.sin u :=
    Real.sin_pos_of_pos_of_lt_pi hu.1 (by linarith [hu.2, Real.pi_pos])
  have hcos : 0 < Real.cos u := Real.cos_pos_of_mem_Ioo
    ⟨by linarith [hu.1, Real.pi_pos], hu.2⟩
  have htan : 0 < Real.tan u := by
    rw [Real.tan_eq_sin_div_cos]
    exact div_pos hsin hcos
  have hinner : HasDerivAt (fun y : ℝ => y / 2 + Real.pi / 4) (1 / 2) x :=
    (hasDerivAt_id x).div_const 2 |>.add_const (Real.pi / 4)
  have htan_deriv := (Real.hasDerivAt_tan (ne_of_gt hcos)).comp x hinner
  have hlog := (Real.hasDerivAt_log (ne_of_gt htan)).comp x htan_deriv
  have hsin_two : Real.sin (2 * u) = Real.cos x := by
    rw [show 2 * u = x + Real.pi / 2 by dsimp [u]; ring, Real.sin_add_pi_div_two]
  have hval : (Real.tan u)⁻¹ * (1 / Real.cos u ^ 2 * (1 / 2)) =
      1 / Real.cos x := by
    rw [Real.tan_eq_sin_div_cos, ← hsin_two, Real.sin_two_mul]
    field_simp [ne_of_gt hsin, ne_of_gt hcos]
  rw [hval] at hlog
  have hfun : adsLogTanShift = Real.log ∘ Real.tan ∘
      fun y : ℝ => y / 2 + Real.pi / 4 := by
    funext y
    rfl
  rw [hfun]
  exact hlog

private lemma ads_sinc_pos_of_mem_Icc {x : ℝ}
    (hx : x ∈ Set.Icc 0 (Real.pi / 4)) : 0 < Real.sinc x := by
  by_cases hzero : x = 0
  · subst x
    simp
  · rw [Real.sinc_of_ne_zero hzero]
    rw [Set.mem_Icc] at hx
    have hxpos : 0 < x := lt_of_le_of_ne hx.1 (Ne.symm hzero)
    exact div_pos
      (Real.sin_pos_of_pos_of_lt_pi hxpos (by linarith [hx.2, Real.pi_pos])) hxpos

private lemma ads_sin_eq_mul_sinc (x : ℝ) :
    Real.sin x = x * Real.sinc x := by
  by_cases hzero : x = 0
  · subst x
    simp
  · rw [Real.sinc_of_ne_zero hzero]
    field_simp

private lemma ads_intervalIntegrable_x_div_sin :
    IntervalIntegrable (fun x : ℝ => x / Real.sin x) volume 0 (Real.pi / 4) := by
  have hpi : (0 : ℝ) ≤ Real.pi / 4 := by positivity
  have hcont : ContinuousOn (fun x : ℝ => (Real.sinc x)⁻¹)
      (Set.uIcc 0 (Real.pi / 4)) := by
    apply Real.continuous_sinc.continuousOn.inv₀
    intro x hx
    apply ne_of_gt
    apply ads_sinc_pos_of_mem_Icc
    simpa [Set.uIcc_of_le hpi] using hx
  have hint : IntervalIntegrable (fun x : ℝ => (Real.sinc x)⁻¹)
      volume 0 (Real.pi / 4) := hcont.intervalIntegrable
  have heq : Set.EqOn (fun x : ℝ => x / Real.sin x)
      (fun x : ℝ => (Real.sinc x)⁻¹) (Set.uIoc 0 (Real.pi / 4)) := by
    intro x hx
    rw [Set.uIoc_of_le hpi, Set.mem_Ioc] at hx
    change x / Real.sin x = (Real.sinc x)⁻¹
    rw [ads_sin_eq_mul_sinc]
    field_simp [ne_of_gt hx.1]
  exact (intervalIntegrable_congr heq).mpr hint

private lemma ads_intervalIntegrable_x_div_cos :
    IntervalIntegrable (fun x : ℝ => x / Real.cos x) volume 0 (Real.pi / 4) := by
  have hpi : (0 : ℝ) ≤ Real.pi / 4 := by positivity
  apply ContinuousOn.intervalIntegrable
  apply continuousOn_id.div Real.continuous_cos.continuousOn
  intro x hx
  rw [Set.uIcc_of_le hpi, Set.mem_Icc] at hx
  apply ne_of_gt
  exact Real.cos_pos_of_mem_Ioo
    ⟨by linarith [hx.1, Real.pi_pos], by linarith [hx.2, Real.pi_pos]⟩

private lemma ads_logTanHalf_intervalIntegrable :
    IntervalIntegrable adsLogTanHalf volume 0 (Real.pi / 4) := by
  have hsin : IntervalIntegrable (fun x : ℝ => Real.log (Real.sin (x / 2)))
      volume 0 (Real.pi / 4) := by
    convert
      (intervalIntegrable_log_sin (a := (0 : ℝ)) (b := Real.pi / 8)).comp_mul_left
        (c := (1 / 2 : ℝ)) using 1 <;> norm_num <;> ring_nf
  have hcos : IntervalIntegrable (fun x : ℝ => Real.log (Real.cos (x / 2)))
      volume 0 (Real.pi / 4) := by
    convert
      (intervalIntegrable_log_cos (a := (0 : ℝ)) (b := Real.pi / 8)).comp_mul_left
        (c := (1 / 2 : ℝ)) using 1 <;> norm_num <;> ring_nf
  have hsub := hsin.sub hcos
  have heq : Set.EqOn
      (fun x : ℝ => Real.log (Real.sin (x / 2)) - Real.log (Real.cos (x / 2)))
      adsLogTanHalf (Set.uIoc 0 (Real.pi / 4)) := by
    intro x hx
    rw [Set.uIoc_of_le (by positivity), Set.mem_Ioc] at hx
    have hs : Real.sin (x / 2) ≠ 0 := ne_of_gt
      (Real.sin_pos_of_pos_of_lt_pi (by linarith [hx.1])
        (by linarith [hx.2, Real.pi_pos]))
    have hc : Real.cos (x / 2) ≠ 0 := ne_of_gt (Real.cos_pos_of_mem_Ioo
      ⟨by linarith [hx.1, Real.pi_pos], by linarith [hx.2, Real.pi_pos]⟩)
    unfold adsLogTanHalf
    rw [Real.tan_eq_sin_div_cos, Real.log_div hs hc]
  exact (intervalIntegrable_congr heq).mp hsub

private lemma ads_logTanShift_intervalIntegrable :
    IntervalIntegrable adsLogTanShift volume 0 (Real.pi / 4) := by
  have hsin : IntervalIntegrable
      (fun x : ℝ => Real.log (Real.sin (x / 2 + Real.pi / 4)))
      volume 0 (Real.pi / 4) := by
    convert ((intervalIntegrable_log_sin (a := Real.pi / 4)
      (b := 3 * Real.pi / 8)).comp_add_right (Real.pi / 4)).comp_mul_left
        (c := (1 / 2 : ℝ)) using 1 <;> norm_num <;> try ring_nf
    funext x
    rw [add_comm]
  have hcos : IntervalIntegrable
      (fun x : ℝ => Real.log (Real.cos (x / 2 + Real.pi / 4)))
      volume 0 (Real.pi / 4) := by
    convert ((intervalIntegrable_log_cos (a := Real.pi / 4)
      (b := 3 * Real.pi / 8)).comp_add_right (Real.pi / 4)).comp_mul_left
        (c := (1 / 2 : ℝ)) using 1 <;> norm_num <;> try ring_nf
    funext x
    rw [add_comm]
  have hsub := hsin.sub hcos
  have heq : Set.EqOn
      (fun x : ℝ => Real.log (Real.sin (x / 2 + Real.pi / 4)) -
        Real.log (Real.cos (x / 2 + Real.pi / 4)))
      adsLogTanShift (Set.uIoc 0 (Real.pi / 4)) := by
    intro x hx
    rw [Set.uIoc_of_le (by positivity), Set.mem_Ioc] at hx
    have hu : x / 2 + Real.pi / 4 ∈ Set.Ioo 0 (Real.pi / 2) := by
      constructor <;> linarith [hx.1, hx.2, Real.pi_pos]
    have hs : Real.sin (x / 2 + Real.pi / 4) ≠ 0 := ne_of_gt
      (Real.sin_pos_of_pos_of_lt_pi hu.1 (by linarith [hu.2, Real.pi_pos]))
    have hc : Real.cos (x / 2 + Real.pi / 4) ≠ 0 := ne_of_gt
      (Real.cos_pos_of_mem_Ioo ⟨by linarith [hu.1, Real.pi_pos], hu.2⟩)
    unfold adsLogTanShift
    rw [Real.tan_eq_sin_div_cos, Real.log_div hs hc]
  exact (intervalIntegrable_congr heq).mp hsub

private lemma ads_halfProduct_continuousOn :
    ContinuousOn (fun x : ℝ => x * adsLogTanHalf x) (Set.Icc 0 (Real.pi / 4)) := by
  have harg : Continuous fun x : ℝ => x / 2 := continuous_id.div_const 2
  have hmulLog : Continuous fun x : ℝ =>
      2 * ((x / 2) * Real.log (x / 2)) := by
    exact continuous_const.mul (Real.continuous_mul_log.comp harg)
  have hlogSinc : ContinuousOn (fun x : ℝ => Real.log (Real.sinc (x / 2)))
      (Set.Icc 0 (Real.pi / 4)) := by
    apply Real.continuousOn_log.comp (Real.continuous_sinc.comp harg).continuousOn
    intro x hx
    simp only [Set.mem_compl_iff, Set.mem_singleton_iff]
    apply ne_of_gt
    apply ads_sinc_pos_of_mem_Icc
    rw [Set.mem_Icc] at hx ⊢
    constructor <;> linarith [hx.1, hx.2]
  have hlogCos : ContinuousOn (fun x : ℝ => Real.log (Real.cos (x / 2)))
      (Set.Icc 0 (Real.pi / 4)) := by
    apply Real.continuousOn_log.comp (Real.continuous_cos.comp harg).continuousOn
    intro x hx
    simp only [Set.mem_compl_iff, Set.mem_singleton_iff]
    rw [Set.mem_Icc] at hx
    exact ne_of_gt (Real.cos_pos_of_mem_Ioo
      ⟨by linarith [hx.1, Real.pi_pos], by linarith [hx.2, Real.pi_pos]⟩)
  have hrhs : ContinuousOn (fun x : ℝ =>
      2 * ((x / 2) * Real.log (x / 2)) + x * Real.log (Real.sinc (x / 2)) -
        x * Real.log (Real.cos (x / 2))) (Set.Icc 0 (Real.pi / 4)) :=
    hmulLog.continuousOn.add (continuousOn_id.mul hlogSinc) |>.sub
      (continuousOn_id.mul hlogCos)
  apply hrhs.congr
  intro x hx
  by_cases hzero : x = 0
  · subst x
    simp [adsLogTanHalf]
  · rw [Set.mem_Icc] at hx
    have hxpos : 0 < x := lt_of_le_of_ne hx.1 (Ne.symm hzero)
    have hhalf : x / 2 ≠ 0 := by positivity
    have hsinc : Real.sinc (x / 2) ≠ 0 := ne_of_gt (ads_sinc_pos_of_mem_Icc <| by
      rw [Set.mem_Icc]
      constructor <;> linarith [hx.1, hx.2])
    have hsin : Real.sin (x / 2) ≠ 0 := ne_of_gt
      (Real.sin_pos_of_pos_of_lt_pi (by positivity)
        (by linarith [hx.2, Real.pi_pos]))
    have hcos : Real.cos (x / 2) ≠ 0 := ne_of_gt (Real.cos_pos_of_mem_Ioo
      ⟨by linarith [hxpos, Real.pi_pos], by linarith [hx.2, Real.pi_pos]⟩)
    change x * Real.log (Real.tan (x / 2)) =
      2 * ((x / 2) * Real.log (x / 2)) + x * Real.log (Real.sinc (x / 2)) -
        x * Real.log (Real.cos (x / 2))
    rw [Real.tan_eq_sin_div_cos, Real.log_div hsin hcos,
      ads_sin_eq_mul_sinc, Real.log_mul hhalf hsinc]
    ring

private lemma ads_logTanShift_continuousOn :
    ContinuousOn adsLogTanShift (Set.Icc 0 (Real.pi / 4)) := by
  have harg : Continuous fun x : ℝ => x / 2 + Real.pi / 4 :=
    (continuous_id.div_const 2).add continuous_const
  have htan : ContinuousOn (fun x : ℝ => Real.tan (x / 2 + Real.pi / 4))
      (Set.Icc 0 (Real.pi / 4)) := by
    apply Real.continuousOn_tan_Ioo.comp harg.continuousOn
    intro x hx
    rw [Set.mem_Icc] at hx
    constructor <;> linarith [hx.1, hx.2, Real.pi_pos]
  unfold adsLogTanShift
  apply Real.continuousOn_log.comp htan
  intro x hx
  simp only [Set.mem_compl_iff, Set.mem_singleton_iff]
  rw [Set.mem_Icc] at hx
  have hs : 0 < Real.sin (x / 2 + Real.pi / 4) :=
    Real.sin_pos_of_pos_of_lt_pi (by linarith [hx.1, Real.pi_pos])
      (by linarith [hx.2, Real.pi_pos])
  have hc : 0 < Real.cos (x / 2 + Real.pi / 4) := Real.cos_pos_of_mem_Ioo
    ⟨by linarith [hx.1, Real.pi_pos], by linarith [hx.2, Real.pi_pos]⟩
  rw [Real.tan_eq_sin_div_cos]
  exact ne_of_gt (div_pos hs hc)

private lemma ads_logTanProducts_continuousOn :
    ContinuousOn adsLogTanProducts (Set.Icc 0 (Real.pi / 4)) := by
  unfold adsLogTanProducts
  exact ads_halfProduct_continuousOn.add
    (continuousOn_id.mul ads_logTanShift_continuousOn)

private lemma ads_logTanProducts_hasDerivAt {x : ℝ}
    (hx : x ∈ Set.Ioo 0 (Real.pi / 4)) :
    HasDerivAt adsLogTanProducts
      (adsLogTanHalf x + x / Real.sin x + adsLogTanShift x + x / Real.cos x) x := by
  have hx' : x ∈ Set.Ioo 0 (Real.pi / 2) := by
    rw [Set.mem_Ioo] at hx ⊢
    exact ⟨hx.1, by linarith [hx.2, Real.pi_pos]⟩
  have hhalf := (hasDerivAt_id x).mul (ads_logTanHalf_hasDerivAt hx')
  have hshift := (hasDerivAt_id x).mul (ads_logTanShift_hasDerivAt hx')
  change HasDerivAt (fun y : ℝ =>
    y * adsLogTanHalf y + y * adsLogTanShift y) _ x
  have hfun : (id * adsLogTanHalf + id * adsLogTanShift : ℝ → ℝ) =
      fun y : ℝ => y * adsLogTanHalf y + y * adsLogTanShift y := by
    funext y
    rfl
  rw [← hfun]
  simpa only [Pi.add_apply, Pi.mul_apply, id_eq, one_mul, div_eq_mul_inv,
    add_assoc] using hhalf.add hshift

private lemma ads_logTanProducts_deriv_intervalIntegrable :
    IntervalIntegrable (fun x : ℝ =>
      adsLogTanHalf x + x / Real.sin x + adsLogTanShift x + x / Real.cos x)
      volume 0 (Real.pi / 4) :=
  ((ads_logTanHalf_intervalIntegrable.add ads_intervalIntegrable_x_div_sin).add
    ads_logTanShift_intervalIntegrable).add ads_intervalIntegrable_x_div_cos

private lemma ads_logTanProducts_endpoints :
    adsLogTanProducts 0 = 0 ∧ adsLogTanProducts (Real.pi / 4) = 0 := by
  constructor
  · simp [adsLogTanProducts]
  · have ht : Real.tan (3 * Real.pi / 8) = (Real.tan (Real.pi / 8))⁻¹ := by
      rw [show 3 * Real.pi / 8 = Real.pi / 2 - Real.pi / 8 by ring,
        Real.tan_pi_div_two_sub]
    have hlogs : Real.log (Real.tan (Real.pi / 8)) +
        Real.log (Real.tan (3 * Real.pi / 8)) = 0 := by
      rw [ht, Real.log_inv, add_neg_cancel]
    rw [adsLogTanProducts, adsLogTanHalf, adsLogTanShift,
      show (Real.pi / 4) / 2 = Real.pi / 8 by ring,
      show Real.pi / 8 + Real.pi / 4 = 3 * Real.pi / 8 by ring]
    calc
      Real.pi / 4 * Real.log (Real.tan (Real.pi / 8)) +
          Real.pi / 4 * Real.log (Real.tan (3 * Real.pi / 8)) =
          Real.pi / 4 * (Real.log (Real.tan (Real.pi / 8)) +
            Real.log (Real.tan (3 * Real.pi / 8))) := by ring
      _ = 0 := by rw [hlogs, mul_zero]

private lemma ads_logTan_intervalIntegrable (a b : ℝ) :
    IntervalIntegrable (fun x : ℝ => Real.log (Real.tan x)) volume a b := by
  have hsub := (intervalIntegrable_log_sin (a := a) (b := b)).sub
    (intervalIntegrable_log_cos (a := a) (b := b))
  have hsin : Real.sin ⁻¹' {0}ᶜ ∈ Filter.codiscrete ℝ :=
    Real.analyticOnNhd_sin.preimage_zero_mem_codiscrete (x := Real.pi / 2) (by simp)
  have hcos : Real.cos ⁻¹' {0}ᶜ ∈ Filter.codiscrete ℝ :=
    Real.analyticOnNhd_cos.preimage_zero_mem_codiscrete (x := 0) (by simp)
  apply hsub.congr_codiscreteWithin
  filter_upwards [Filter.codiscreteWithin_mono (Set.subset_univ _) hsin,
    Filter.codiscreteWithin_mono (Set.subset_univ _) hcos] with x hs hc
  simp only [Set.preimage_compl, Set.mem_compl_iff, Set.mem_preimage,
    Set.mem_singleton_iff] at hs hc
  simp only [Function.comp_apply]
  rw [Real.tan_eq_sin_div_cos, Real.log_div hs hc]

private lemma ads_integral_log_terms_and_j_eq_zero :
    (∫ x in (0 : ℝ)..(Real.pi / 4),
      adsLogTanHalf x + x / Real.sin x + adsLogTanShift x + x / Real.cos x) = 0 := by
  have hftc := intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le
    (a := (0 : ℝ)) (b := Real.pi / 4) (f := adsLogTanProducts)
    (f' := fun x : ℝ =>
      adsLogTanHalf x + x / Real.sin x + adsLogTanShift x + x / Real.cos x)
    (by positivity) ads_logTanProducts_continuousOn
    (fun x hx => ads_logTanProducts_hasDerivAt hx)
    ads_logTanProducts_deriv_intervalIntegrable
  rw [ads_logTanProducts_endpoints.1, ads_logTanProducts_endpoints.2, sub_zero] at hftc
  exact hftc

private lemma ads_j_eq_log_integrals :
    (∫ x in (0 : ℝ)..(Real.pi / 4), adsJIntegrand x) =
      -(∫ x in (0 : ℝ)..(Real.pi / 4), adsLogTanHalf x) -
        ∫ x in (0 : ℝ)..(Real.pi / 4), adsLogTanShift x := by
  have hzero := ads_integral_log_terms_and_j_eq_zero
  rw [intervalIntegral.integral_add
      ((ads_logTanHalf_intervalIntegrable.add ads_intervalIntegrable_x_div_sin).add
        ads_logTanShift_intervalIntegrable)
      ads_intervalIntegrable_x_div_cos,
    intervalIntegral.integral_add
      (ads_logTanHalf_intervalIntegrable.add ads_intervalIntegrable_x_div_sin)
      ads_logTanShift_intervalIntegrable,
    intervalIntegral.integral_add ads_logTanHalf_intervalIntegrable
      ads_intervalIntegrable_x_div_sin] at hzero
  have hj : (∫ x in (0 : ℝ)..(Real.pi / 4), adsJIntegrand x) =
      (∫ x in (0 : ℝ)..(Real.pi / 4), x / Real.cos x) +
        ∫ x in (0 : ℝ)..(Real.pi / 4), x / Real.sin x := by
    rw [← intervalIntegral.integral_add ads_intervalIntegrable_x_div_cos
      ads_intervalIntegrable_x_div_sin]
    apply intervalIntegral.integral_congr
    intro x _
    unfold adsJIntegrand
    ring
  rw [hj]
  linarith

private lemma ads_integral_logTanHalf :
    (∫ x in (0 : ℝ)..(Real.pi / 4), adsLogTanHalf x) =
      2 * adsLogTanIntegral (Real.pi / 8) := by
  unfold adsLogTanHalf adsLogTanIntegral
  convert intervalIntegral.integral_comp_div
    (a := (0 : ℝ)) (b := Real.pi / 4) (c := (2 : ℝ))
    (fun x : ℝ => Real.log (Real.tan x)) (by norm_num) using 1
  all_goals norm_num
  all_goals ring_nf

private lemma ads_integral_logTanShift :
    (∫ x in (0 : ℝ)..(Real.pi / 4), adsLogTanShift x) =
      2 * (adsLogTanIntegral (3 * Real.pi / 8) -
        adsLogTanIntegral (Real.pi / 4)) := by
  have hcomp : (∫ x in (0 : ℝ)..(Real.pi / 4), adsLogTanShift x) =
      2 * ∫ x in (Real.pi / 4)..(3 * Real.pi / 8),
        Real.log (Real.tan x) := by
    unfold adsLogTanShift
    convert intervalIntegral.integral_comp_mul_add
      (a := (0 : ℝ)) (b := Real.pi / 4) (c := (1 / 2 : ℝ))
      (fun x : ℝ => Real.log (Real.tan x)) (by norm_num) (Real.pi / 4) using 1
    all_goals norm_num
    all_goals ring_nf
    apply intervalIntegral.integral_congr
    intro x _
    change Real.log (Real.tan (x * (1 / 2) + Real.pi * (1 / 4))) =
      Real.log (Real.tan (Real.pi * (1 / 4) + x * (1 / 2)))
    rw [add_comm]
  have hadd := intervalIntegral.integral_add_adjacent_intervals
    (ads_logTan_intervalIntegrable 0 (Real.pi / 4))
    (ads_logTan_intervalIntegrable (Real.pi / 4) (3 * Real.pi / 8))
  unfold adsLogTanIntegral
  rw [hcomp]
  linarith

private lemma ads_logTan_reflection (a : ℝ) :
    (∫ x in (Real.pi / 2 - a)..(Real.pi / 2), Real.log (Real.tan x)) =
      -adsLogTanIntegral a := by
  have hfun : (fun x : ℝ => Real.log (Real.tan (Real.pi / 2 - x))) =
      fun x : ℝ => -Real.log (Real.tan x) := by
    funext x
    rw [Real.tan_pi_div_two_sub, Real.log_inv]
  have hsubst := intervalIntegral.integral_comp_sub_left
    (a := (0 : ℝ)) (b := a) (fun x : ℝ => Real.log (Real.tan x)) (Real.pi / 2)
  rw [hfun, intervalIntegral.integral_neg] at hsubst
  simpa [adsLogTanIntegral] using hsubst.symm

private lemma ads_logTanIntegral_pi_div_two :
    adsLogTanIntegral (Real.pi / 2) = 0 := by
  have h : adsLogTanIntegral (Real.pi / 2) =
      -adsLogTanIntegral (Real.pi / 2) := by
    simpa [adsLogTanIntegral] using ads_logTan_reflection (Real.pi / 2)
  linarith

private lemma ads_logTanIntegral_three_pi_div_eight :
    adsLogTanIntegral (3 * Real.pi / 8) = adsLogTanIntegral (Real.pi / 8) := by
  have href := ads_logTan_reflection (Real.pi / 8)
  rw [show Real.pi / 2 - Real.pi / 8 = 3 * Real.pi / 8 by ring] at href
  have hadd : adsLogTanIntegral (3 * Real.pi / 8) +
      (∫ x in (3 * Real.pi / 8)..(Real.pi / 2), Real.log (Real.tan x)) =
      adsLogTanIntegral (Real.pi / 2) := by
    simpa [adsLogTanIntegral] using intervalIntegral.integral_add_adjacent_intervals
      (ads_logTan_intervalIntegrable 0 (3 * Real.pi / 8))
      (ads_logTan_intervalIntegrable (3 * Real.pi / 8) (Real.pi / 2))
  rw [href, ads_logTanIntegral_pi_div_two] at hadd
  linarith

private lemma ads_integral_eq_logTan_values :
    (∫ x in (0 : ℝ)..(Real.pi / 2),
      Real.arcsin (Real.sin x ^ 2) / Real.sin x) =
      -4 * adsLogTanIntegral (Real.pi / 8) +
        2 * adsLogTanIntegral (Real.pi / 4) := by
  rw [ads_integral_eq_j, ads_j_eq_log_integrals, ads_integral_logTanHalf,
    ads_integral_logTanShift, ads_logTanIntegral_three_pi_div_eight]
  ring

private lemma ads_base_summable :
    Summable (fun k : ℕ => (1 : ℝ) / (((2 * k + 1 : ℕ) : ℝ) ^ 2)) := by
  have h := (Real.summable_one_div_nat_pow (p := 2)).mpr (by norm_num)
  exact h.comp_injective (by
    intro a b hab
    dsimp only at hab
    omega)

private def adsSr (r x : ℝ) : ℝ :=
  ∑' k : ℕ, r ^ (2 * k + 1) * Real.sin (2 * ((2 * k + 1 : ℕ) : ℝ) * x) /
    (((2 * k + 1 : ℕ) : ℝ) ^ 2)

private def adsDr (r x : ℝ) : ℝ :=
  ∑' k : ℕ, r ^ (2 * k + 1) * 2 * Real.cos (2 * ((2 * k + 1 : ℕ) : ℝ) * x) /
    ((2 * k + 1 : ℕ) : ℝ)

private def adsDrClosed (r x : ℝ) : ℝ :=
  Real.log ((1 + 2 * r * Real.cos (2 * x) + r ^ 2) /
    (1 - 2 * r * Real.cos (2 * x) + r ^ 2)) / 2

private def adsRho (n : ℕ) : ℝ :=
  1 - 1 / ((n : ℝ) + 1)

private lemma ads_odd_hasSum {z : ℂ} (hz : ‖z‖ < 1) :
    HasSum (fun k : ℕ => z ^ (2 * k + 1) / ((2 * k + 1 : ℕ) : ℂ))
      ((-Complex.log (1 - z) + Complex.log (1 + z)) / 2) := by
  have h₁ := Complex.hasSum_taylorSeries_neg_log (z := z) hz
  have h₂ := Complex.hasSum_taylorSeries_neg_log (z := -z) (by simpa using hz)
  rw [show (1 : ℂ) - -z = 1 + z by ring] at h₂
  have hdiv := (h₁.sub h₂).div_const (2 : ℂ)
  have hval : (-Complex.log (1 - z) - -Complex.log (1 + z)) / 2 =
      (-Complex.log (1 - z) + Complex.log (1 + z)) / 2 := by ring
  rw [hval] at hdiv
  replace hdiv := (Nat.divModEquiv 2).symm.hasSum_iff.mpr hdiv
  simp only [Function.comp_def, Nat.divModEquiv_symm_apply] at hdiv
  simp_rw [← mul_comm 2 _] at hdiv
  refine hdiv.prod_fiberwise fun k => ?_
  dsimp only
  convert! hasSum_fintype (_ : Fin 2 → ℂ) using 1
  rw [Fin.sum_univ_two, Fin.val_zero, Fin.val_one]
  have heven : Even (2 * k + 0) := ⟨k, by ring⟩
  have hodd : Odd (2 * k + 1) := ⟨k, rfl⟩
  rw [heven.neg_pow, hodd.neg_pow]
  simp only [sub_self, zero_div, zero_add]
  rw [neg_div, sub_neg_eq_add, add_self_div_two]

private lemma ads_polar_pow (r θ : ℝ) (n : ℕ) :
    ((((r * Real.cos θ : ℝ)) : ℂ) + (((r * Real.sin θ : ℝ)) : ℂ) * Complex.I) ^ n =
      ((((r ^ n * Real.cos ((n : ℝ) * θ) : ℝ)) : ℂ) +
        (((r ^ n * Real.sin ((n : ℝ) * θ) : ℝ)) : ℂ) * Complex.I) := by
  induction n with
  | zero => simp
  | succ n ih =>
    have hcast : (((n + 1 : ℕ)) : ℝ) * θ = θ + (n : ℝ) * θ := by
      push_cast
      ring
    have hrpow : r ^ (n + 1) = r * r ^ n := pow_succ' r n
    rw [pow_succ, ih]
    apply Complex.ext
    · simp only [Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im,
        Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im,
        mul_zero, mul_one, sub_zero, add_zero]
      rw [hcast, hrpow, Real.cos_add]
      ring
    · simp only [Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im,
        Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im,
        mul_zero, mul_one, sub_zero, add_zero]
      rw [hcast, hrpow, Real.sin_add]
      ring

private lemma ads_polar_norm (r θ : ℝ) (hr : 0 ≤ r) :
    ‖((((r * Real.cos θ : ℝ)) : ℂ) +
      (((r * Real.sin θ : ℝ)) : ℂ) * Complex.I)‖ = r := by
  have hnormSq : Complex.normSq ((((r * Real.cos θ : ℝ)) : ℂ) +
      (((r * Real.sin θ : ℝ)) : ℂ) * Complex.I) = r ^ 2 := by
    rw [Complex.normSq_add_mul_I]
    have htrig := Real.cos_sq_add_sin_sq θ
    have hexpand : (r * Real.cos θ) ^ 2 + (r * Real.sin θ) ^ 2 =
        r ^ 2 * (Real.cos θ ^ 2 + Real.sin θ ^ 2) := by ring
    rw [hexpand, htrig, mul_one]
  rw [Complex.norm_def, hnormSq, Real.sqrt_sq hr]

private lemma ads_Dr_eq_closed (r x : ℝ) (hr0 : 0 ≤ r) (hr1 : r < 1) :
    adsDr r x = adsDrClosed r x := by
  unfold adsDr adsDrClosed
  set θ : ℝ := 2 * x with hθ
  set z : ℂ := (((r * Real.cos θ : ℝ) : ℂ) +
    ((r * Real.sin θ : ℝ) : ℂ) * Complex.I) with hz
  have hnorm : ‖z‖ < 1 := by
    rw [hz, ads_polar_norm r θ hr0]
    exact hr1
  have hodd := ads_odd_hasSum hnorm
  have hre := Complex.hasSum_re hodd
  have hterm (k : ℕ) : (z ^ (2 * k + 1) / ((2 * k + 1 : ℕ) : ℂ)).re =
      r ^ (2 * k + 1) * Real.cos (((2 * k + 1 : ℕ) : ℝ) * θ) /
        ((2 * k + 1 : ℕ) : ℝ) := by
    rw [← Complex.ofReal_natCast, Complex.div_ofReal_re, hz, ads_polar_pow]
    simp only [Complex.add_re, Complex.mul_re, Complex.ofReal_re,
      Complex.ofReal_im, Complex.I_re, Complex.I_im, mul_zero, mul_one,
      sub_zero, add_zero]
  have hdr : (fun k : ℕ => r ^ (2 * k + 1) * 2 *
      Real.cos (2 * ((2 * k + 1 : ℕ) : ℝ) * x) / ((2 * k + 1 : ℕ) : ℝ)) =
      fun k : ℕ => 2 * (z ^ (2 * k + 1) / ((2 * k + 1 : ℕ) : ℂ)).re := by
    funext k
    rw [hterm k]
    have harg : ((2 * k + 1 : ℕ) : ℝ) * θ =
        2 * ((2 * k + 1 : ℕ) : ℝ) * x := by
      rw [hθ]
      ring
    rw [harg]
    ring
  have htsum : (∑' k : ℕ,
      2 * (z ^ (2 * k + 1) / ((2 * k + 1 : ℕ) : ℂ)).re) =
      2 * ((-Complex.log (1 - z) + Complex.log (1 + z)) / 2).re :=
    (hre.mul_left 2).tsum_eq
  rw [hdr, htsum]
  have hz1 : z ≠ 1 := by
    intro h
    rw [h, norm_one] at hnorm
    exact (lt_irrefl 1 hnorm)
  have hzn1 : z ≠ -1 := by
    intro h
    rw [h] at hnorm
    norm_num at hnorm
  have hminus : (1 : ℂ) - z ≠ 0 := sub_ne_zero.mpr (Ne.symm hz1)
  have hplus : (1 : ℂ) + z ≠ 0 := by
    intro h
    apply hzn1
    linear_combination h
  have hplusForm : (1 : ℂ) + z =
      ((1 + r * Real.cos θ : ℝ) : ℂ) +
        ((r * Real.sin θ : ℝ) : ℂ) * Complex.I := by
    rw [hz, Complex.ofReal_add, Complex.ofReal_one]
    ring
  have hminusForm : (1 : ℂ) - z =
      ((1 - r * Real.cos θ : ℝ) : ℂ) +
        ((-(r * Real.sin θ) : ℝ) : ℂ) * Complex.I := by
    rw [hz, Complex.ofReal_sub, Complex.ofReal_one, Complex.ofReal_neg]
    ring
  have hnormPlus : Complex.normSq (1 + z) =
      1 + 2 * r * Real.cos θ + r ^ 2 := by
    rw [hplusForm, Complex.normSq_add_mul_I]
    have htrig := Real.sin_sq_add_cos_sq θ
    have hexpand : (1 + r * Real.cos θ) ^ 2 + (r * Real.sin θ) ^ 2 =
        1 + 2 * r * Real.cos θ +
          r ^ 2 * (Real.sin θ ^ 2 + Real.cos θ ^ 2) := by ring
    rw [hexpand, htrig, mul_one]
  have hnormMinus : Complex.normSq (1 - z) =
      1 - 2 * r * Real.cos θ + r ^ 2 := by
    rw [hminusForm, Complex.normSq_add_mul_I]
    have htrig := Real.sin_sq_add_cos_sq θ
    have hexpand : (1 - r * Real.cos θ) ^ 2 + (-(r * Real.sin θ)) ^ 2 =
        1 - 2 * r * Real.cos θ +
          r ^ 2 * (Real.sin θ ^ 2 + Real.cos θ ^ 2) := by ring
    rw [hexpand, htrig, mul_one]
  have hplusPos : 0 < 1 + 2 * r * Real.cos θ + r ^ 2 := by
    rw [← hnormPlus]
    exact Complex.normSq_pos.mpr hplus
  have hminusPos : 0 < 1 - 2 * r * Real.cos θ + r ^ 2 := by
    rw [← hnormMinus]
    exact Complex.normSq_pos.mpr hminus
  have hreLog : ((-Complex.log (1 - z) + Complex.log (1 + z)) / 2).re =
      (-Real.log ‖1 - z‖ + Real.log ‖1 + z‖) / 2 := by
    have htwo : (2 : ℂ) = ((2 : ℝ) : ℂ) := by simp
    rw [htwo, Complex.div_ofReal_re, Complex.add_re, Complex.neg_re,
      Complex.log_re, Complex.log_re]
  rw [hreLog]
  have eplus : Real.log ‖1 + z‖ =
      Real.log (1 + 2 * r * Real.cos θ + r ^ 2) / 2 := by
    rw [Complex.norm_def, hnormPlus, Real.log_sqrt (le_of_lt hplusPos)]
  have eminus : Real.log ‖1 - z‖ =
      Real.log (1 - 2 * r * Real.cos θ + r ^ 2) / 2 := by
    rw [Complex.norm_def, hnormMinus, Real.log_sqrt (le_of_lt hminusPos)]
  rw [eplus, eminus,
    Real.log_div (ne_of_gt hplusPos) (ne_of_gt hminusPos)]
  ring

private lemma ads_Sr_norm_le (r x : ℝ) (hr0 : 0 ≤ r) (hr1 : r ≤ 1) (k : ℕ) :
    ‖r ^ (2 * k + 1) * Real.sin (2 * ((2 * k + 1 : ℕ) : ℝ) * x) /
        (((2 * k + 1 : ℕ) : ℝ) ^ 2)‖ ≤
      (1 : ℝ) / (((2 * k + 1 : ℕ) : ℝ) ^ 2) := by
  have hden : (0 : ℝ) < (((2 * k + 1 : ℕ) : ℝ) ^ 2) := by positivity
  rw [norm_div, Real.norm_eq_abs, Real.norm_eq_abs, abs_of_pos hden]
  have hrabs : |r| ≤ 1 := by simpa [abs_of_nonneg hr0] using hr1
  have hrpow : |r| ^ (2 * k + 1) ≤ 1 := pow_le_one₀ (abs_nonneg r) hrabs
  have hsin := Real.abs_sin_le_one (2 * ((2 * k + 1 : ℕ) : ℝ) * x)
  have hnum : |r ^ (2 * k + 1) *
      Real.sin (2 * ((2 * k + 1 : ℕ) : ℝ) * x)| ≤ 1 := by
    rw [abs_mul, abs_pow]
    calc
      |r| ^ (2 * k + 1) * |Real.sin (2 * ((2 * k + 1 : ℕ) : ℝ) * x)| ≤
          1 * 1 := mul_le_mul hrpow hsin (abs_nonneg _) zero_le_one
      _ = 1 := one_mul 1
  exact div_le_div_of_nonneg_right hnum (le_of_lt hden)

private lemma ads_Sr_summable (r x : ℝ) (hr0 : 0 ≤ r) (hr1 : r ≤ 1) :
    Summable (fun k : ℕ => r ^ (2 * k + 1) *
      Real.sin (2 * ((2 * k + 1 : ℕ) : ℝ) * x) /
        (((2 * k + 1 : ℕ) : ℝ) ^ 2)) := by
  apply Summable.of_norm
  exact Summable.of_nonneg_of_le (fun k => norm_nonneg _)
    (fun k => ads_Sr_norm_le r x hr0 hr1 k) ads_base_summable

private lemma ads_Sr_continuous (r : ℝ) (hr0 : 0 ≤ r) (hr1 : r ≤ 1) :
    Continuous (adsSr r) := by
  apply continuous_tsum (fun n => ?_) ads_base_summable
    (fun n x => ads_Sr_norm_le r x hr0 hr1 n)
  have hlin : Continuous (fun x : ℝ => 2 * ((2 * n + 1 : ℕ) : ℝ) * x) := by
    fun_prop
  apply Continuous.div_const
  exact continuous_const.mul (Real.continuous_sin.comp hlin)

private lemma ads_Dr_norm_le (r z : ℝ) (hr0 : 0 ≤ r) (hr1 : r < 1) (n : ℕ) :
    ‖r ^ (2 * n + 1) * 2 * Real.cos (2 * ((2 * n + 1 : ℕ) : ℝ) * z) /
        ((2 * n + 1 : ℕ) : ℝ)‖ ≤ 2 * (r ^ 2) ^ n := by
  have hden : (1 : ℝ) ≤ ((2 * n + 1 : ℕ) : ℝ) := by
    exact_mod_cast (show 1 ≤ 2 * n + 1 by omega)
  have hden_pos : (0 : ℝ) < ((2 * n + 1 : ℕ) : ℝ) := by linarith
  have hrpow : r ^ (2 * n + 1) ≤ (r ^ 2) ^ n := by
    have hexp : r ^ (2 * n + 1) = r * (r ^ 2) ^ n := by
      rw [pow_succ', pow_mul]
    rw [hexp]
    calc
      r * (r ^ 2) ^ n ≤ 1 * (r ^ 2) ^ n :=
        mul_le_mul_of_nonneg_right (le_of_lt hr1) (by positivity)
      _ = (r ^ 2) ^ n := one_mul _
  have hcos := Real.abs_cos_le_one (2 * ((2 * n + 1 : ℕ) : ℝ) * z)
  have hnum : |r ^ (2 * n + 1) * 2 *
      Real.cos (2 * ((2 * n + 1 : ℕ) : ℝ) * z)| ≤ 2 * (r ^ 2) ^ n := by
    rw [abs_mul, abs_mul, abs_of_nonneg (pow_nonneg hr0 _),
      abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2)]
    calc
      r ^ (2 * n + 1) * 2 * |Real.cos (2 * ((2 * n + 1 : ℕ) : ℝ) * z)| ≤
          (r ^ 2) ^ n * 2 * 1 := by
        apply mul_le_mul _ hcos (abs_nonneg _) (by positivity)
        exact mul_le_mul_of_nonneg_right hrpow (by norm_num)
      _ = 2 * (r ^ 2) ^ n := by ring
  rw [norm_div, Real.norm_eq_abs, Real.norm_eq_abs, abs_of_pos hden_pos]
  calc
    |r ^ (2 * n + 1) * 2 * Real.cos (2 * ((2 * n + 1 : ℕ) : ℝ) * z)| /
        ((2 * n + 1 : ℕ) : ℝ) ≤
        (2 * (r ^ 2) ^ n) / ((2 * n + 1 : ℕ) : ℝ) :=
      div_le_div_of_nonneg_right hnum (le_of_lt hden_pos)
    _ ≤ 2 * (r ^ 2) ^ n := div_le_self (by positivity) hden

private lemma ads_Sr_term_hasDerivAt (r x : ℝ) (k : ℕ) :
    HasDerivAt
      (fun y : ℝ => r ^ (2 * k + 1) *
        Real.sin (2 * ((2 * k + 1 : ℕ) : ℝ) * y) /
          (((2 * k + 1 : ℕ) : ℝ) ^ 2))
      (r ^ (2 * k + 1) * 2 * Real.cos (2 * ((2 * k + 1 : ℕ) : ℝ) * x) /
        ((2 * k + 1 : ℕ) : ℝ)) x := by
  have hlin : HasDerivAt (fun y : ℝ => 2 * ((2 * k + 1 : ℕ) : ℝ) * y)
      (2 * ((2 * k + 1 : ℕ) : ℝ)) x := by
    simpa using (hasDerivAt_id' x).const_mul (2 * ((2 * k + 1 : ℕ) : ℝ))
  have hsin := (Real.hasDerivAt_sin
    (2 * ((2 * k + 1 : ℕ) : ℝ) * x)).comp x hlin
  have hdiv := (hsin.const_mul (r ^ (2 * k + 1))).div_const
    (((2 * k + 1 : ℕ) : ℝ) ^ 2)
  have hden : ((2 * k + 1 : ℕ) : ℝ) ≠ 0 := ne_of_gt (by positivity)
  have hsimp : r ^ (2 * k + 1) *
        (Real.cos (2 * ((2 * k + 1 : ℕ) : ℝ) * x) *
          (2 * ((2 * k + 1 : ℕ) : ℝ))) /
        (((2 * k + 1 : ℕ) : ℝ) ^ 2) =
      r ^ (2 * k + 1) * 2 * Real.cos (2 * ((2 * k + 1 : ℕ) : ℝ) * x) /
        ((2 * k + 1 : ℕ) : ℝ) := by
    field_simp
  rwa [hsimp] at hdiv

private lemma ads_Sr_hasDerivAt (r x : ℝ) (hr0 : 0 ≤ r) (hr1 : r < 1) :
    HasDerivAt (adsSr r) (adsDr r x) x := by
  have hr2 : r ^ 2 < 1 := pow_lt_one₀ hr0 hr1 (by norm_num)
  have hmajorant : Summable (fun n : ℕ => 2 * (r ^ 2) ^ n) :=
    (summable_geometric_of_lt_one (sq_nonneg r) hr2).mul_left 2
  have hderiv : ∀ n : ℕ, ∀ z ∈ (Set.univ : Set ℝ),
      HasDerivAt
        (fun y : ℝ => r ^ (2 * n + 1) *
          Real.sin (2 * ((2 * n + 1 : ℕ) : ℝ) * y) /
            (((2 * n + 1 : ℕ) : ℝ) ^ 2))
        (r ^ (2 * n + 1) * 2 * Real.cos (2 * ((2 * n + 1 : ℕ) : ℝ) * z) /
          ((2 * n + 1 : ℕ) : ℝ)) z :=
    fun n z _ => ads_Sr_term_hasDerivAt r z n
  have hbound : ∀ n : ℕ, ∀ z ∈ (Set.univ : Set ℝ),
      ‖r ^ (2 * n + 1) * 2 * Real.cos (2 * ((2 * n + 1 : ℕ) : ℝ) * z) /
          ((2 * n + 1 : ℕ) : ℝ)‖ ≤ 2 * (r ^ 2) ^ n :=
    fun n z _ => ads_Dr_norm_le r z hr0 hr1 n
  have hsum0 : Summable (fun n : ℕ => r ^ (2 * n + 1) *
      Real.sin (2 * ((2 * n + 1 : ℕ) : ℝ) * 0) /
        (((2 * n + 1 : ℕ) : ℝ) ^ 2)) := by
    simp
  have h := hasDerivAt_tsum_of_isPreconnected hmajorant isOpen_univ
    isPreconnected_univ hderiv hbound (Set.mem_univ 0) hsum0 (Set.mem_univ x)
  unfold adsSr adsDr at ⊢
  exact h

private lemma ads_Dr_continuous (r : ℝ) (hr0 : 0 ≤ r) (hr1 : r < 1) :
    Continuous (adsDr r) := by
  have hr2 : r ^ 2 < 1 := pow_lt_one₀ hr0 hr1 (by norm_num)
  have hmajorant : Summable (fun n : ℕ => 2 * (r ^ 2) ^ n) :=
    (summable_geometric_of_lt_one (sq_nonneg r) hr2).mul_left 2
  apply continuous_tsum (fun n => ?_) hmajorant
    (fun n x => ads_Dr_norm_le r x hr0 hr1 n)
  have hlin : Continuous (fun x : ℝ => 2 * ((2 * n + 1 : ℕ) : ℝ) * x) := by
    fun_prop
  apply Continuous.div_const
  exact continuous_const.mul (Real.continuous_cos.comp hlin)

private lemma ads_Sr_zero (r : ℝ) : adsSr r 0 = 0 := by
  unfold adsSr
  simp

private lemma ads_Sr_eq_integral (r x : ℝ) (hr0 : 0 ≤ r) (hr1 : r < 1)
    (hx0 : 0 ≤ x) :
    adsSr r x = ∫ t in (0 : ℝ)..x, adsDrClosed r t := by
  have hSrC : ContinuousOn (adsSr r) (Set.Icc 0 x) :=
    (ads_Sr_continuous r hr0 (le_of_lt hr1)).continuousOn
  have hFTC : (∫ t in (0 : ℝ)..x, adsDr r t) = adsSr r x - adsSr r 0 :=
    intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le hx0 hSrC
      (fun t _ => ads_Sr_hasDerivAt r t hr0 hr1)
      (((ads_Dr_continuous r hr0 hr1).continuousOn.mono
        (Set.subset_univ _)).intervalIntegrable_of_Icc hx0)
  rw [ads_Sr_zero, sub_zero] at hFTC
  have heq : (∫ t in (0 : ℝ)..x, adsDr r t) =
      ∫ t in (0 : ℝ)..x, adsDrClosed r t := by
    apply intervalIntegral.integral_congr
    intro t _
    exact ads_Dr_eq_closed r t hr0 hr1
  rw [heq] at hFTC
  exact hFTC.symm

private def adsSineTerm (x : ℝ) (k : ℕ) : ℝ :=
  Real.sin (2 * ((2 * k + 1 : ℕ) : ℝ) * x) /
    (((2 * k + 1 : ℕ) : ℝ) ^ 2)

private def adsSineSeries (x : ℝ) : ℝ :=
  ∑' k : ℕ, adsSineTerm x k

private lemma ads_SineSeries_eq_Sr_one (x : ℝ) :
    adsSineSeries x = adsSr 1 x := by
  unfold adsSineSeries adsSineTerm adsSr
  apply tsum_congr
  intro k
  simp

private lemma ads_Rho_nonneg (n : ℕ) : 0 ≤ adsRho n := by
  have hden : (1 : ℝ) ≤ (n : ℝ) + 1 := by
    have hn : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
    linarith
  have hle : 1 / ((n : ℝ) + 1) ≤ 1 := by
    simpa using one_div_le_one_div_of_le zero_lt_one hden
  unfold adsRho
  linarith

private lemma ads_Rho_lt_one (n : ℕ) : adsRho n < 1 := by
  unfold adsRho
  have hpos : (0 : ℝ) < 1 / ((n : ℝ) + 1) := by positivity
  linarith

private lemma ads_Rho_tendsto : Tendsto adsRho atTop (𝓝 1) := by
  have h0 : Tendsto (fun n : ℕ => 1 / ((n : ℝ) + 1)) atTop (𝓝 0) :=
    tendsto_one_div_add_atTop_nhds_zero_nat
  have h1 : Tendsto adsRho atTop (𝓝 (1 - 0)) := tendsto_const_nhds.sub h0
  simpa using h1

private lemma ads_Rho_eventually_ge :
    ∀ᶠ n : ℕ in atTop, (1 / 2 : ℝ) ≤ adsRho n := by
  have h := ads_Rho_tendsto.eventually
    (eventually_gt_nhds (by norm_num : (1 / 2 : ℝ) < 1))
  filter_upwards [h] with n hn
  exact le_of_lt hn

private lemma ads_Sr_continuous_r (x : ℝ) :
    ContinuousOn (fun r : ℝ => adsSr r x) (Set.Icc 0 1) := by
  apply continuousOn_tsum (fun n => ?_) ads_base_summable
    (fun n r hr => ?_)
  · apply ContinuousOn.div_const
    exact (continuous_pow (2 * n + 1)).continuousOn.mul continuousOn_const
  · rw [Set.mem_Icc] at hr
    exact ads_Sr_norm_le r x hr.1 hr.2 n

private lemma ads_Sr_tendsto_SineSeries (x : ℝ) :
    Tendsto (fun n : ℕ => adsSr (adsRho n) x) atTop (𝓝 (adsSineSeries x)) := by
  have hmem : (1 : ℝ) ∈ Set.Icc 0 1 := ⟨by norm_num, by norm_num⟩
  have hev : ∀ᶠ n : ℕ in atTop, adsRho n ∈ Set.Icc 0 1 := by
    filter_upwards with n
    exact ⟨ads_Rho_nonneg n, le_of_lt (ads_Rho_lt_one n)⟩
  have hrho : Tendsto adsRho atTop (𝓝[Set.Icc 0 1] 1) := by
    rw [tendsto_nhdsWithin_iff]
    exact ⟨ads_Rho_tendsto, hev⟩
  have hlim : Tendsto (fun n : ℕ => adsSr (adsRho n) x) atTop
      (𝓝 (adsSr 1 x)) :=
    Tendsto.comp (ads_Sr_continuous_r x 1 hmem) hrho
  rwa [← ads_SineSeries_eq_Sr_one x] at hlim

private lemma ads_DrClosed_tendsto (t : ℝ)
    (ht : t ∈ Set.Ioc 0 (Real.pi / 4)) :
    Tendsto (fun n : ℕ => adsDrClosed (adsRho n) t) atTop
      (𝓝 (-Real.log (Real.tan t))) := by
  rw [Set.mem_Ioc] at ht
  have hsin : 0 < Real.sin t :=
    Real.sin_pos_of_pos_of_lt_pi ht.1 (by linarith [ht.2, Real.pi_pos])
  have hcos : 0 < Real.cos t :=
    Real.cos_pos_of_mem_Ioo
      ⟨by linarith [ht.1, Real.pi_pos], by linarith [ht.2, Real.pi_pos]⟩
  have htan : 0 < Real.tan t := by
    rw [Real.tan_eq_sin_div_cos]
    exact div_pos hsin hcos
  have hnum : (1 : ℝ) + 2 * 1 * Real.cos (2 * t) + 1 ^ 2 =
      4 * Real.cos t ^ 2 := by
    rw [Real.cos_two_mul]
    ring
  have hden : (1 : ℝ) - 2 * 1 * Real.cos (2 * t) + 1 ^ 2 =
      4 * Real.sin t ^ 2 := by
    rw [Real.cos_two_mul_eq_one_sub]
    ring
  have hval : adsDrClosed 1 t = -Real.log (Real.tan t) := by
    unfold adsDrClosed
    rw [hnum, hden]
    have hc0 : (0 : ℝ) < Real.cos t ^ 2 := pow_pos hcos 2
    have hs0 : (0 : ℝ) < Real.sin t ^ 2 := pow_pos hsin 2
    rw [Real.log_div (ne_of_gt (mul_pos (by norm_num) hc0))
        (ne_of_gt (mul_pos (by norm_num) hs0)),
      Real.log_mul (by norm_num) (ne_of_gt hc0),
      Real.log_mul (by norm_num) (ne_of_gt hs0),
      Real.log_pow, Real.log_pow]
    have htan_log : Real.log (Real.tan t) =
        Real.log (Real.sin t) - Real.log (Real.cos t) := by
      rw [Real.tan_eq_sin_div_cos,
        Real.log_div (ne_of_gt hsin) (ne_of_gt hcos)]
    rw [htan_log]
    ring
  have hcont : ContinuousAt (fun r : ℝ => adsDrClosed r t) 1 := by
    unfold adsDrClosed
    have hN : ContinuousAt
        (fun r : ℝ => 1 + 2 * r * Real.cos (2 * t) + r ^ 2) 1 := by
      fun_prop
    have hM : ContinuousAt
        (fun r : ℝ => 1 - 2 * r * Real.cos (2 * t) + r ^ 2) 1 := by
      fun_prop
    have hMpos : (0 : ℝ) < 1 - 2 * 1 * Real.cos (2 * t) + 1 ^ 2 := by
      rw [hden]
      positivity
    have hdiv : ContinuousAt
        (fun r : ℝ => (1 + 2 * r * Real.cos (2 * t) + r ^ 2) /
          (1 - 2 * r * Real.cos (2 * t) + r ^ 2)) 1 :=
      hN.div hM (ne_of_gt hMpos)
    have hNpos : (0 : ℝ) < 1 + 2 * 1 * Real.cos (2 * t) + 1 ^ 2 := by
      rw [hnum]
      positivity
    have hratio : (1 + 2 * 1 * Real.cos (2 * t) + 1 ^ 2) /
        (1 - 2 * 1 * Real.cos (2 * t) + 1 ^ 2) ≠ 0 :=
      div_ne_zero (ne_of_gt hNpos) (ne_of_gt hMpos)
    have hlog : Tendsto
        (fun r : ℝ => Real.log ((1 + 2 * r * Real.cos (2 * t) + r ^ 2) /
          (1 - 2 * r * Real.cos (2 * t) + r ^ 2)))
        (𝓝 1)
        (𝓝 (Real.log ((1 + 2 * 1 * Real.cos (2 * t) + 1 ^ 2) /
          (1 - 2 * 1 * Real.cos (2 * t) + 1 ^ 2)))) :=
      (Real.continuousAt_log hratio).tendsto.comp hdiv.tendsto
    exact hlog.div_const 2
  have hcomp := hcont.tendsto.comp ads_Rho_tendsto
  rwa [hval] at hcomp

private lemma ads_DrClosed_bound (r t : ℝ) (hr0 : (1 / 2 : ℝ) ≤ r)
    (hr1 : r ≤ 1) (ht : t ∈ Set.Ioc 0 (Real.pi / 4)) :
    ‖adsDrClosed r t‖ ≤ Real.log 2 - Real.log (Real.sin t) := by
  rw [Set.mem_Ioc] at ht
  have hsin : 0 < Real.sin t :=
    Real.sin_pos_of_pos_of_lt_pi ht.1 (by linarith [ht.2, Real.pi_pos])
  have hsin1 : Real.sin t ≤ 1 := Real.sin_le_one t
  have hcos2 : Real.cos (2 * t) ≤ 1 := Real.cos_le_one _
  have hcos2nn : 0 ≤ Real.cos (2 * t) := by
    exact Real.cos_nonneg_of_mem_Icc
      ⟨by linarith [ht.1, Real.pi_pos], by linarith [ht.2, Real.pi_pos]⟩
  unfold adsDrClosed
  set C : ℝ := Real.cos (2 * t) with hCdef
  set N : ℝ := 1 + 2 * r * C + r ^ 2 with hNdef
  set M : ℝ := 1 - 2 * r * C + r ^ 2 with hMdef
  have hr0' : (0 : ℝ) ≤ r := by linarith
  have hr2 : r ^ 2 ≤ 1 := pow_le_one₀ hr0' hr1
  have h2rC : (0 : ℝ) ≤ 2 * r * C := by positivity
  have hNlo : (1 : ℝ) ≤ N := by
    rw [hNdef]
    nlinarith [sq_nonneg r, h2rC]
  have hNhi : N ≤ 4 := by
    rw [hNdef]
    have h1 : 2 * r * C ≤ 2 := by
      have e1 : 2 * r ≤ 2 * 1 := mul_le_mul_of_nonneg_left hr1 (by norm_num)
      have e2 : (2 * r) * C ≤ (2 * 1) * C :=
        mul_le_mul_of_nonneg_right e1 hcos2nn
      have e3 : (2 * 1) * C ≤ (2 * 1) * 1 :=
        mul_le_mul_of_nonneg_left hcos2 (by norm_num)
      calc
        (2 * r) * C ≤ (2 * 1) * C := e2
        _ ≤ (2 * 1) * 1 := e3
        _ = 2 := by norm_num
    linarith
  have hC2 : C = 1 - 2 * Real.sin t ^ 2 := by
    rw [hCdef, Real.cos_two_mul_eq_one_sub]
  have hMlo : 2 * Real.sin t ^ 2 ≤ M := by
    have hsq : (0 : ℝ) ≤ (1 - r) ^ 2 := sq_nonneg _
    have h2r : (0 : ℝ) ≤ (2 * r - 1) * (2 * Real.sin t ^ 2) :=
      mul_nonneg (by linarith) (by positivity)
    have hexpand : M - 2 * Real.sin t ^ 2 =
        (1 - r) ^ 2 + (2 * r - 1) * (2 * Real.sin t ^ 2) := by
      rw [hMdef, hC2]
      ring
    linarith
  have hMpos : (0 : ℝ) < M := by
    have h2s : (0 : ℝ) < 2 * Real.sin t ^ 2 := by positivity
    linarith
  have hMhi : M ≤ 2 := by
    rw [hMdef]
    linarith
  have hNpos : (0 : ℝ) < N := by linarith
  have hM2sin : (0 : ℝ) < 2 * Real.sin t ^ 2 := by positivity
  have hratio_le : N / M ≤ 2 / Real.sin t ^ 2 := by
    have h1 : N / M ≤ 4 / M :=
      div_le_div_of_nonneg_right hNhi (le_of_lt hMpos)
    have h2 : (4 : ℝ) / M ≤ 4 / (2 * Real.sin t ^ 2) := by
      rw [div_le_div_iff_of_pos_left (by norm_num) hMpos hM2sin]
      exact hMlo
    have h3 : (4 : ℝ) / (2 * Real.sin t ^ 2) = 2 / Real.sin t ^ 2 := by
      field_simp [ne_of_gt (pow_pos hsin 2), ne_of_gt hM2sin]
      ring
    rw [h3] at h2
    exact h1.trans h2
  have hratio_ge : (1 / 2 : ℝ) ≤ N / M := by
    have h1 : (1 : ℝ) / M ≤ N / M :=
      div_le_div_of_nonneg_right hNlo (le_of_lt hMpos)
    exact (one_div_le_one_div_of_le hMpos hMhi).trans h1
  have hlog2pos : (0 : ℝ) < Real.log 2 := Real.log_pos (by norm_num)
  have hlogsin_nn : Real.log (Real.sin t) ≤ 0 :=
    Real.log_nonpos (le_of_lt hsin) hsin1
  have hupper : Real.log (N / M) / 2 ≤
      Real.log 2 - Real.log (Real.sin t) := by
    have hlog : Real.log (N / M) ≤ Real.log (2 / Real.sin t ^ 2) :=
      Real.log_le_log (div_pos hNpos hMpos) hratio_le
    have hexpand : Real.log (2 / Real.sin t ^ 2) =
        Real.log 2 - 2 * Real.log (Real.sin t) := by
      rw [Real.log_div (by norm_num) (ne_of_gt (pow_pos hsin 2)), Real.log_pow]
      ring
    rw [hexpand] at hlog
    linarith
  have hlower : -(Real.log 2 - Real.log (Real.sin t)) ≤
      Real.log (N / M) / 2 := by
    have hlog : Real.log (1 / 2) ≤ Real.log (N / M) :=
      Real.log_le_log (by norm_num) hratio_ge
    have hexpand : Real.log (1 / 2 : ℝ) = -Real.log 2 := by
      rw [Real.log_div (by norm_num) (by norm_num), Real.log_one, zero_sub]
    rw [hexpand] at hlog
    linarith
  rw [Real.norm_eq_abs]
  exact abs_le.mpr ⟨hlower, hupper⟩

private lemma ads_DrClosed_continuous (r : ℝ) (hr0 : 0 ≤ r) (hr1 : r < 1) :
    Continuous (fun t : ℝ => adsDrClosed r t) := by
  have h : (fun t : ℝ => adsDrClosed r t) = adsDr r := by
    funext t
    exact (ads_Dr_eq_closed r t hr0 hr1).symm
  rw [h]
  exact ads_Dr_continuous r hr0 hr1

private lemma ads_logSin_bound_intervalIntegrable (a b : ℝ) :
    IntervalIntegrable (fun t : ℝ => Real.log 2 - Real.log (Real.sin t))
      volume a b := by
  have hsin : IntervalIntegrable (Real.log ∘ Real.sin) volume a b :=
    intervalIntegrable_log_sin
  have hconst : IntervalIntegrable (fun _ : ℝ => Real.log 2) volume a b :=
    intervalIntegrable_const
  simpa [Pi.sub_apply, Function.comp_apply] using hconst.sub hsin

private lemma ads_SineSeries_eq_integral {x : ℝ}
    (hx : x ∈ Set.Icc 0 (Real.pi / 4)) :
    adsSineSeries x = ∫ t in (0 : ℝ)..x, -Real.log (Real.tan t) := by
  rw [Set.mem_Icc] at hx
  have hSr_lim := ads_Sr_tendsto_SineSeries x
  have hSeqEq : (fun n : ℕ => adsSr (adsRho n) x) =
      (fun n : ℕ => ∫ t in (0 : ℝ)..x, adsDrClosed (adsRho n) t) := by
    funext n
    exact ads_Sr_eq_integral (adsRho n) x (ads_Rho_nonneg n)
      (ads_Rho_lt_one n) hx.1
  rw [hSeqEq] at hSr_lim
  have hF_meas : ∀ᶠ n : ℕ in atTop, AEStronglyMeasurable
      (fun t : ℝ => adsDrClosed (adsRho n) t)
        (volume.restrict (Set.uIoc 0 x)) := by
    filter_upwards with n
    exact (ads_DrClosed_continuous (adsRho n) (ads_Rho_nonneg n)
      (ads_Rho_lt_one n)).aestronglyMeasurable
  have hbound : ∀ᶠ n : ℕ in atTop, ∀ᵐ t ∂volume, t ∈ Set.uIoc 0 x →
      ‖adsDrClosed (adsRho n) t‖ ≤
        Real.log 2 - Real.log (Real.sin t) := by
    filter_upwards [ads_Rho_eventually_ge] with n hn
    filter_upwards with t
    intro ht
    have htIoc : t ∈ Set.Ioc 0 (Real.pi / 4) := by
      rw [Set.uIoc_of_le hx.1, Set.mem_Ioc] at ht
      exact ⟨ht.1, ht.2.trans hx.2⟩
    exact ads_DrClosed_bound (adsRho n) t hn (le_of_lt (ads_Rho_lt_one n)) htIoc
  have hint := ads_logSin_bound_intervalIntegrable 0 x
  have hlim : ∀ᵐ t ∂volume, t ∈ Set.uIoc 0 x →
      Tendsto (fun n : ℕ => adsDrClosed (adsRho n) t) atTop
        (𝓝 (-Real.log (Real.tan t))) := by
    filter_upwards with t
    intro ht
    have htIoc : t ∈ Set.Ioc 0 (Real.pi / 4) := by
      rw [Set.uIoc_of_le hx.1, Set.mem_Ioc] at ht
      exact ⟨ht.1, ht.2.trans hx.2⟩
    exact ads_DrClosed_tendsto t htIoc
  have hDCT := intervalIntegral.tendsto_integral_filter_of_dominated_convergence
    (bound := fun t : ℝ => Real.log 2 - Real.log (Real.sin t))
    hF_meas hbound hint hlim
  exact tendsto_nhds_unique hSr_lim hDCT

private lemma ads_logTanIntegral_eq_neg_sineSeries {x : ℝ}
    (hx : x ∈ Set.Icc 0 (Real.pi / 4)) :
    adsLogTanIntegral x = -adsSineSeries x := by
  have h := ads_SineSeries_eq_integral hx
  rw [intervalIntegral.integral_neg] at h
  unfold adsLogTanIntegral
  linarith

private lemma ads_sin_odd_pi_div_two (k : ℕ) :
    Real.sin (((4 * k + 2 : ℕ) : ℝ) * (Real.pi / 4)) = (-1 : ℝ) ^ k := by
  have hcast : ((4 * k + 2 : ℕ) : ℝ) = 4 * (k : ℝ) + 2 := by
    push_cast
    ring
  have harg : (4 * (k : ℝ) + 2) * (Real.pi / 4) =
      Real.pi / 2 + (k : ℝ) * Real.pi := by ring
  rw [hcast, harg, Real.sin_add_nat_mul_pi, Real.sin_pi_div_two, mul_one]

private lemma ads_SineSeries_pi_div_four :
    adsSineSeries (Real.pi / 4) =
      ∑' n : ℕ, (-1 : ℝ) ^ n / (2 * (n : ℝ) + 1) ^ 2 := by
  unfold adsSineSeries adsSineTerm
  apply tsum_congr
  intro n
  have harg : 2 * ((2 * n + 1 : ℕ) : ℝ) * (Real.pi / 4) =
      ((4 * n + 2 : ℕ) : ℝ) * (Real.pi / 4) := by
    push_cast
    ring
  rw [harg, ads_sin_odd_pi_div_two]
  norm_num

private lemma ads_logTanIntegral_pi_div_four :
    adsLogTanIntegral (Real.pi / 4) =
      -(∑' n : ℕ, (-1 : ℝ) ^ n / (2 * (n : ℝ) + 1) ^ 2) := by
  rw [ads_logTanIntegral_eq_neg_sineSeries
    (show Real.pi / 4 ∈ Set.Icc (0 : ℝ) (Real.pi / 4) by
      exact ⟨by positivity, le_rfl⟩),
    ads_SineSeries_pi_div_four]

private def adsResidueSum (j : ℕ) : ℝ :=
  ∑' n : ℕ, (1 : ℝ) / (((8 * n + j : ℕ) : ℝ) ^ 2)

private lemma ads_residue_summable (j : ℕ) :
    Summable (fun n : ℕ => (1 : ℝ) / (((8 * n + j : ℕ) : ℝ) ^ 2)) := by
  have h := (Real.summable_one_div_nat_pow (p := 2)).mpr (by norm_num)
  have hinj : Function.Injective (fun n : ℕ => 8 * n + j) := by
    intro a b hab
    exact Nat.mul_left_cancel (by norm_num) (Nat.add_right_cancel hab)
  simpa [Function.comp_def] using h.comp_injective hinj

private lemma ads_sin_residue_one (n : ℕ) :
    Real.sin (((8 * n + 1 : ℕ) : ℝ) * (Real.pi / 4)) = Real.sqrt 2 / 2 := by
  have harg : ((8 * n + 1 : ℕ) : ℝ) * (Real.pi / 4) =
      Real.pi / 4 + (n : ℝ) * (2 * Real.pi) := by
    push_cast
    ring
  rw [harg, Real.sin_add_nat_mul_two_pi, Real.sin_pi_div_four]

private lemma ads_sin_residue_three (n : ℕ) :
    Real.sin (((8 * n + 3 : ℕ) : ℝ) * (Real.pi / 4)) = Real.sqrt 2 / 2 := by
  have harg : ((8 * n + 3 : ℕ) : ℝ) * (Real.pi / 4) =
      3 * Real.pi / 4 + (n : ℝ) * (2 * Real.pi) := by
    push_cast
    ring
  rw [harg, Real.sin_add_nat_mul_two_pi,
    show 3 * Real.pi / 4 = Real.pi - Real.pi / 4 by ring,
    Real.sin_pi_sub, Real.sin_pi_div_four]

private lemma ads_sin_residue_five (n : ℕ) :
    Real.sin (((8 * n + 5 : ℕ) : ℝ) * (Real.pi / 4)) = -(Real.sqrt 2 / 2) := by
  have harg : ((8 * n + 5 : ℕ) : ℝ) * (Real.pi / 4) =
      5 * Real.pi / 4 + (n : ℝ) * (2 * Real.pi) := by
    push_cast
    ring
  rw [harg, Real.sin_add_nat_mul_two_pi,
    show 5 * Real.pi / 4 = Real.pi / 4 + Real.pi by ring,
    Real.sin_add_pi, Real.sin_pi_div_four]

private lemma ads_sin_residue_seven (n : ℕ) :
    Real.sin (((8 * n + 7 : ℕ) : ℝ) * (Real.pi / 4)) = -(Real.sqrt 2 / 2) := by
  have harg : ((8 * n + 7 : ℕ) : ℝ) * (Real.pi / 4) =
      7 * Real.pi / 4 + (n : ℝ) * (2 * Real.pi) := by
    push_cast
    ring
  rw [harg, Real.sin_add_nat_mul_two_pi,
    show 7 * Real.pi / 4 = 3 * Real.pi / 4 + Real.pi by ring,
    Real.sin_add_pi,
    show 3 * Real.pi / 4 = Real.pi - Real.pi / 4 by ring,
    Real.sin_pi_sub, Real.sin_pi_div_four]

private lemma ads_SineTerm_summable (x : ℝ) : Summable (adsSineTerm x) := by
  unfold adsSineTerm
  simpa only [one_pow, one_mul] using
    ads_Sr_summable (1 : ℝ) x (by norm_num) (by norm_num)

private lemma ads_tsum_mod_four {f : ℕ → ℝ} (hf : Summable f) :
    (∑' n : ℕ, f n) =
      ((∑' n : ℕ, f (4 * n)) + ∑' n : ℕ, f (4 * n + 2)) +
        ((∑' n : ℕ, f (4 * n + 1)) + ∑' n : ℕ, f (4 * n + 3)) := by
  rw [Nat.sumByResidueClasses hf 4]
  rw [← (ZMod.finEquiv 4).toEquiv.sum_comp, Fin.sum_univ_four]
  change ((∑' m : ℕ, f (0 + 4 * m)) + (∑' m : ℕ, f (1 + 4 * m)) +
    (∑' m : ℕ, f (2 + 4 * m)) + ∑' m : ℕ, f (3 + 4 * m)) = _
  ring_nf

private lemma ads_SineTerm_pi_div_eight_residue_one (n : ℕ) :
    adsSineTerm (Real.pi / 8) (4 * n) = Real.sqrt 2 / 2 *
      ((1 : ℝ) / (((8 * n + 1 : ℕ) : ℝ) ^ 2)) := by
  unfold adsSineTerm
  have hk : 2 * (4 * n) + 1 = 8 * n + 1 := by omega
  rw [hk]
  have harg : 2 * ((8 * n + 1 : ℕ) : ℝ) * (Real.pi / 8) =
      ((8 * n + 1 : ℕ) : ℝ) * (Real.pi / 4) := by ring
  rw [harg, ads_sin_residue_one]
  ring

private lemma ads_SineTerm_pi_div_eight_residue_three (n : ℕ) :
    adsSineTerm (Real.pi / 8) (4 * n + 1) = Real.sqrt 2 / 2 *
      ((1 : ℝ) / (((8 * n + 3 : ℕ) : ℝ) ^ 2)) := by
  unfold adsSineTerm
  have hk : 2 * (4 * n + 1) + 1 = 8 * n + 3 := by omega
  rw [hk]
  have harg : 2 * ((8 * n + 3 : ℕ) : ℝ) * (Real.pi / 8) =
      ((8 * n + 3 : ℕ) : ℝ) * (Real.pi / 4) := by ring
  rw [harg, ads_sin_residue_three]
  ring

private lemma ads_SineTerm_pi_div_eight_residue_five (n : ℕ) :
    adsSineTerm (Real.pi / 8) (4 * n + 2) = -(Real.sqrt 2 / 2) *
      ((1 : ℝ) / (((8 * n + 5 : ℕ) : ℝ) ^ 2)) := by
  unfold adsSineTerm
  have hk : 2 * (4 * n + 2) + 1 = 8 * n + 5 := by omega
  rw [hk]
  have harg : 2 * ((8 * n + 5 : ℕ) : ℝ) * (Real.pi / 8) =
      ((8 * n + 5 : ℕ) : ℝ) * (Real.pi / 4) := by ring
  rw [harg, ads_sin_residue_five]
  ring

private lemma ads_SineTerm_pi_div_eight_residue_seven (n : ℕ) :
    adsSineTerm (Real.pi / 8) (4 * n + 3) = -(Real.sqrt 2 / 2) *
      ((1 : ℝ) / (((8 * n + 7 : ℕ) : ℝ) ^ 2)) := by
  unfold adsSineTerm
  have hk : 2 * (4 * n + 3) + 1 = 8 * n + 7 := by omega
  rw [hk]
  have harg : 2 * ((8 * n + 7 : ℕ) : ℝ) * (Real.pi / 8) =
      ((8 * n + 7 : ℕ) : ℝ) * (Real.pi / 4) := by ring
  rw [harg, ads_sin_residue_seven]
  ring

private lemma ads_tsum_SineTerm_pi_div_eight_residue_one :
    (∑' n : ℕ, adsSineTerm (Real.pi / 8) (4 * n)) =
      Real.sqrt 2 / 2 * adsResidueSum 1 := by
  unfold adsResidueSum
  simp_rw [ads_SineTerm_pi_div_eight_residue_one, tsum_mul_left]

private lemma ads_tsum_SineTerm_pi_div_eight_residue_three :
    (∑' n : ℕ, adsSineTerm (Real.pi / 8) (4 * n + 1)) =
      Real.sqrt 2 / 2 * adsResidueSum 3 := by
  unfold adsResidueSum
  simp_rw [ads_SineTerm_pi_div_eight_residue_three, tsum_mul_left]

private lemma ads_tsum_SineTerm_pi_div_eight_residue_five :
    (∑' n : ℕ, adsSineTerm (Real.pi / 8) (4 * n + 2)) =
      -(Real.sqrt 2 / 2) * adsResidueSum 5 := by
  unfold adsResidueSum
  simp_rw [ads_SineTerm_pi_div_eight_residue_five, tsum_mul_left]

private lemma ads_tsum_SineTerm_pi_div_eight_residue_seven :
    (∑' n : ℕ, adsSineTerm (Real.pi / 8) (4 * n + 3)) =
      -(Real.sqrt 2 / 2) * adsResidueSum 7 := by
  unfold adsResidueSum
  simp_rw [ads_SineTerm_pi_div_eight_residue_seven, tsum_mul_left]

private lemma ads_SineSeries_pi_div_eight :
    adsSineSeries (Real.pi / 8) = Real.sqrt 2 / 2 *
      (adsResidueSum 1 + adsResidueSum 3 - adsResidueSum 5 - adsResidueSum 7) := by
  rw [adsSineSeries, ads_tsum_mod_four (ads_SineTerm_summable (Real.pi / 8)),
    ads_tsum_SineTerm_pi_div_eight_residue_one,
    ads_tsum_SineTerm_pi_div_eight_residue_three,
    ads_tsum_SineTerm_pi_div_eight_residue_five,
    ads_tsum_SineTerm_pi_div_eight_residue_seven]
  ring

private lemma ads_logTanIntegral_pi_div_eight :
    adsLogTanIntegral (Real.pi / 8) = -(Real.sqrt 2 / 2 *
      (adsResidueSum 1 + adsResidueSum 3 - adsResidueSum 5 -
        adsResidueSum 7)) := by
  rw [ads_logTanIntegral_eq_neg_sineSeries
    (show Real.pi / 8 ∈ Set.Icc (0 : ℝ) (Real.pi / 4) by
      constructor <;> linarith [Real.pi_pos]),
    ads_SineSeries_pi_div_eight]

private lemma ads_all_inv_sq_summable :
    Summable (fun n : ℕ => (1 : ℝ) / ((n : ℝ) ^ 2)) :=
  Real.summable_one_div_nat_pow.mpr (by norm_num)

private lemma ads_even_inv_sq_summable :
    Summable (fun n : ℕ => (1 : ℝ) / (((2 * n : ℕ) : ℝ) ^ 2)) := by
  have hinj : Function.Injective (fun n : ℕ => 2 * n) := by
    intro a b hab
    exact Nat.mul_left_cancel (by norm_num) hab
  simpa only [Function.comp_def] using ads_all_inv_sq_summable.comp_injective hinj

private lemma ads_even_inv_sq_tsum :
    (∑' n : ℕ, (1 : ℝ) / (((2 * n : ℕ) : ℝ) ^ 2)) =
      (1 / 4 : ℝ) * ∑' n : ℕ, (1 : ℝ) / ((n : ℝ) ^ 2) := by
  have hterm (n : ℕ) : (1 : ℝ) / (((2 * n : ℕ) : ℝ) ^ 2) =
      (1 / 4 : ℝ) * ((1 : ℝ) / ((n : ℝ) ^ 2)) := by
    by_cases hn : n = 0
    · subst n
      norm_num
    · have hcast : ((2 * n : ℕ) : ℝ) = 2 * (n : ℝ) := by
        push_cast
        ring
      rw [hcast]
      field_simp
      ring
  simp_rw [hterm, tsum_mul_left]

private lemma ads_odd_inv_sq_tsum :
    (∑' n : ℕ, (1 : ℝ) / (((2 * n + 1 : ℕ) : ℝ) ^ 2)) =
      Real.pi ^ 2 / 8 := by
  have hzeta : (∑' n : ℕ, (1 : ℝ) / ((n : ℝ) ^ 2)) = Real.pi ^ 2 / 6 :=
    hasSum_zeta_two.tsum_eq
  have hsplit := tsum_even_add_odd
    (f := fun n : ℕ => (1 : ℝ) / ((n : ℝ) ^ 2))
    ads_even_inv_sq_summable ads_base_summable
  rw [ads_even_inv_sq_tsum, hzeta] at hsplit
  linarith [sq_pos_of_pos Real.pi_pos]

private lemma ads_base_residue_one :
    (∑' n : ℕ, (1 : ℝ) / (((2 * (4 * n) + 1 : ℕ) : ℝ) ^ 2)) =
      adsResidueSum 1 := by
  unfold adsResidueSum
  apply tsum_congr
  intro n
  rw [show 2 * (4 * n) + 1 = 8 * n + 1 by omega]

private lemma ads_base_residue_three :
    (∑' n : ℕ, (1 : ℝ) / (((2 * (4 * n + 1) + 1 : ℕ) : ℝ) ^ 2)) =
      adsResidueSum 3 := by
  unfold adsResidueSum
  apply tsum_congr
  intro n
  rw [show 2 * (4 * n + 1) + 1 = 8 * n + 3 by omega]

private lemma ads_base_residue_five :
    (∑' n : ℕ, (1 : ℝ) / (((2 * (4 * n + 2) + 1 : ℕ) : ℝ) ^ 2)) =
      adsResidueSum 5 := by
  unfold adsResidueSum
  apply tsum_congr
  intro n
  rw [show 2 * (4 * n + 2) + 1 = 8 * n + 5 by omega]

private lemma ads_base_residue_seven :
    (∑' n : ℕ, (1 : ℝ) / (((2 * (4 * n + 3) + 1 : ℕ) : ℝ) ^ 2)) =
      adsResidueSum 7 := by
  unfold adsResidueSum
  apply tsum_congr
  intro n
  rw [show 2 * (4 * n + 3) + 1 = 8 * n + 7 by omega]

private lemma ads_residue_sum_total :
    adsResidueSum 1 + adsResidueSum 3 + adsResidueSum 5 + adsResidueSum 7 =
      Real.pi ^ 2 / 8 := by
  have h := ads_tsum_mod_four ads_base_summable
  rw [ads_odd_inv_sq_tsum, ads_base_residue_one, ads_base_residue_three,
    ads_base_residue_five, ads_base_residue_seven] at h
  linarith

private lemma ads_shifted_tsum_one :
    (∑' n : ℕ, (1 : ℝ) / (((n : ℝ) + (1 / 8 : ℝ)) ^ 2)) =
      64 * adsResidueSum 1 := by
  unfold adsResidueSum
  calc
    (∑' n : ℕ, (1 : ℝ) / (((n : ℝ) + (1 / 8 : ℝ)) ^ 2)) =
        ∑' n : ℕ, 64 * ((1 : ℝ) / (((8 * n + 1 : ℕ) : ℝ) ^ 2)) := by
      apply tsum_congr
      intro n
      push_cast
      have h : 8 * (n : ℝ) + 1 ≠ 0 := by positivity
      field_simp
      ring
    _ = 64 * ∑' n : ℕ, (1 : ℝ) / (((8 * n + 1 : ℕ) : ℝ) ^ 2) :=
      tsum_mul_left

private lemma ads_shifted_tsum_three :
    (∑' n : ℕ, (1 : ℝ) / (((n : ℝ) + (3 / 8 : ℝ)) ^ 2)) =
      64 * adsResidueSum 3 := by
  unfold adsResidueSum
  calc
    (∑' n : ℕ, (1 : ℝ) / (((n : ℝ) + (3 / 8 : ℝ)) ^ 2)) =
        ∑' n : ℕ, 64 * ((1 : ℝ) / (((8 * n + 3 : ℕ) : ℝ) ^ 2)) := by
      apply tsum_congr
      intro n
      push_cast
      have h : 8 * (n : ℝ) + 3 ≠ 0 := by positivity
      field_simp
      ring
    _ = 64 * ∑' n : ℕ, (1 : ℝ) / (((8 * n + 3 : ℕ) : ℝ) ^ 2) :=
      tsum_mul_left

/-- Source: Narendra Bhandari, "Infinite Series Associated with the Ratio and
Product of Central Binomial Coefficients", Journal of Integer Sequences 25
(2022), equation (36), lines 307--309,
<https://cs.uwaterloo.ca/journals/JIS/VOL25/Bhandari/bhan8.tex>.

Catalan's constant `G` and the trigamma values `ψ₁(1/8)`, `ψ₁(3/8)` are
expanded as the defining `tsum`s.

Proves `Wanted` entry `arcsin_div_sin_integral`.

Proof: The route follows Bhandari's reduction to log-tangent integrals, followed by an
Abel-regularized Fourier expansion and residue-class evaluation.
-/
public theorem arcsin_div_sin_integral : ∫ x in (0 : ℝ)..(Real.pi / 2), Real.arcsin
  ((Real.sin x) ^ 2) / Real.sin x = -2 * tsum
  (fun n : ℕ => (-1 : ℝ) ^ n / ((2 * (n : ℝ) + 1) ^ 2)) - Real.pi ^ 2 / (2 * Real.sqrt 2) + 1 /
  (8 * Real.sqrt 2) *
  (tsum (fun n : ℕ => (1 : ℝ) / (((n : ℝ) + (1 / 8 : ℝ)) ^ 2)) + tsum
  (fun n : ℕ => (1 : ℝ) / (((n : ℝ) + (3 / 8 : ℝ)) ^ 2))) := by
  rw [ads_integral_eq_logTan_values, ads_logTanIntegral_pi_div_eight,
    ads_logTanIntegral_pi_div_four, ads_shifted_tsum_one, ads_shifted_tsum_three]
  have hsum := ads_residue_sum_total
  have hdiff : adsResidueSum 1 + adsResidueSum 3 - adsResidueSum 5 -
      adsResidueSum 7 =
        2 * (adsResidueSum 1 + adsResidueSum 3) - Real.pi ^ 2 / 8 := by
    linarith
  rw [hdiff]
  have hsqrt_pos : 0 < Real.sqrt 2 := Real.sqrt_pos.2 (by norm_num)
  have hsqrt_sq : Real.sqrt 2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  field_simp [ne_of_gt hsqrt_pos]
  ring_nf
  rw [hsqrt_sq]
  ring

end

end MetaMathlibExt
