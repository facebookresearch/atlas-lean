/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.Analysis.Calculus.ContDiff.Basic
public import Mathlib.Analysis.Calculus.IteratedDeriv.Defs
public import Mathlib.Analysis.Complex.Exponential
public import Mathlib.Analysis.Real.Sqrt
public import Mathlib.Analysis.SpecialFunctions.Complex.Log
public import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
public import Mathlib.Analysis.SpecialFunctions.Gamma.Digamma
public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Arctan
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
public import Mathlib.Basic.Complex.Basic
public import Mathlib.Data.Finset.Defs
public import Mathlib.Data.Nat.Choose.Basic
public import Mathlib.Data.Nat.Factorial.Basic
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
public import Mathlib.MeasureTheory.Measure.MeasureSpaceDef
public import Mathlib.NumberTheory.Bernoulli
public import Mathlib.NumberTheory.Harmonic.EulerMascheroni
public import Mathlib.NumberTheory.LSeries.RiemannZeta
public import Mathlib.Order.Filter.Basic
public import Mathlib.Order.Interval.Finset.Defs
public import Mathlib.Order.Interval.Set.Defs
public import Mathlib.Topology.Algebra.InfiniteSum.Basic
public import Mathlib.Topology.Algebra.InfiniteSum.SummationFilter
public import Mathlib.Topology.Basic
public import MathlibExt.Analysis.Ramanujan.Part1Ch8Entry9Qgamma
public import MathlibExt.Analysis.SpecialFunctions.Gamma.Digamma
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Analytic.IsolatedZeros
import Mathlib.Analysis.Calculus.SmoothSeries
import Mathlib.Analysis.Complex.CauchyIntegral
import Mathlib.Analysis.Convex.Basic
import Mathlib.Analysis.Convex.PathConnected
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.NumberTheory.ZetaValues
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Topology.Algebra.InfiniteSum.NatInt
import MathlibExt.Analysis.SpecialFunctions.Gamma.Digamma

@[expose] public section

section

/-!
# Ramanujan's Notebooks, Part I, Chapter 8

Statements of entries from B. C. Berndt, *Ramanujan's Notebooks, Part I*
(Springer, 1985), with proofs.
-/

namespace MathlibExt.Analysis.Ramanujan.Part1Ch8

namespace Entry10Qgammalimit

open scoped Nat Real BigOperators Interval Polynomial ContDiff
open Asymptotics Filter Finset Complex Topology MeasureTheory

noncomputable section

def chapter8Entry10Kernel (x : ℂ) (u : ℝ) : ℂ :=
  if u = 0 then 0
  else if u = 1 then -1 / x
  else
    ((1 - u : ℝ) : ℂ) /
      ((u : ℂ) * (Entry9Qgamma.chapter8UnitPow x u - 1))

-- Helper: x ≠ 0 from Re x < 0.
private lemma helper_x_ne (x : ℂ) (hx : x.re < 0) : x ≠ 0 := by
  intro h
  rw [h] at hx
  simp at hx

-- Helper: Gamma (1 - 1 / x) ≠ 0 since Re (1 - 1 / x) > 1.
private lemma helper_Gamma_ne (x : ℂ) (hx : x.re < 0) :
    Complex.Gamma (1 - 1 / x) ≠ 0 := by
  apply Complex.Gamma_ne_zero
  intro m h
  have hx0 : x ≠ 0 := helper_x_ne x hx
  have hns : 0 < Complex.normSq x := Complex.normSq_pos.mpr hx0
  have h1 : (1 / x).re < 0 := by
    rw [one_div, Complex.inv_re]
    exact div_neg_of_neg_of_pos hx hns
  have h2 : (1 - 1 / x).re > 1 := by
    have : (1 - 1 / x).re = 1 - (1 / x).re := by
      simp [Complex.sub_re, Complex.one_re]
    linarith
  have h3 : ((-((m : ℕ) : ℂ))).re ≤ 0 := by
    simp [Complex.natCast_re]
  rw [h] at h2
  linarith

-- Helper: denominator nonzero on (0, 1); |exp w| = exp (Re w) > 1.
private lemma helper_denom_ne (x : ℂ) (hx : x.re < 0) (u : ℝ)
    (hu : u ∈ Set.Ioo 0 1) :
    (u : ℂ) * (Entry9Qgamma.chapter8UnitPow x u - 1) ≠ 0 := by
  obtain ⟨hu0, hu1⟩ := hu
  have hu0' : u ≠ 0 := ne_of_gt hu0
  have hlog : Real.log u < 0 := (Real.log_neg_iff hu0).mpr hu1
  have hure : (u : ℂ) ≠ 0 := by exact_mod_cast hu0'
  have hre : (x * (Real.log u : ℂ)).re > 0 := by
    rw [Complex.mul_re]
    simp only [Complex.ofReal_re, Complex.ofReal_im, mul_zero, sub_zero]
    exact mul_pos_of_neg_of_neg hx hlog
  have hexp : Complex.exp (x * (Real.log u : ℂ)) ≠ 1 := by
    intro hcon
    have hnorm : ‖Complex.exp (x * (Real.log u : ℂ))‖ = ‖(1 : ℂ)‖ := by rw [hcon]
    rw [Complex.norm_exp, norm_one] at hnorm
    have : 1 < Real.exp ((x * (Real.log u : ℂ)).re) := Real.one_lt_exp_iff.mpr hre
    linarith
  have hU : Entry9Qgamma.chapter8UnitPow x u = Complex.exp (x * (Real.log u : ℂ)) := by
    simp [Entry9Qgamma.chapter8UnitPow, hu0']
  apply mul_ne_zero hure
  rw [hU]
  intro hsub
  apply hexp
  exact sub_eq_zero.mp hsub

-- Helper: the kernel formula on (0,1), without the endpoint cases.
private def helper_formula (x : ℂ) (u : ℝ) : ℂ :=
  ((1 - u : ℝ) : ℂ) / ((u : ℂ) * (Entry9Qgamma.chapter8UnitPow x u - 1))

private lemma helper_UnitPow_one (x : ℂ) : Entry9Qgamma.chapter8UnitPow x 1 = 1 := by
  simp [Entry9Qgamma.chapter8UnitPow, Real.log_one, one_ne_zero]

private lemma helper_hasDeriv_UnitPow (x : ℂ) : HasDerivAt (Entry9Qgamma.chapter8UnitPow x) x 1 := by
  have hlog : HasDerivAt Real.log 1 1 := by simpa using Real.hasDerivAt_log one_ne_zero
  have hlogC : HasDerivAt (fun y : ℝ => ((Real.log y : ℝ) : ℂ)) 1 1 := by
    simpa using HasDerivAt.ofReal_comp hlog
  have hmul : HasDerivAt (fun y : ℝ => x * ((Real.log y : ℝ) : ℂ)) (x * 1) 1 :=
    HasDerivAt.const_mul x hlogC
  have hexp : HasDerivAt (fun y : ℝ => Complex.exp (x * ((Real.log y : ℝ) : ℂ)))
      (Complex.exp (x * ((Real.log 1 : ℝ) : ℂ)) * (x * 1)) 1 := hmul.cexp
  rw [Real.log_one] at hexp
  simp only [Complex.ofReal_zero, mul_zero, Complex.exp_zero, one_mul, mul_one] at hexp
  apply hexp.congr_of_eventuallyEq
  filter_upwards [eventually_ne_nhds one_ne_zero] with u hu
  simp [Entry9Qgamma.chapter8UnitPow, hu]

private lemma helper_slope_UnitPow (x : ℂ) :
    Tendsto (slope (Entry9Qgamma.chapter8UnitPow x) 1) (nhdsWithin (1 : ℝ) {1}ᶜ) (nhds x) := by
  have h := (hasDerivAt_iff_tendsto_slope.mp (helper_hasDeriv_UnitPow x))
  simpa using h

private lemma helper_formula_lim (x : ℂ) (hx0 : x ≠ 0) :
    Tendsto (helper_formula x) (nhdsWithin (1 : ℝ) {1}ᶜ) (nhds (-1 / x)) := by
  have hslope := helper_slope_UnitPow x
  have hinv :
      Tendsto (fun u : ℝ => (slope (Entry9Qgamma.chapter8UnitPow x) 1 u)⁻¹)
        (nhdsWithin (1 : ℝ) {1}ᶜ) (nhds x⁻¹) :=
    hslope.inv₀ hx0
  have h1 : Tendsto (fun u : ℝ => (u : ℂ)) (nhdsWithin (1 : ℝ) {1}ᶜ) (nhds ((1 : ℝ) : ℂ)) :=
    ((Complex.continuous_ofReal.tendsto 1).mono_left nhdsWithin_le_nhds)
  have hcoe : Tendsto (fun u : ℝ => (-1 : ℂ) / (u : ℂ)) (nhdsWithin (1 : ℝ) {1}ᶜ) (nhds (-1)) := by
    have hc : Tendsto (fun _ : ℝ => (-1 : ℂ)) (nhdsWithin (1 : ℝ) {1}ᶜ)
        (nhds (-1)) :=
      tendsto_const_nhds
    have hne : ((1 : ℝ) : ℂ) ≠ 0 := by simp
    have h := hc.div h1 hne
    rw [Complex.ofReal_one, div_one] at h
    exact h
  have hmul := hcoe.mul hinv
  have heq : (-1 : ℂ) * x⁻¹ = -1 / x := by rw [div_eq_mul_inv]
  rw [heq] at hmul
  apply hmul.congr'
  have hne0 : ∀ᶠ u : ℝ in nhdsWithin (1 : ℝ) {1}ᶜ, u ≠ 0 :=
    (eventually_ne_nhds (by norm_num : (1 : ℝ) ≠ 0)).filter_mono nhdsWithin_le_nhds
  filter_upwards [self_mem_nhdsWithin,
    hslope.eventually (eventually_ne_nhds hx0), hne0] with u hu hs hu0'
  simp only [Set.mem_compl_iff, Set.mem_singleton_iff] at hu
  have hu0 : (u : ℂ) ≠ 0 := by exact_mod_cast hu0'
  have hE : Entry9Qgamma.chapter8UnitPow x u - 1 ≠ 0 := by
    intro hcon
    apply hs
    simp only [slope, vsub_eq_sub, helper_UnitPow_one]
    rw [hcon]
    simp
  have hsub : (u : ℝ) - 1 ≠ 0 := sub_ne_zero.mpr hu
  have hsubC : ((u : ℝ) : ℂ) - 1 ≠ 0 := by
    have hcc : (((u - 1 : ℝ)) : ℂ) ≠ 0 := by
      rw [ne_eq, Complex.ofReal_eq_zero]
      exact hsub
    simpa [Complex.ofReal_sub, Complex.ofReal_one] using hcc
  simp only [helper_formula, slope, vsub_eq_sub, helper_UnitPow_one,
    Complex.real_smul, Complex.ofReal_inv]
  rw [mul_inv, inv_inv]
  have e1 : ((1 - u : ℝ) : ℂ) = -(((u : ℝ) : ℂ) - 1) := by push_cast; ring
  rw [e1]
  field_simp
  push_cast
  ring

private lemma helper_contOn_UnitPow (x : ℂ) : ContinuousOn (Entry9Qgamma.chapter8UnitPow x) {0}ᶜ := by
  have hlog : ContinuousOn Real.log {0}ᶜ := Real.continuousOn_log
  have hlogC : ContinuousOn (fun y : ℝ => ((Real.log y : ℝ) : ℂ)) {0}ᶜ := by
    have h := Complex.continuous_ofReal.comp_continuousOn hlog
    apply h.congr
    intro u _
    rfl
  have hmul : ContinuousOn (fun y : ℝ => x * ((Real.log y : ℝ) : ℂ)) {0}ᶜ :=
    hlogC.const_mul x
  have hexp : ContinuousOn (fun y : ℝ => Complex.exp (x * ((Real.log y : ℝ) : ℂ))) {0}ᶜ :=
    hmul.cexp
  apply hexp.congr
  intro u hu
  simp only [Set.mem_compl_iff, Set.mem_singleton_iff] at hu
  simp [Entry9Qgamma.chapter8UnitPow, hu]

-- denominator nonzero on (0,1)
private lemma helper_contOn_formula (x : ℂ) (hx : x.re < 0) :
    ContinuousOn (helper_formula x) (Set.Ioo 0 1) := by
  have hsub : Set.Ioo (0 : ℝ) 1 ⊆ {0}ᶜ := by
    intro u hu
    simp only [Set.mem_compl_iff, Set.mem_singleton_iff]
    exact ne_of_gt hu.1
  have hE : ContinuousOn (Entry9Qgamma.chapter8UnitPow x) (Set.Ioo 0 1) := (helper_contOn_UnitPow x).mono hsub
  have hnum : ContinuousOn (fun u : ℝ => ((1 - u : ℝ) : ℂ)) (Set.Ioo 0 1) :=
    (Complex.continuous_ofReal.comp (continuous_const.sub continuous_id')).continuousOn
  have hden : ContinuousOn (fun u : ℝ => (u : ℂ) * (Entry9Qgamma.chapter8UnitPow x u - 1)) (Set.Ioo 0 1) :=
    (Complex.continuous_ofReal.continuousOn).mul (hE.sub continuousOn_const)
  have hne : ∀ u ∈ Set.Ioo (0 : ℝ) 1, (u : ℂ) * (Entry9Qgamma.chapter8UnitPow x u - 1) ≠ 0 :=
    fun u hu => helper_denom_ne x hx u hu
  have h := hnum.div hden hne
  apply h.congr
  intro u _
  rfl

-- kernel is continuous on (0,1)
private lemma helper_contOn_kernel_Ioo (x : ℂ) (hx : x.re < 0) :
    ContinuousOn (chapter8Entry10Kernel x) (Set.Ioo 0 1) := by
  have h := helper_contOn_formula x hx
  apply h.congr
  intro u hu
  obtain ⟨hu0, hu1⟩ := hu
  have h0 : u ≠ 0 := ne_of_gt hu0
  have h1 : u ≠ 1 := ne_of_lt hu1
  simp only [chapter8Entry10Kernel, helper_formula, h0, h1, ite_false]

private lemma helper_kernel_one (x : ℂ) : chapter8Entry10Kernel x 1 = -1 / x := by
  simp [chapter8Entry10Kernel, one_ne_zero]

-- kernel is continuous at 1 (removable singularity, value -1/x)
private lemma helper_contAt_kernel_one (x : ℂ) (hx0 : x ≠ 0) :
    ContinuousAt (chapter8Entry10Kernel x) 1 := by
  have hlim := helper_formula_lim x hx0
  have hval := helper_kernel_one x
  rw [Metric.continuousAt_iff]
  intro ε hε
  have hev : ∀ᶠ u : ℝ in nhdsWithin (1 : ℝ) {1}ᶜ, dist (helper_formula x u) (-1 / x) < ε := by
    have hball : Metric.ball (-1 / x) ε ∈ nhds (-1 / x) := Metric.ball_mem_nhds _ hε
    have h2 := hlim.eventually hball
    filter_upwards [h2] with u hu
    exact Metric.mem_ball.mp hu
  rw [eventually_nhdsWithin_iff, Metric.eventually_nhds_iff_ball] at hev
  obtain ⟨δ, hδ, hball⟩ := hev
  refine ⟨min δ 1, lt_min hδ one_pos, fun y hy => ?_⟩
  have hyδ : y ∈ Metric.ball (1 : ℝ) δ := Metric.mem_ball.mpr (lt_of_lt_of_le hy (min_le_left _ _))
  have hy0 : y ≠ 0 := by
    rintro rfl
    have h10 : dist (0 : ℝ) (1 : ℝ) = 1 := by simp [dist_eq_norm]
    have hy' : dist (0 : ℝ) (1 : ℝ) < min δ 1 := hy
    rw [h10] at hy'
    have hle := min_le_right δ (1 : ℝ)
    linarith
  by_cases hy1 : y = 1
  · subst hy1
    rw [hval]
    simpa using hε
  · have hmem : y ∈ ({1}ᶜ : Set ℝ) := by simpa using hy1
    have h2 := hball y hyδ hmem
    have hKy : chapter8Entry10Kernel x y = helper_formula x y := by
      simp [chapter8Entry10Kernel, helper_formula, hy0, hy1]
    rw [hKy, hval]
    exact h2

-- kernel is integrable on [1/2, 1] (continuous on the compact interval)
private lemma helper_intble_half_one (x : ℂ) (hx : x.re < 0) (hx0 : x ≠ 0) :
    IntervalIntegrable (chapter8Entry10Kernel x) volume (1 / 2) 1 := by
  have h12 : ContinuousOn (chapter8Entry10Kernel x) (Set.uIcc (1 / 2 : ℝ) 1) := by
    rw [Set.uIcc_of_le (by norm_num : (1 / 2 : ℝ) ≤ 1)]
    intro u hu
    by_cases hu1 : u = 1
    · subst hu1
      exact (helper_contAt_kernel_one x hx0).continuousWithinAt
    · have huIoo : u ∈ Set.Ioo (0 : ℝ) 1 := by
        refine ⟨lt_of_lt_of_le (by norm_num) hu.1, lt_of_le_of_ne hu.2 hu1⟩
      exact ((helper_contOn_kernel_Ioo x hx).continuousAt
        (Ioo_mem_nhds huIoo.1 huIoo.2)).continuousWithinAt
  exact h12.intervalIntegrable

-- norm of UnitPow away from 0
private lemma helper_norm_UnitPow (x : ℂ) (u : ℝ) (hu0 : u ≠ 0) :
    ‖Entry9Qgamma.chapter8UnitPow x u‖ = Real.exp (x.re * Real.log u) := by
  have hE : Entry9Qgamma.chapter8UnitPow x u = Complex.exp (x * ((Real.log u : ℝ) : ℂ)) := by
    simp [Entry9Qgamma.chapter8UnitPow, hu0]
  rw [hE, Complex.norm_exp, Complex.mul_re]
  simp only [Complex.ofReal_re, Complex.ofReal_im, mul_zero, sub_zero]

-- the threshold below which |E| ≥ 2
private lemma helper_thresh_lt_one (x : ℂ) (hx : x.re < 0) (δ₀ : ℝ)
    (hδ₀pos : 0 < δ₀) (hδ₀ : Real.log δ₀ = Real.log 2 / x.re) : δ₀ < 1 := by
  have hlogδ : Real.log δ₀ < 0 := by
    rw [hδ₀]
    exact div_neg_of_pos_of_neg (Real.log_pos (by norm_num)) hx
  exact (Real.log_neg_iff hδ₀pos).mp hlogδ

private lemma helper_two_le_norm (x : ℂ) (hx : x.re < 0) (δ₀ : ℝ)
    (hδ₀ : Real.log δ₀ = Real.log 2 / x.re)
    (u : ℝ) (hu : u ∈ Set.Ioc 0 δ₀) : 2 ≤ ‖Entry9Qgamma.chapter8UnitPow x u‖ := by
  obtain ⟨hu0pos, huδ⟩ := hu
  have hu0' : u ≠ 0 := ne_of_gt hu0pos
  have hxr : x.re ≠ 0 := ne_of_lt hx
  have hlogu : Real.log u ≤ Real.log δ₀ := Real.log_le_log hu0pos huδ
  rw [hδ₀] at hlogu
  have hmul : Real.log 2 ≤ x.re * Real.log u := by
    have hstep := mul_le_mul_of_nonpos_left hlogu (le_of_lt hx)
    have hcancel : x.re * (Real.log 2 / x.re) = Real.log 2 := by field_simp
    rwa [hcancel] at hstep
  rw [helper_norm_UnitPow x u hu0']
  calc (2 : ℝ) = Real.exp (Real.log 2) := (Real.exp_log (by norm_num)).symm
    _ ≤ Real.exp (x.re * Real.log u) := Real.exp_le_exp.mpr hmul

-- pointwise domination near 0 by 2 * u^(-1 - Re x)
private lemma helper_bound_kernel (x : ℂ) (hx : x.re < 0) (δ₀ : ℝ)
    (hδ₀pos : 0 < δ₀) (hδ₀ : Real.log δ₀ = Real.log 2 / x.re)
    (u : ℝ) (hu : u ∈ Set.Ioc 0 δ₀) :
    ‖chapter8Entry10Kernel x u‖ ≤ 2 * u ^ (-1 - x.re) := by
  obtain ⟨hu0pos, huδ⟩ := hu
  have hu0' : u ≠ 0 := ne_of_gt hu0pos
  have hu0ne : u ≠ 0 := hu0'
  have hδ₀1 : δ₀ < 1 := helper_thresh_lt_one x hx δ₀ hδ₀pos hδ₀
  have hu1 : u < 1 := lt_of_le_of_lt huδ hδ₀1
  have hKu : chapter8Entry10Kernel x u = helper_formula x u := by
    simp [chapter8Entry10Kernel, helper_formula, hu0', ne_of_lt hu1]
  have h2 : 2 ≤ ‖Entry9Qgamma.chapter8UnitPow x u‖ := helper_two_le_norm x hx δ₀ hδ₀ u ⟨hu0pos, huδ⟩
  have hEpos : 0 < ‖Entry9Qgamma.chapter8UnitPow x u‖ := by linarith
  have hEne : ‖Entry9Qgamma.chapter8UnitPow x u‖ ≠ 0 := ne_of_gt hEpos
  have hnpos : 0 < ‖Entry9Qgamma.chapter8UnitPow x u - 1‖ := by
    have h := norm_sub_norm_le (Entry9Qgamma.chapter8UnitPow x u) 1
    rw [norm_one] at h
    linarith
  have hden : ‖Entry9Qgamma.chapter8UnitPow x u‖ / 2 ≤ ‖Entry9Qgamma.chapter8UnitPow x u - 1‖ := by
    have h := norm_sub_norm_le (Entry9Qgamma.chapter8UnitPow x u) 1
    rw [norm_one] at h
    linarith
  have hexp_eq : u * ‖Entry9Qgamma.chapter8UnitPow x u‖ = Real.exp ((1 + x.re) * Real.log u) := by
    rw [helper_norm_UnitPow x u hu0']
    nth_rewrite 1 [← Real.exp_log hu0pos]
    rw [← Real.exp_add]
    congr 1
    ring
  have hrpow_eq : u ^ (-1 - x.re) = (Real.exp ((1 + x.re) * Real.log u))⁻¹ := by
    rw [Real.rpow_def_of_pos hu0pos, ← Real.exp_neg]
    congr 1
    ring
  rw [hKu, helper_formula, norm_div, norm_mul, Complex.norm_real, Complex.norm_real,
    Real.norm_eq_abs, Real.norm_eq_abs, abs_of_pos (sub_pos.mpr hu1), abs_of_pos hu0pos,
    div_le_iff₀ (mul_pos hu0pos hnpos)]
  have h1u : (1 - u) ≤ 1 := by linarith
  refine le_trans h1u ?_
  have key : 2 * u ^ (-1 - x.re) * (u * ‖Entry9Qgamma.chapter8UnitPow x u - 1‖)
      = 2 * ‖Entry9Qgamma.chapter8UnitPow x u - 1‖ / ‖Entry9Qgamma.chapter8UnitPow x u‖ := by
    rw [hrpow_eq, ← hexp_eq]
    field_simp
  rw [key, le_div_iff₀ hEpos, one_mul]
  linarith

-- kernel is integrable on [0, δ] for δ ≤ δ₀, by domination
private lemma helper_intble_zero_delta (x : ℂ) (hx : x.re < 0) (δ₀ δ : ℝ)
    (hδ₀pos : 0 < δ₀) (hδ₀ : Real.log δ₀ = Real.log 2 / x.re)
    (hδpos : 0 < δ) (hδ : δ ≤ δ₀) :
    IntervalIntegrable (chapter8Entry10Kernel x) volume 0 δ := by
  have hr : (-1 : ℝ) < -1 - x.re := by linarith
  have hg : IntervalIntegrable (fun u : ℝ => 2 * u ^ (-1 - x.re)) volume 0 δ :=
    (intervalIntegral.intervalIntegrable_rpow' hr).const_mul 2
  rw [intervalIntegrable_iff_integrableOn_Ioc_of_le (le_of_lt hδpos)] at hg ⊢
  apply MeasureTheory.Integrable.mono' hg _ _
  · have hδ1 : δ < 1 := lt_of_le_of_lt hδ (helper_thresh_lt_one x hx δ₀ hδ₀pos hδ₀)
    have hcont : ContinuousOn (chapter8Entry10Kernel x) (Set.Ioc 0 δ) := by
      apply (helper_contOn_kernel_Ioo x hx).mono
      intro u hu
      exact ⟨hu.1, lt_of_le_of_lt hu.2 hδ1⟩
    exact hcont.aestronglyMeasurable measurableSet_Ioc
  · filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ioc] with u hu
    exact helper_bound_kernel x hx δ₀ hδ₀pos hδ₀ u ⟨hu.1, le_trans hu.2 hδ⟩

-- kernel is integrable on [δ, 1/2] (continuous, away from singularities)
private lemma helper_intble_delta_half (x : ℂ) (hx : x.re < 0) (δ : ℝ)
    (hδpos : 0 < δ) (hδ12 : δ ≤ 1 / 2) :
    IntervalIntegrable (chapter8Entry10Kernel x) volume δ (1 / 2) := by
  have hcont : ContinuousOn (chapter8Entry10Kernel x) (Set.uIcc δ (1 / 2)) := by
    rw [Set.uIcc_of_le hδ12]
    apply (helper_contOn_kernel_Ioo x hx).mono
    intro u hu
    exact ⟨lt_of_lt_of_le hδpos hu.1, lt_of_le_of_lt hu.2 (by norm_num)⟩
  exact hcont.intervalIntegrable

-- full integrability on [0, 1]
private lemma helper_intble_zero_one (x : ℂ) (hx : x.re < 0) (hx0 : x ≠ 0) :
    IntervalIntegrable (chapter8Entry10Kernel x) volume 0 1 := by
  have hδ₀pos : 0 < Real.exp (Real.log 2 / x.re) := Real.exp_pos _
  have hδ₀ : Real.log (Real.exp (Real.log 2 / x.re)) = Real.log 2 / x.re :=
    Real.log_exp _
  set δ := min (Real.exp (Real.log 2 / x.re)) (1 / 2) with hδdef
  have hδpos : 0 < δ := lt_min hδ₀pos (by norm_num)
  have h1 := helper_intble_zero_delta x hx _ _ hδ₀pos hδ₀ hδpos (min_le_left _ _)
  have h2 := helper_intble_delta_half x hx δ hδpos (min_le_right _ _)
  have h3 := helper_intble_half_one x hx hx0
  exact (h1.trans h2).trans h3


-- Step B: the kernel integral equals the digamma series, via geometric series.
private def intExp2 (x : ℂ) (m : ℕ) : ℂ := -(((m : ℕ) : ℂ) + 1) * x

private def intExp1 (x : ℂ) (m : ℕ) : ℂ := intExp2 x m - 1

private def intTerm (x : ℂ) (m : ℕ) (u : ℝ) : ℂ :=
  (u : ℂ) ^ intExp1 x m - (u : ℂ) ^ intExp2 x m

private lemma helper_intExp_re (x : ℂ) (hx : x.re < 0) (m : ℕ) :
    -1 < (intExp1 x m).re ∧ -1 < (intExp2 x m).re := by
  have ha : (0 : ℝ) < -x.re := neg_pos.mpr hx
  have hm : (0 : ℝ) < ((m : ℕ) : ℝ) + 1 := by positivity
  have hre2 : (intExp2 x m).re = (((m : ℕ) : ℝ) + 1) * (-x.re) := by
    simp only [intExp2, Complex.mul_re, Complex.neg_re, Complex.neg_im,
      Complex.add_re, Complex.add_im, Complex.natCast_re, Complex.natCast_im,
      Complex.one_re, Complex.one_im]
    ring
  have hpos : (0 : ℝ) < (intExp2 x m).re := by
    rw [hre2]
    positivity
  refine ⟨?_, by linarith⟩
  simp only [intExp1, Complex.sub_re, Complex.one_re]
  linarith

private lemma helper_intTerm_intble_aux (x : ℂ) (hx : x.re < 0)
    (m : ℕ) :
    IntervalIntegrable (fun u : ℝ => (u : ℂ) ^ intExp1 x m)
      volume 0 1
    ∧ IntervalIntegrable (fun u : ℝ => (u : ℂ) ^ intExp2 x m)
      volume 0 1 := by
  constructor
  · exact intervalIntegral.intervalIntegrable_cpow'
      (helper_intExp_re x hx m).1
  · exact intervalIntegral.intervalIntegrable_cpow'
      (helper_intExp_re x hx m).2

private lemma helper_intTerm_intble (x : ℂ) (hx : x.re < 0)
    (m : ℕ) :
    IntervalIntegrable (intTerm x m) volume 0 1 := by
  have h := helper_intTerm_intble_aux x hx m
  exact h.1.sub h.2

private lemma helper_intExp_add_ne (x : ℂ) (hx : x.re < 0)
    (m : ℕ) :
    intExp1 x m + 1 ≠ 0 ∧ intExp2 x m + 1 ≠ 0 := by
  have h1 : (0 : ℝ) < (intExp1 x m + 1).re := by
    rw [Complex.add_re, Complex.one_re]
    have h := (helper_intExp_re x hx m).1
    linarith
  have h2 : (0 : ℝ) < (intExp2 x m + 1).re := by
    rw [Complex.add_re, Complex.one_re]
    have h := (helper_intExp_re x hx m).2
    linarith
  constructor
  · intro hcon
    rw [hcon, Complex.zero_re] at h1
    exact lt_irrefl 0 h1
  · intro hcon
    rw [hcon, Complex.zero_re] at h2
    exact lt_irrefl 0 h2

private lemma helper_intExp_shift (x : ℂ) (m : ℕ) :
    intExp1 x m + 1 = intExp2 x m := by
  simp only [intExp1, sub_add_cancel]

private lemma helper_intTerm_integral (x : ℂ) (hx : x.re < 0)
    (m : ℕ) :
    (∫ u in (0 : ℝ)..1, intTerm x m u)
      = 1 / intExp2 x m - 1 / (intExp2 x m + 1) := by
  have h := helper_intTerm_intble_aux x hx m
  have hint : (∫ u in (0 : ℝ)..1, intTerm x m u)
      = (∫ u in (0 : ℝ)..1, (u : ℂ) ^ intExp1 x m)
        - (∫ u in (0 : ℝ)..1, (u : ℂ) ^ intExp2 x m) :=
    intervalIntegral.integral_sub h.1 h.2
  have hc := helper_intExp_add_ne x hx m
  rw [hint, integral_cpow (Or.inl (helper_intExp_re x hx m).1),
    integral_cpow (Or.inl (helper_intExp_re x hx m).2),
    Complex.ofReal_one, Complex.ofReal_zero, Complex.one_cpow,
    Complex.one_cpow, Complex.zero_cpow hc.1,
    Complex.zero_cpow hc.2, helper_intExp_shift x m, sub_zero]

private def geomBase (x : ℂ) (u : ℝ) : ℂ :=
  Complex.exp (-x * (Real.log u : ℂ))

private lemma helper_geomBase_norm (x : ℂ) (hx : x.re < 0)
    (u : ℝ) (hu : u ∈ Set.Ioo 0 1) :
    ‖geomBase x u‖ < 1 := by
  have hlog : Real.log u < 0 := (Real.log_neg_iff hu.1).mpr hu.2
  rw [geomBase, Complex.norm_exp]
  have hre : (-x * (Real.log u : ℂ)).re < 0 := by
    rw [Complex.mul_re, Complex.neg_re, Complex.neg_im,
      Complex.ofReal_re, Complex.ofReal_im]
    simp only [mul_zero, sub_zero]
    have ha : (0 : ℝ) < -x.re := neg_pos.mpr hx
    exact mul_neg_of_pos_of_neg ha hlog
  exact Real.exp_lt_one_iff.mpr hre

private lemma helper_cpow_exp (u : ℝ) (hu : 0 < u) (c : ℂ) :
    (u : ℂ) ^ c = Complex.exp (c * (Real.log u : ℂ)) := by
  have hu0 : (u : ℂ) ≠ 0 := by exact_mod_cast ne_of_gt hu
  rw [Complex.cpow_def_of_ne_zero hu0]
  have hlog : Complex.log (u : ℂ) = (Real.log u : ℂ) :=
    (Complex.ofReal_log hu.le).symm
  rw [hlog]
  congr 1
  ring

private lemma helper_intTerm_pointwise (x : ℂ) (u : ℝ)
    (hu : u ∈ Set.Ioo 0 1) (m : ℕ) :
    intTerm x m u
      = ((1 - u : ℝ) : ℂ) / (u : ℂ)
        * geomBase x u ^ (m + 1) := by
  have hu0 : (u : ℂ) ≠ 0 := by exact_mod_cast ne_of_gt hu.1
  have hC2 : (u : ℂ) ^ intExp2 x m = geomBase x u ^ (m + 1) := by
    rw [helper_cpow_exp u hu.1]
    have hexp : geomBase x u ^ (m + 1)
        = Complex.exp (intExp2 x m * (Real.log u : ℂ)) := by
      rw [geomBase, ← Complex.exp_nat_mul]
      congr 1
      simp only [intExp2]
      push_cast
      ring
    rw [hexp]
  have hadd : intExp2 x m = intExp1 x m + 1 := by
    simp only [intExp1, sub_add_cancel]
  have hC1 : (u : ℂ) ^ intExp1 x m
      = (u : ℂ) ^ intExp2 x m / (u : ℂ) := by
    have hmul : (u : ℂ) ^ intExp2 x m
        = (u : ℂ) ^ intExp1 x m * (u : ℂ) := by
      rw [hadd, Complex.cpow_add _ _ hu0, Complex.cpow_one]
    rw [hmul]
    exact (mul_div_cancel_right₀ _ hu0).symm
  have huv : (((1 - u : ℝ)) : ℂ) = 1 - (u : ℂ) := by
    rw [Complex.ofReal_sub, Complex.ofReal_one]
  simp only [intTerm]
  rw [hC1, hC2, huv]
  field_simp

private lemma helper_kernel_tsum (x : ℂ) (hx : x.re < 0)
    (u : ℝ) (hu : u ∈ Set.Ioo 0 1) :
    chapter8Entry10Kernel x u = ∑' m : ℕ, intTerm x m u := by
  have hu0 : u ≠ 0 := ne_of_gt hu.1
  have hu1 : u ≠ 1 := ne_of_lt hu.2
  have hu0C : (u : ℂ) ≠ 0 := by exact_mod_cast hu0
  have hK : chapter8Entry10Kernel x u = helper_formula x u := by
    simp [chapter8Entry10Kernel, helper_formula, hu0, hu1]
  have hnorm := helper_geomBase_norm x hx u hu
  have hgeom := hasSum_geometric_of_norm_lt_one hnorm
  have hshift : HasSum (fun m : ℕ => geomBase x u ^ (m + 1))
      (geomBase x u * (1 - geomBase x u)⁻¹) := by
    have hmul := hgeom.mul_left (geomBase x u)
    have hfun : (fun m : ℕ => geomBase x u ^ (m + 1))
        = fun n : ℕ => geomBase x u * geomBase x u ^ n := by
      funext m
      rw [pow_succ']
    rw [hfun]
    exact hmul
  have hE : Entry9Qgamma.chapter8UnitPow x u
      = Complex.exp (x * (Real.log u : ℂ)) := by
    simp [Entry9Qgamma.chapter8UnitPow, hu0]
  have hqE : geomBase x u * Entry9Qgamma.chapter8UnitPow x u = 1 := by
    rw [hE, geomBase, ← Complex.exp_add]
    have harg : -x * (Real.log u : ℂ) + x * (Real.log u : ℂ)
        = 0 := by
      ring
    rw [harg, Complex.exp_zero]
  have hq0 : geomBase x u ≠ 0 := Complex.exp_ne_zero _
  have hEeq : Entry9Qgamma.chapter8UnitPow x u = (geomBase x u)⁻¹ :=
    eq_inv_of_mul_eq_one_right hqE
  have h1q : (1 : ℂ) - geomBase x u ≠ 0 := by
    intro hcon
    have h11 : (1 : ℂ) = geomBase x u := sub_eq_zero.mp hcon
    rw [← h11] at hnorm
    simp at hnorm
  have hsum : (∑' m : ℕ, intTerm x m u)
      = ((1 - u : ℝ) : ℂ) / (u : ℂ)
        * (geomBase x u * (1 - geomBase x u)⁻¹) := by
    have hterm : ∀ m : ℕ, intTerm x m u
        = ((1 - u : ℝ) : ℂ) / (u : ℂ)
          * geomBase x u ^ (m + 1) :=
      fun m => helper_intTerm_pointwise x u hu m
    have hfun : (fun m : ℕ => intTerm x m u)
        = fun m : ℕ => ((1 - u : ℝ) : ℂ) / (u : ℂ)
          * geomBase x u ^ (m + 1) :=
      funext hterm
    rw [hfun]
    have htsum := hshift.summable.tsum_mul_left
      (((1 - u : ℝ) : ℂ) / (u : ℂ))
    rw [htsum]
    congr 1
    exact hshift.tsum_eq
  have hden : (u : ℂ) * ((geomBase x u)⁻¹ - 1) ≠ 0 := by
    have h := helper_denom_ne x hx u hu
    rwa [hEeq] at h
  rw [hK, hsum]
  simp only [helper_formula]
  rw [hEeq]
  field_simp

private lemma helper_geomBase_norm_eq (x : ℂ) (u : ℝ)
    (hu : 0 < u) :
    ‖geomBase x u‖ = u ^ (-x.re) := by
  rw [geomBase, Complex.norm_exp]
  have hre : (-x * (Real.log u : ℂ)).re
      = (-x.re) * Real.log u := by
    rw [Complex.mul_re, Complex.neg_re, Complex.neg_im,
      Complex.ofReal_re, Complex.ofReal_im]
    simp only [mul_zero, sub_zero]
  rw [hre, Real.rpow_def_of_pos hu]
  congr 1
  ring

private lemma helper_intTerm_norm (x : ℂ)
    (m : ℕ) (u : ℝ) (hu : u ∈ Set.Ioc 0 1) :
    ‖intTerm x m u‖
      ≤ (1 - u) * u ^ ((-x.re) * ((m : ℝ) + 1) - 1) := by
  by_cases hu1 : u = 1
  · subst hu1
    have hT : intTerm x m 1 = 0 := by
      simp [intTerm, Complex.one_cpow]
    rw [hT, norm_zero]
    simp
  · have huIoo : u ∈ Set.Ioo 0 1 :=
      ⟨hu.1, lt_of_le_of_ne hu.2 hu1⟩
    have hu0 : (u : ℝ) ≠ 0 := ne_of_gt hu.1
    have hC : ‖(((1 - u : ℝ)) : ℂ) / (u : ℂ)‖
        = (1 - u) / u := by
      rw [norm_div, Complex.norm_real, Complex.norm_real,
        Real.norm_eq_abs, Real.norm_eq_abs,
        abs_of_pos (sub_pos.mpr (lt_of_le_of_ne hu.2 hu1)),
        abs_of_pos hu.1]
    have hq : ‖geomBase x u ^ (m + 1)‖
        = u ^ ((-x.re) * ((m : ℝ) + 1)) := by
      rw [norm_pow, helper_geomBase_norm_eq x u hu.1,
        ← Real.rpow_natCast _ (m + 1),
        ← Real.rpow_mul (le_of_lt hu.1)]
      congr 1
      rw [Nat.cast_add, Nat.cast_one]
    have hsplit : u ^ ((-x.re) * ((m : ℝ) + 1))
        = u * u ^ ((-x.re) * ((m : ℝ) + 1) - 1) := by
      have h1 : (-x.re) * ((m : ℝ) + 1)
          = 1 + ((-x.re) * ((m : ℝ) + 1) - 1) := by ring
      conv_lhs => rw [h1]
      rw [Real.rpow_add hu.1, Real.rpow_one]
    have heq : (1 - u) / u * u ^ ((-x.re) * ((m : ℝ) + 1))
        = (1 - u) * u ^ ((-x.re) * ((m : ℝ) + 1) - 1) := by
      rw [hsplit, div_mul_eq_mul_div]
      have hrw : (1 - u) * (u * u ^ ((-x.re) * ((m : ℝ) + 1) - 1))
          = ((1 - u) * u ^ ((-x.re) * ((m : ℝ) + 1) - 1)) * u := by
        ring
      rw [hrw, mul_div_cancel_right₀ _ hu0]
    rw [helper_intTerm_pointwise x u huIoo m, norm_mul, hC, hq]
    exact le_of_eq heq

private lemma helper_bound_integral (x : ℂ) (hx : x.re < 0)
    (m : ℕ) :
    (∫ u in (0:ℝ)..1, (1 - u) * u ^ ((-x.re) * ((m : ℝ) + 1) - 1))
      = 1 / (((m : ℝ) + 1) * (-x.re))
        - 1 / (((m : ℝ) + 1) * (-x.re) + 1) := by
  have ha : (0:ℝ) < -x.re := neg_pos.mpr hx
  have hm : (0:ℝ) < ((m : ℕ) : ℝ) + 1 := by positivity
  set p : ℝ := (-x.re) * ((m : ℝ) + 1) - 1 with hpdef
  have hp : (-1:ℝ) < p := by
    rw [hpdef]
    have hpos : (0:ℝ) < (-x.re) * ((m : ℝ) + 1) :=
      mul_pos ha hm
    linarith
  have hp1 : (-1:ℝ) < p + 1 := by linarith
  have hint1 : IntervalIntegrable (fun u : ℝ => u ^ p)
      volume 0 1 :=
    intervalIntegral.intervalIntegrable_rpow' hp
  have hint2 : IntervalIntegrable (fun u : ℝ => u ^ (p + 1))
      volume 0 1 :=
    intervalIntegral.intervalIntegrable_rpow' hp1
  have hae1 : ∀ᵐ u ∂(volume : Measure ℝ), u ∈ Set.Ioc 0 1 →
      (1 - u) * u ^ p = u ^ p - u ^ (p + 1) := by
    filter_upwards with u
    intro hu
    have hu0 : (0:ℝ) < u := hu.1
    have hexp : u ^ (p + 1) = u ^ p * u := by
      rw [Real.rpow_add hu0, Real.rpow_one]
    rw [sub_mul, one_mul, hexp]
    ring
  have hae2 : ∀ᵐ u ∂(volume : Measure ℝ), u ∈ Set.Ioc 1 0 →
      (1 - u) * u ^ p = u ^ p - u ^ (p + 1) := by
    filter_upwards with u
    intro hu
    rw [Set.mem_Ioc] at hu
    have h10 : (1:ℝ) < 0 := lt_of_lt_of_le hu.1 hu.2
    norm_num at h10
  have hcongr := intervalIntegral.integral_congr_ae' (μ := volume)
    (f := fun u : ℝ => (1 - u) * u ^ p)
    (g := fun u : ℝ => u ^ p - u ^ (p + 1)) hae1 hae2
  have hsub : (∫ u in (0:ℝ)..1, (u ^ p - u ^ (p + 1)))
      = (∫ u in (0:ℝ)..1, u ^ p)
        - (∫ u in (0:ℝ)..1, u ^ (p + 1)) :=
    intervalIntegral.integral_sub hint1 hint2
  have h01 : p + 1 ≠ 0 := ne_of_gt (by linarith : (0:ℝ) < p + 1)
  have h02 : (p + 1) + 1 ≠ 0 :=
    ne_of_gt (by linarith : (0:ℝ) < (p + 1) + 1)
  have hpp : p + 1 = ((m : ℝ) + 1) * (-x.re) := by
    rw [hpdef]
    ring
  rw [hcongr, hsub, integral_rpow (Or.inl hp),
    integral_rpow (Or.inl hp1), Real.one_rpow, Real.one_rpow,
    Real.zero_rpow h01, Real.zero_rpow h02, hpp, sub_zero]

private lemma helper_value_le_majorant (x : ℂ) (hx : x.re < 0)
    (m : ℕ) :
    1 / (((m : ℝ) + 1) * (-x.re))
      - 1 / (((m : ℝ) + 1) * (-x.re) + 1)
      ≤ (1 / (-x.re) ^ 2) / ((m : ℝ) + 1) ^ 2 := by
  have ha : (0:ℝ) < -x.re := neg_pos.mpr hx
  have hm : (0:ℝ) < ((m : ℕ) : ℝ) + 1 := by positivity
  have hX : (0:ℝ) < ((m : ℝ) + 1) * (-x.re) := mul_pos hm ha
  have hX0 : ((m : ℝ) + 1) * (-x.re) ≠ 0 := ne_of_gt hX
  have hX10 : ((m : ℝ) + 1) * (-x.re) + 1 ≠ 0 :=
    ne_of_gt (by linarith)
  have heq : 1 / (((m : ℝ) + 1) * (-x.re))
      - 1 / (((m : ℝ) + 1) * (-x.re) + 1)
      = 1 / ((((m : ℝ) + 1) * (-x.re))
        * (((m : ℝ) + 1) * (-x.re) + 1)) := by
    rw [div_sub_div _ _ hX0 hX10, one_mul, mul_one,
      show ((m : ℝ) + 1) * (-x.re) + 1 - ((m : ℝ) + 1) * (-x.re)
        = 1 from by ring]
  have hle : (-x.re) ^ 2 * ((m : ℝ) + 1) ^ 2
      ≤ (((m : ℝ) + 1) * (-x.re))
        * (((m : ℝ) + 1) * (-x.re) + 1) := by
    have h1 : ((m : ℝ) + 1) * (-x.re)
        ≤ ((m : ℝ) + 1) * (-x.re) + 1 := by linarith
    have h2 := mul_le_mul_of_nonneg_left h1 (le_of_lt hX)
    have h3 : (-x.re) ^ 2 * ((m : ℝ) + 1) ^ 2
        = (((m : ℝ) + 1) * (-x.re))
          * (((m : ℝ) + 1) * (-x.re)) := by
      ring
    rw [h3]
    exact h2
  have hrw : (1 / (-x.re) ^ 2) / ((m : ℝ) + 1) ^ 2
      = 1 / ((-x.re) ^ 2 * ((m : ℝ) + 1) ^ 2) := by
    simp only [div_eq_mul_inv, one_mul, mul_inv]
  rw [heq, hrw]
  exact one_div_le_one_div_of_le (by positivity) hle

private lemma helper_norm_integral_le (x : ℂ) (hx : x.re < 0)
    (m : ℕ) :
    (∫ u in Set.Ioc (0:ℝ) 1, ‖intTerm x m u‖ ∂volume)
      ≤ 1 / (((m : ℝ) + 1) * (-x.re))
        - 1 / (((m : ℝ) + 1) * (-x.re) + 1) := by
  have hTInt : Integrable (intTerm x m)
      (volume.restrict (Set.Ioc 0 1)) :=
    (intervalIntegrable_iff_integrableOn_Ioc_of_le zero_le_one).mp
      (helper_intTerm_intble x hx m)
  have hnormInt : Integrable (fun u => ‖intTerm x m u‖)
      (volume.restrict (Set.Ioc 0 1)) := hTInt.norm
  have ha : (0:ℝ) < -x.re := neg_pos.mpr hx
  have hm : (0:ℝ) < ((m : ℕ) : ℝ) + 1 := by positivity
  set p : ℝ := (-x.re) * ((m : ℝ) + 1) - 1 with hpdef
  have hp : (-1:ℝ) < p := by
    rw [hpdef]
    have hpos : (0:ℝ) < (-x.re) * ((m : ℝ) + 1) :=
      mul_pos ha hm
    linarith
  have hp1 : (-1:ℝ) < p + 1 := by linarith
  have hint1 : IntervalIntegrable (fun u : ℝ => u ^ p)
      volume 0 1 :=
    intervalIntegral.intervalIntegrable_rpow' hp
  have hint2 : IntervalIntegrable (fun u : ℝ => u ^ (p + 1))
      volume 0 1 :=
    intervalIntegral.intervalIntegrable_rpow' hp1
  have hdiffInt : Integrable (fun u : ℝ => u ^ p - u ^ (p + 1))
      (volume.restrict (Set.Ioc 0 1)) :=
    (intervalIntegrable_iff_integrableOn_Ioc_of_le zero_le_one).mp
      (hint1.sub hint2)
  have hae_eq : (fun u : ℝ => u ^ p - u ^ (p + 1))
      =ᵐ[volume.restrict (Set.Ioc 0 1)]
      (fun u : ℝ => (1 - u) * u ^ p) := by
    filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ioc]
      with u hu
    have hu0 : (0:ℝ) < u := hu.1
    have hexp : u ^ (p + 1) = u ^ p * u := by
      rw [Real.rpow_add hu0, Real.rpow_one]
    rw [sub_mul, one_mul, hexp]
    ring
  have hboundInt : Integrable (fun u : ℝ => (1 - u) * u ^ p)
      (volume.restrict (Set.Ioc 0 1)) :=
    hdiffInt.congr hae_eq
  have hae_le : ∀ᵐ u ∂(volume.restrict (Set.Ioc 0 1)),
      ‖intTerm x m u‖ ≤ (1 - u) * u ^ p := by
    filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ioc]
      with u hu
    have h := helper_intTerm_norm x m u hu
    rw [← hpdef] at h
    exact h
  have hmono := MeasureTheory.integral_mono_ae hnormInt hboundInt
    hae_le
  have hval : (∫ u in Set.Ioc 0 1, (1 - u) * u ^ p ∂volume)
      = 1 / (((m : ℝ) + 1) * (-x.re))
        - 1 / (((m : ℝ) + 1) * (-x.re) + 1) := by
    have h := helper_bound_integral x hx m
    rw [← intervalIntegral.integral_of_le zero_le_one]
    rw [← hpdef] at h
    exact h
  rw [← hval]
  exact hmono

private lemma helper_norm_integral_summable (x : ℂ)
    (hx : x.re < 0) :
    Summable (fun m : ℕ =>
      ∫ u in Set.Ioc (0:ℝ) 1, ‖intTerm x m u‖ ∂volume) := by
  have ha : (0:ℝ) < -x.re := neg_pos.mpr hx
  have hmaj : Summable (fun m : ℕ =>
      (1 / (-x.re) ^ 2) / ((m : ℝ) + 1) ^ 2) := by
    have hsum := Real.summable_one_div_add_nat_succ_sq.mul_left
      (1 / (-x.re) ^ 2)
    refine hsum.congr (fun m => ?_)
    rw [mul_one_div]
  have h0 : ∀ m : ℕ, (0:ℝ) ≤
      ∫ u in Set.Ioc (0:ℝ) 1, ‖intTerm x m u‖ ∂volume := by
    intro m
    exact MeasureTheory.integral_nonneg_of_ae
      (ae_of_all _ (fun u => norm_nonneg _))
  have hle : ∀ m : ℕ,
      (∫ u in Set.Ioc (0:ℝ) 1, ‖intTerm x m u‖ ∂volume)
        ≤ (1 / (-x.re) ^ 2) / ((m : ℝ) + 1) ^ 2 := by
    intro m
    exact (helper_norm_integral_le x hx m).trans
      (helper_value_le_majorant x hx m)
  exact Summable.of_nonneg_of_le h0 hle hmaj

private lemma helper_s_re (x : ℂ) (hx : x.re < 0) :
    1 < (1 - 1 / x).re := by
  have hx0 : x ≠ 0 := helper_x_ne x hx
  have hns : 0 < Complex.normSq x := Complex.normSq_pos.mpr hx0
  have h1 : (1 / x).re < 0 := by
    rw [one_div, Complex.inv_re]
    exact div_neg_of_neg_of_pos hx hns
  have heq : (1 - 1 / x).re = 1 - (1 / x).re := by
    simp [Complex.sub_re, Complex.one_re]
  linarith

private lemma helper_intExp2_pos (x : ℂ) (hx : x.re < 0)
    (m : ℕ) :
    0 < (intExp2 x m).re := by
  have ha : (0:ℝ) < -x.re := neg_pos.mpr hx
  have hm : (0:ℝ) < ((m : ℕ) : ℝ) + 1 := by positivity
  have hre2 : (intExp2 x m).re
      = (((m : ℕ) : ℝ) + 1) * (-x.re) := by
    simp only [intExp2, Complex.mul_re, Complex.neg_re, Complex.neg_im,
      Complex.add_re, Complex.add_im, Complex.natCast_re, Complex.natCast_im,
      Complex.one_re, Complex.one_im]
    ring
  rw [hre2]
  positivity

private lemma helper_term_algebra (x : ℂ) (hx : x.re < 0)
    (m : ℕ) :
    (-x) * (1 / intExp2 x m - 1 / (intExp2 x m + 1))
      = Complex.digammaSeriesTerm m (1 - 1 / x) := by
  have hx0 : x ≠ 0 := helper_x_ne x hx
  have h2ne : intExp2 x m ≠ 0 := by
    have hpos : (0:ℝ) < (intExp2 x m).re :=
      helper_intExp2_pos x hx m
    intro hcon
    rw [hcon, Complex.zero_re] at hpos
    exact lt_irrefl 0 hpos
  have h2p1ne : intExp2 x m + 1 ≠ 0 :=
    (helper_intExp_add_ne x hx m).2
  have hn0 : ((m : ℕ) : ℂ) + 1 ≠ 0 := by
    have hpos : (0:ℝ) < (((m : ℕ) : ℂ) + 1).re := by
      rw [Complex.add_re, Complex.natCast_re, Complex.one_re]
      have hm0 : (0:ℝ) ≤ (m : ℝ) := Nat.cast_nonneg m
      linarith
    intro hcon
    rw [hcon, Complex.zero_re] at hpos
    exact lt_irrefl 0 hpos
  have hns : ((m : ℕ) : ℂ) + (1 - 1 / x) ≠ 0 := by
    have hpos : (0:ℝ) < (((m : ℕ) : ℂ) + (1 - 1 / x)).re := by
      rw [Complex.add_re, Complex.natCast_re]
      have h1x := helper_s_re x hx
      have hm0 : (0:ℝ) ≤ (m : ℝ) := Nat.cast_nonneg m
      linarith
    intro hcon
    rw [hcon, Complex.zero_re] at hpos
    exact lt_irrefl 0 hpos
  have hnx1 : (((m : ℕ) : ℂ) + 1) * x - 1 ≠ 0 := by
    have hneg : ((((m : ℕ) : ℂ) + 1) * x - 1).re < 0 := by
      have hre : ((((m : ℕ) : ℂ) + 1) * x - 1).re
          = (((m : ℕ) : ℝ) + 1) * x.re - 1 := by
        simp only [Complex.sub_re, Complex.mul_re, Complex.add_re,
          Complex.add_im, Complex.natCast_re, Complex.natCast_im,
          Complex.one_re, Complex.one_im]
        ring
      rw [hre]
      have hle : (((m : ℕ) : ℝ) + 1) * x.re ≤ 0 :=
        mul_nonpos_of_nonneg_of_nonpos (by positivity)
          (le_of_lt hx)
      linarith
    intro hcon
    rw [hcon, Complex.zero_re] at hneg
    exact lt_irrefl 0 hneg
  have hfrac : (1:ℂ) / (((m : ℕ) : ℂ) + (1 - 1 / x))
      = x / ((((m : ℕ) : ℂ) + 1) * x - 1) := by
    rw [div_eq_div_iff hns hnx1, one_mul]
    have hxx : x * (1 / x) = 1 := mul_one_div_cancel hx0
    linear_combination hxx
  have he1 : (1:ℂ) / intExp2 x m - 1 / (intExp2 x m + 1)
      = 1 / (intExp2 x m * (intExp2 x m + 1)) := by
    have hnum : (1:ℂ) * (intExp2 x m + 1) - intExp2 x m * 1
        = 1 := by
      ring
    rw [div_sub_div _ _ h2ne h2p1ne, hnum]
  have he2 : (1:ℂ) / (((m : ℕ) : ℂ) + 1)
      - x / ((((m : ℕ) : ℂ) + 1) * x - 1)
      = -1 / ((((m : ℕ) : ℂ) + 1)
        * ((((m : ℕ) : ℂ) + 1) * x - 1)) := by
    have hnum : (1:ℂ) * ((((m : ℕ) : ℂ) + 1) * x - 1)
        - (((m : ℕ) : ℂ) + 1) * x = -1 := by
      ring
    rw [div_sub_div _ _ hn0 hnx1, hnum]
  have hee : intExp2 x m * (intExp2 x m + 1) ≠ 0 :=
    mul_ne_zero h2ne h2p1ne
  have hnn : (((m : ℕ) : ℂ) + 1)
      * ((((m : ℕ) : ℂ) + 1) * x - 1) ≠ 0 :=
    mul_ne_zero hn0 hnx1
  simp only [Complex.digammaSeriesTerm]
  rw [hfrac, he1, he2, mul_one_div, div_eq_div_iff hee hnn]
  simp only [intExp2]
  ring

private lemma helper_integral_tsum (x : ℂ) (hx : x.re < 0) :
    (∫ u in (0:ℝ)..1, chapter8Entry10Kernel x u)
      = ∑' m : ℕ, (∫ u in (0:ℝ)..1, intTerm x m u) := by
  have hTInt : ∀ m : ℕ, Integrable (intTerm x m)
      (volume.restrict (Set.Ioc 0 1)) := fun m =>
    (intervalIntegrable_iff_integrableOn_Ioc_of_le zero_le_one).mp
      (helper_intTerm_intble x hx m)
  have hsum := MeasureTheory.hasSum_integral_of_summable_integral_norm
    hTInt (helper_norm_integral_summable x hx)
  have htsum := hsum.tsum_eq
  have hae : (chapter8Entry10Kernel x)
      =ᵐ[volume.restrict (Set.Ioc 0 1)]
      (fun u => ∑' m : ℕ, intTerm x m u) := by
    have h1ne : ∀ᵐ u ∂(volume : Measure ℝ), u ≠ 1 := by
      rw [ae_iff]
      have hempty : {a : ℝ | ¬ a ≠ 1} = {1} := by
        ext a
        simp
      rw [hempty]
      exact Real.volume_singleton
    have h1neR : ∀ᵐ u ∂(volume.restrict (Set.Ioc (0:ℝ) (1:ℝ))),
        u ≠ 1 := by
      rw [ae_restrict_iff' measurableSet_Ioc]
      filter_upwards [h1ne] with u hu _
      exact hu
    filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ioc,
      h1neR] with u huIoc hu1
    have huIoo : u ∈ Set.Ioo 0 1 :=
      ⟨huIoc.1, lt_of_le_of_ne huIoc.2 hu1⟩
    exact helper_kernel_tsum x hx u huIoo
  have hcongr : (∫ u in Set.Ioc 0 1, chapter8Entry10Kernel x u ∂volume)
      = ∫ u in Set.Ioc 0 1, (∑' m : ℕ, intTerm x m u) ∂volume :=
    MeasureTheory.integral_congr_ae hae
  have hLHS : (∫ u in (0:ℝ)..1, chapter8Entry10Kernel x u)
      = ∫ u in Set.Ioc 0 1, chapter8Entry10Kernel x u ∂volume :=
    intervalIntegral.integral_of_le zero_le_one
  have hfun : (fun m : ℕ =>
        ∫ u in Set.Ioc 0 1, intTerm x m u ∂volume)
      = fun m : ℕ => ∫ u in (0:ℝ)..1, intTerm x m u :=
    funext (fun m =>
      (intervalIntegral.integral_of_le zero_le_one).symm)
  rw [hLHS, hcongr, ← htsum, hfun]

private lemma helper_J_summable (x : ℂ) (hx : x.re < 0) :
    Summable (fun m : ℕ =>
      ∫ u in (0:ℝ)..1, intTerm x m u) := by
  have hTInt : ∀ m : ℕ, Integrable (intTerm x m)
      (volume.restrict (Set.Ioc 0 1)) := fun m =>
    (intervalIntegrable_iff_integrableOn_Ioc_of_le zero_le_one).mp
      (helper_intTerm_intble x hx m)
  have hsum := MeasureTheory.hasSum_integral_of_summable_integral_norm
    hTInt (helper_norm_integral_summable x hx)
  refine hsum.summable.congr (fun m => ?_)
  exact (intervalIntegral.integral_of_le zero_le_one).symm

private lemma helper_integral_eq_series (x : ℂ) (hx : x.re < 0) :
    (-x) * (∫ u in (0:ℝ)..1, chapter8Entry10Kernel x u)
      = Complex.digammaSeriesFun (1 - 1 / x) := by
  have hI := helper_integral_tsum x hx
  have hJsumm := helper_J_summable x hx
  have hterm : ∀ m : ℕ, (-x) * (∫ u in (0:ℝ)..1, intTerm x m u)
      = Complex.digammaSeriesTerm m (1 - 1 / x) := by
    intro m
    rw [helper_intTerm_integral x hx m]
    exact helper_term_algebra x hx m
  have hfun : (fun m : ℕ =>
        (-x) * (∫ u in (0:ℝ)..1, intTerm x m u))
      = fun m : ℕ => Complex.digammaSeriesTerm m (1 - 1 / x) :=
    funext hterm
  calc (-x) * (∫ u in (0:ℝ)..1, chapter8Entry10Kernel x u)
      = (-x) * (∑' m : ℕ, (∫ u in (0:ℝ)..1, intTerm x m u)) := by
        rw [hI]
    _ = ∑' m : ℕ, ((-x) * (∫ u in (0:ℝ)..1, intTerm x m u)) :=
        (hJsumm.tsum_mul_left (-x)).symm
    _ = ∑' m : ℕ, Complex.digammaSeriesTerm m (1 - 1 / x) := by rw [hfun]
    _ = Complex.digammaSeriesFun (1 - 1 / x) := rfl

/-- **Ramanujan's integral for $\psi(1 - 1/x)$ (Chapter 8, Entry 10).** Let $x$ be a complex
number with $\operatorname{Re} x < 0$. For real $u$ put $u^x = e^{x \log |u|}$ when $u \ne 0$,
and define $K_x(0) = 0$, $K_x(1) = -1/x$ and $K_x(u) = \frac{1 - u}{u\,(u^x - 1)}$ for every
other real $u$, the quotient being taken to be $0$ at $u = -1$, where its denominator vanishes.
Then $x \ne 0$ and $\Gamma(1 - 1/x) \ne 0$; for every $u \in (0, 1)$ the denominator
$u\,(u^x - 1)$ is nonzero and $K_x(u) = \frac{1 - u}{u\,(u^x - 1)}$; $K_x$ is integrable on
$[0, 1]$; and
$$\psi\left(1 - \frac{1}{x}\right) + \gamma = -x \int_0^1 K_x(u)\,du,$$
where $\psi$ is the digamma function and $\gamma$ is the Euler–Mascheroni constant.

Source: Bruce C. Berndt, Ramanujan's Notebooks, Part I, Chapter 8.
-/
theorem ramanujan_part1_ch8_entry10_qgammalimit (x : ℂ) (hx : x.re < 0) :
    x ≠ 0 ∧
      Complex.Gamma (1 - 1 / x) ≠ 0 ∧
      chapter8Entry10Kernel x 0 = 0 ∧
      chapter8Entry10Kernel x 1 = -1 / x ∧
      (∀ u : ℝ, u ∈ Set.Ioo 0 1 →
        (u : ℂ) * (Entry9Qgamma.chapter8UnitPow x u - 1) ≠ 0 ∧
          chapter8Entry10Kernel x u =
            ((1 - u : ℝ) : ℂ) /
              ((u : ℂ) * (Entry9Qgamma.chapter8UnitPow x u - 1))) ∧
      IntervalIntegrable (chapter8Entry10Kernel x) volume 0 1 ∧
      Complex.digamma (1 - 1 / x) +
          (Real.eulerMascheroniConstant : ℂ) =
        -x * ∫ u in (0 : ℝ)..1, chapter8Entry10Kernel x u := by
  refine ⟨helper_x_ne x hx, helper_Gamma_ne x hx, ?_, ?_, ?_, ?_, ?_⟩
  · simp [chapter8Entry10Kernel]
  · simp [chapter8Entry10Kernel, one_ne_zero]
  · intro u hu
    obtain ⟨hu0, hu1⟩ := hu
    exact ⟨helper_denom_ne x hx u ⟨hu0, hu1⟩, by
      simp [chapter8Entry10Kernel, ne_of_gt hu0, ne_of_lt hu1]⟩
  · exact helper_intble_zero_one x hx (helper_x_ne x hx)
  · have hs : (1:ℝ) < (1 - 1 / x).re := helper_s_re x hx
    have hA := (Complex.hasSum_digamma_series (1 - 1 / x) hs).tsum_eq
    have hB := helper_integral_eq_series x hx
    rw [← hA]
    exact hB.symm

end
end Entry10Qgammalimit
end MathlibExt.Analysis.Ramanujan.Part1Ch8
end
