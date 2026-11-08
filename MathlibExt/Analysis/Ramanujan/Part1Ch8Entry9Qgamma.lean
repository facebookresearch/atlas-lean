/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import Mathlib.Analysis.Convex.Deriv

public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Analysis.Calculus.ContDiff.Basic
public import Mathlib.Analysis.Calculus.IteratedDeriv.Defs
public import Mathlib.Analysis.Complex.Exponential
public import Mathlib.Analysis.Real.Sqrt
public import Mathlib.Analysis.SpecialFunctions.Complex.Log
public import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
public import Mathlib.Analysis.SpecialFunctions.Gamma.Digamma
public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Mathlib.Analysis.SpecialFunctions.Pow.Complex
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
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.Analysis.Analytic.IsolatedZeros
import Mathlib.Analysis.Calculus.FDeriv.Analytic
import Mathlib.Analysis.Calculus.ParametricIntervalIntegral
import Mathlib.Analysis.Complex.CauchyIntegral
import Mathlib.Analysis.Complex.Convex
import Mathlib.Analysis.Complex.RealDeriv
import Mathlib.Analysis.SpecialFunctions.Gamma.BohrMollerup
import Mathlib.Analysis.SpecialFunctions.Gamma.Deriv
import Mathlib.Analysis.SpecialFunctions.Integrability.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Ring

@[expose] public section

section
/-!
# Ramanujan's Notebooks, Part I, Chapter 8

Statements of entries from B. C. Berndt, *Ramanujan's Notebooks, Part I*
(Springer, 1985), with proofs.
-/

namespace MathlibExt.Analysis.Ramanujan.Part1Ch8

namespace Entry9Qgamma

open scoped Nat Real BigOperators Interval Polynomial ContDiff
open Asymptotics Filter Finset Complex Topology MeasureTheory

noncomputable section

def chapter8Digamma (z : ℂ) : ℂ :=
  deriv Complex.Gamma z / Complex.Gamma z

def chapter8UnitPow (x : ℂ) (u : ℝ) : ℂ :=
  if u = 0 then 0 else Complex.exp (x * Real.log u)

def chapter8UnitPowRatio (x : ℂ) (u : ℝ) : ℂ :=
  chapter8UnitPow x u / (1 + chapter8UnitPow x u)

/-- The wishlist digamma is the canonical `Complex.digamma`. -/
theorem chapter8Digamma_eq_digamma (z : ℂ) :
    chapter8Digamma z = Complex.digamma z := by
  unfold chapter8Digamma
  rw [Complex.digamma_def, logDeriv_apply]

/-- On `(0, ∞)` the unit power is the standard `Complex.cpow`. -/
theorem chapter8UnitPow_eq_cpow (x : ℂ) (u : ℝ) (hu : 0 < u) :
    chapter8UnitPow x u = (u : ℂ) ^ x := by
  have hune : u ≠ 0 := ne_of_gt hu
  have hcu : (u : ℂ) ≠ 0 := by exact_mod_cast hune
  unfold chapter8UnitPow
  simp only [hune, ↓reduceIte]
  rw [Complex.cpow_def_of_ne_zero hcu, Complex.ofReal_log hu.le]
  congr 1
  ring

/-- Source: Bruce C. Berndt, Ramanujan's Notebooks, Part I, Chapter 8. -/
private lemma entry9_x_ne_zero {x : ℂ} (hx : 0 < x.re) : x ≠ 0 := by
  intro h
  rw [h] at hx
  simp at hx

private lemma entry9_norm_unitPow_of_pos {x : ℂ} {u : ℝ} (hu : 0 < u) :
    ‖chapter8UnitPow x u‖ = u ^ x.re := by
  have hre : (x * ((Real.log u : ℝ) : ℂ)).re = x.re * Real.log u := by
    rw [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, mul_zero, sub_zero]
  unfold chapter8UnitPow
  rw [ite_eq_right (ne_of_gt hu)]
  rw [Complex.norm_exp, Real.rpow_def_of_pos hu, hre]
  exact congrArg Real.exp (mul_comm _ _)

private lemma entry9_one_add_unitPow_ne {x : ℂ} (hx : 0 < x.re) {u : ℝ} (hu : 0 < u) :
    1 + chapter8UnitPow x u ≠ 0 := by
  by_cases hu1 : u = 1
  · subst hu1
    unfold chapter8UnitPow
    rw [ite_eq_right one_ne_zero, Real.log_one]
    simp
  · intro hcon
    have hw1 : ‖chapter8UnitPow x u‖ = 1 := by
      have h1 : (1 : ℂ) = -chapter8UnitPow x u := eq_neg_of_add_eq_zero_left hcon
      have h2 := congrArg Norm.norm h1
      rw [norm_one, norm_neg] at h2
      exact h2.symm
    rw [entry9_norm_unitPow_of_pos hu] at hw1
    rcases lt_trichotomy u 1 with hlt | heq | hgt
    · have hlt1 := Real.rpow_lt_one hu.le hlt hx
      rw [hw1] at hlt1
      exact lt_irrefl 1 hlt1
    · exact hu1 heq
    · have hgt1 := Real.one_lt_rpow hgt hx
      rw [hw1] at hgt1
      exact lt_irrefl 1 hgt1

private lemma entry9_one_add_unitPow_ne_Icc {x : ℂ} (hx : 0 < x.re) {u : ℝ}
    (hu : u ∈ Set.Icc 0 1) : 1 + chapter8UnitPow x u ≠ 0 := by
  rcases eq_or_lt_of_le hu.1 with h0 | hpos
  · subst h0
    unfold chapter8UnitPow
    rw [ite_eq_left rfl]
    simp
  · exact entry9_one_add_unitPow_ne hx hpos

private lemma entry9_continuousOn_unitPow_Ioi {x : ℂ} :
    ContinuousOn (chapter8UnitPow x) (Set.Ioi 0) := by
  have hlog : ContinuousOn (fun u : ℝ => ((Real.log u : ℝ) : ℂ)) (Set.Ioi 0) :=
    Complex.continuous_ofReal.comp_continuousOn
      (Real.continuousOn_log.mono fun u hu => ne_of_gt (Set.mem_Ioi.mp hu))
  have hmul : ContinuousOn (fun u : ℝ => x * ((Real.log u : ℝ) : ℂ)) (Set.Ioi 0) :=
    ContinuousOn.const_mul hlog x
  have hexp : ContinuousOn (fun u : ℝ => Complex.exp (x * ((Real.log u : ℝ) : ℂ)))
      (Set.Ioi 0) :=
    Complex.continuous_exp.comp_continuousOn hmul
  refine hexp.congr ?_
  intro u hu
  unfold chapter8UnitPow
  rw [ite_eq_right (ne_of_gt (Set.mem_Ioi.mp hu))]

private lemma entry9_continuousOn_ratio_Ioi {x : ℂ} (hx : 0 < x.re) :
    ContinuousOn (chapter8UnitPowRatio x) (Set.Ioi 0) := by
  have hN := entry9_continuousOn_unitPow_Ioi (x := x)
  have hD : ContinuousOn (fun u : ℝ => (1 : ℂ) + chapter8UnitPow x u) (Set.Ioi 0) :=
    continuousOn_const.add hN
  have hDen : ∀ u ∈ Set.Ioi (0 : ℝ), (1 : ℂ) + chapter8UnitPow x u ≠ 0 := by
    intro u hu
    exact entry9_one_add_unitPow_ne hx (Set.mem_Ioi.mp hu)
  have hdiv := ContinuousOn.div hN hD hDen
  refine hdiv.congr ?_
  intro u hu
  unfold chapter8UnitPowRatio
  rfl

private lemma entry9_tendsto_unitPow_nhdsWithin {x : ℂ} (hx : 0 < x.re) :
    Filter.Tendsto (chapter8UnitPow x) (nhdsWithin (0 : ℝ) (Set.Icc 0 1)) (nhds 0) := by
  have hxne : x.re ≠ 0 := ne_of_gt hx
  have hbound : ∀ u : ℝ, u ∈ Set.Icc (0 : ℝ) 1 → ‖chapter8UnitPow x u‖ = u ^ x.re := by
    intro u hu
    rcases eq_or_lt_of_le hu.1 with h0 | hpos
    · subst h0
      unfold chapter8UnitPow
      rw [ite_eq_left rfl, norm_zero, Real.zero_rpow hxne]
    · exact entry9_norm_unitPow_of_pos hpos
  have hT : Filter.Tendsto (fun u : ℝ => u ^ x.re) (nhds (0 : ℝ)) (nhds ((0 : ℝ) ^ x.re)) :=
    Real.continuousAt_rpow_const 0 x.re (Or.inr hx.le)
  have h0 : (0 : ℝ) ^ x.re = 0 := Real.zero_rpow hxne
  rw [h0] at hT
  have hglim : Filter.Tendsto (fun u : ℝ => u ^ x.re)
      (nhdsWithin (0 : ℝ) (Set.Icc 0 1)) (nhds 0) :=
    hT.mono_left nhdsWithin_le_nhds
  refine squeeze_zero_norm' ?_ hglim
  filter_upwards [self_mem_nhdsWithin (a := (0 : ℝ)) (s := Set.Icc 0 1)] with u hu
  rw [hbound u hu]

private lemma entry9_ratio_at_zero {x : ℂ} : chapter8UnitPowRatio x 0 = 0 := by
  unfold chapter8UnitPowRatio chapter8UnitPow
  simp

private lemma entry9_tendsto_ratio_nhdsWithin {x : ℂ} (hx : 0 < x.re) :
    Filter.Tendsto (chapter8UnitPowRatio x) (nhdsWithin (0 : ℝ) (Set.Icc 0 1))
      (nhds (chapter8UnitPowRatio x 0)) := by
  rw [entry9_ratio_at_zero]
  have hN := entry9_tendsto_unitPow_nhdsWithin hx
  have hD : Filter.Tendsto (fun u : ℝ => (1 : ℂ) + chapter8UnitPow x u)
      (nhdsWithin (0 : ℝ) (Set.Icc 0 1)) (nhds ((1 : ℂ) + 0)) :=
    tendsto_const_nhds.add hN
  have hne : ((1 : ℂ) + 0) ≠ 0 := by norm_num
  have hdiv := Filter.Tendsto.div hN hD hne
  have h0 : (0 : ℂ) / ((1 : ℂ) + 0) = 0 := by norm_num
  rw [h0] at hdiv
  exact hdiv.congr (fun u => rfl)

private lemma entry9_continuousOn_ratio_Icc {x : ℂ} (hx : 0 < x.re) :
    ContinuousOn (chapter8UnitPowRatio x) (Set.Icc 0 1) := by
  intro u hu
  rcases eq_or_lt_of_le hu.1 with h0 | hpos
  · subst h0
    exact entry9_tendsto_ratio_nhdsWithin hx
  · have huIoi : u ∈ Set.Ioi (0 : ℝ) := Set.mem_Ioi.mpr hpos
    have hAt : ContinuousAt (chapter8UnitPowRatio x) u :=
      (entry9_continuousOn_ratio_Ioi hx).continuousAt (isOpen_Ioi.mem_nhds huIoi)
    exact hAt.continuousWithinAt

private lemma entry9_intervalIntegrable {x : ℂ} (hx : 0 < x.re) :
    IntervalIntegrable (chapter8UnitPowRatio x) volume 0 1 :=
  ContinuousOn.intervalIntegrable_of_Icc (by norm_num) (entry9_continuousOn_ratio_Icc hx)

private lemma entry9_re_inv_pos {x : ℂ} (hx : 0 < x.re) : 0 < (1 / x).re := by
  have hxne := entry9_x_ne_zero hx
  rw [one_div, Complex.inv_re]
  exact div_pos hx (Complex.normSq_pos.mpr hxne)

private lemma entry9_re_inv_two_mul_pos {x : ℂ} (hx : 0 < x.re) : 0 < (1 / (2 * x)).re := by
  have hxne := entry9_x_ne_zero hx
  have h2x : (2 * x).re = 2 * x.re := by simp [Complex.mul_re]
  rw [one_div, Complex.inv_re, h2x]
  exact div_pos (by linarith) (Complex.normSq_pos.mpr (mul_ne_zero (by norm_num) hxne))

private lemma entry9_gamma_ne_one_div_two_mul_add {x : ℂ} (hx : 0 < x.re) :
    Complex.Gamma (1 / (2 * x) + 1) ≠ 0 := by
  apply Complex.Gamma_ne_zero_of_re_pos
  rw [Complex.add_re, Complex.one_re]
  have h := entry9_re_inv_two_mul_pos hx
  linarith

private lemma entry9_gamma_ne_one_div_add {x : ℂ} (hx : 0 < x.re) :
    Complex.Gamma (1 / x + 1) ≠ 0 := by
  apply Complex.Gamma_ne_zero_of_re_pos
  rw [Complex.add_re, Complex.one_re]
  have h := entry9_re_inv_pos hx
  linarith

private lemma entry9_two_mul_lhs {x : ℂ} (hx : 0 < x.re) :
    2 * (1 / (2 * x) + 1 / 2) = 1 / x + 1 := by
  have hxne := entry9_x_ne_zero hx
  field_simp

private lemma entry9_two_mul_rhs (x : ℂ) :
    1 / (2 * x) + 1 / 2 + 1 / 2 = 1 / (2 * x) + 1 := by
  ring

private lemma entry9_two_mul_side {x : ℂ} (hx : 0 < x.re) :
    ∀ m : ℕ, 2 * (1 / (2 * x) + 1 / 2) ≠ -((m : ℕ) : ℂ) := by
  intro m hm
  have h2s := entry9_two_mul_lhs hx
  rw [h2s] at hm
  have hpos : (0 : ℝ) < (1 / x + 1).re := by
    rw [Complex.add_re, Complex.one_re]
    have h := entry9_re_inv_pos hx
    linarith
  have hre := congrArg Complex.re hm
  rw [Complex.neg_re, Complex.natCast_re] at hre
  have hm0 : (0 : ℝ) ≤ ((m : ℕ) : ℝ) := Nat.cast_nonneg m
  linarith

private lemma entry9_unitPow_add {x y : ℂ} {u : ℝ} (hu : u ≠ 0) :
    chapter8UnitPow (x + y) u = chapter8UnitPow x u * chapter8UnitPow y u := by
  unfold chapter8UnitPow
  rw [ite_eq_right hu, ite_eq_right hu, ite_eq_right hu, add_mul, Complex.exp_add]

private lemma entry9_unitPow_nat_mul {x : ℂ} {u : ℝ} (hu : u ≠ 0) (k : ℕ) :
    chapter8UnitPow ((k : ℂ) * x) u = (chapter8UnitPow x u) ^ k := by
  induction k with
  | zero =>
    simp only [Nat.cast_zero, zero_mul, pow_zero]
    unfold chapter8UnitPow
    rw [ite_eq_right hu, zero_mul, Complex.exp_zero]
  | succ n ih =>
    have hcast : ((((n + 1 : ℕ)) : ℂ) * x) = (n : ℂ) * x + x := by push_cast; ring
    rw [hcast, entry9_unitPow_add hu, ih, pow_succ]

private lemma entry9_unitPow_succ_mul {x : ℂ} {u : ℝ} (hu : u ≠ 0) (k : ℕ) :
    chapter8UnitPow (((k : ℂ) + 1) * x) u = (chapter8UnitPow x u) ^ (k + 1) := by
  have hcast : (((k : ℂ) + 1) * x) = x + (k : ℂ) * x := by ring
  rw [hcast, entry9_unitPow_add hu, entry9_unitPow_nat_mul hu, pow_succ']

private lemma entry9_geom_summand {x : ℂ} {u : ℝ} (k : ℕ) :
    (-chapter8UnitPow x u) ^ k * chapter8UnitPow x u =
      (-1) ^ k * chapter8UnitPow (((k : ℂ) + 1) * x) u := by
  by_cases hu : u = 0
  · subst hu
    have h0 : ∀ w : ℂ, chapter8UnitPow w 0 = 0 := by
      intro w
      unfold chapter8UnitPow
      simp
    rw [h0, h0]
    simp
  · rw [entry9_unitPow_succ_mul hu k, neg_pow, pow_succ]
    ring

private lemma entry9_geom_partial {x : ℂ} (hx : 0 < x.re) {u : ℝ} (hu : u ∈ Set.Icc 0 1)
    (N : ℕ) :
    chapter8UnitPowRatio x u
      = (∑ k ∈ range N, (-1) ^ k * chapter8UnitPow (((k : ℂ) + 1) * x) u)
        + (-1) ^ N * chapter8UnitPow (((N : ℂ) + 1) * x) u / (1 + chapter8UnitPow x u) := by
  have h1z : (1 : ℂ) + chapter8UnitPow x u ≠ 0 := entry9_one_add_unitPow_ne_Icc hx hu
  have hgeom := geom_sum_mul (-chapter8UnitPow x u) N
  have hsum : (∑ k ∈ range N, (-1) ^ k * chapter8UnitPow (((k : ℂ) + 1) * x) u)
      = (∑ k ∈ range N, (-chapter8UnitPow x u) ^ k) * chapter8UnitPow x u := by
    rw [Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro k _
    rw [entry9_geom_summand]
  have hS : (∑ k ∈ range N, (-chapter8UnitPow x u) ^ k) * (1 + chapter8UnitPow x u)
      = 1 - (-chapter8UnitPow x u) ^ N := by
    linear_combination -hgeom
  have key : chapter8UnitPow x u
      = (∑ k ∈ range N, (-chapter8UnitPow x u) ^ k) * chapter8UnitPow x u
          * (1 + chapter8UnitPow x u)
        + (-chapter8UnitPow x u) ^ N * chapter8UnitPow x u := by
    linear_combination (-chapter8UnitPow x u) * hS
  have hdiv : chapter8UnitPow x u / (1 + chapter8UnitPow x u)
      = (∑ k ∈ range N, (-chapter8UnitPow x u) ^ k) * chapter8UnitPow x u
        + (-chapter8UnitPow x u) ^ N * chapter8UnitPow x u / (1 + chapter8UnitPow x u) := by
    have hdiv2 : chapter8UnitPow x u / (1 + chapter8UnitPow x u)
        = ((∑ k ∈ range N, (-chapter8UnitPow x u) ^ k) * chapter8UnitPow x u
          * (1 + chapter8UnitPow x u)
          + (-chapter8UnitPow x u) ^ N * chapter8UnitPow x u) / (1 + chapter8UnitPow x u) := by
      exact congrArg (· / (1 + chapter8UnitPow x u)) key
    rw [hdiv2, add_div, mul_div_cancel_right₀ _ h1z]
  unfold chapter8UnitPowRatio
  rw [hsum, hdiv, entry9_geom_summand N]

private lemma entry9_re_succ_mul_pos {x : ℂ} (hx : 0 < x.re) (k : ℕ) :
    0 < ((((k : ℂ) + 1) * x)).re := by
  have h1 : ((((k : ℂ) + 1) * x)) = (((((k : ℝ) + 1 : ℝ)) : ℂ) * x) := by
    rw [Complex.ofReal_add, Complex.ofReal_one, Complex.ofReal_natCast]
  rw [h1, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero]
  exact mul_pos (by have hk : (0 : ℝ) ≤ (k : ℝ) := Nat.cast_nonneg k; linarith) hx

private lemma entry9_ofReal_log_hasDerivAt {u : ℝ} (hu : 0 < u) :
    HasDerivAt (fun v : ℝ => ((Real.log v : ℝ) : ℂ)) (((u⁻¹ : ℝ)) : ℂ) u := by
  have h1 : HasFDerivAt Real.log (ContinuousLinearMap.toSpanSingleton ℝ (u⁻¹ : ℝ)) u :=
    (Real.hasDerivAt_log (ne_of_gt hu)).hasFDerivAt
  have h2 : HasFDerivAt (⇑Complex.ofRealCLM) Complex.ofRealCLM (Real.log u) :=
    Complex.ofRealCLM.hasFDerivAt
  have h3 := HasFDerivAt.comp u h2 h1
  have h4 := h3.hasDerivAt
  have hder : (Complex.ofRealCLM ∘SL ContinuousLinearMap.toSpanSingleton ℝ (u⁻¹ : ℝ)) 1
      = (((u⁻¹ : ℝ)) : ℂ) := by simp
  rw [hder] at h4
  exact h4.congr_of_eventuallyEq (Eventually.of_forall fun v => rfl)

private lemma entry9_hasDerivAt_unitPow_succ {y : ℂ} (hy : 0 < y.re) {u : ℝ} (hu : 0 < u) :
    HasDerivAt (fun v : ℝ => chapter8UnitPow (y + 1) v / (y + 1))
      (chapter8UnitPow y u) u := by
  have hu0 : u ≠ 0 := ne_of_gt hu
  have hy1 : y + 1 ≠ 0 := by
    intro hcon
    have hre : y.re + 1 = 0 := by
      have h := congrArg Complex.re hcon
      simpa using h
    linarith
  have hlog := entry9_ofReal_log_hasDerivAt hu
  have hmul : HasDerivAt (fun v : ℝ => (y + 1) * ((Real.log v : ℝ) : ℂ))
      ((y + 1) * (((u⁻¹ : ℝ)) : ℂ)) u :=
    hlog.const_mul (y + 1)
  have hexp : HasDerivAt (fun v : ℝ => Complex.exp ((y + 1) * ((Real.log v : ℝ) : ℂ)))
      (Complex.exp ((y + 1) * ((Real.log u : ℝ) : ℂ)) * ((y + 1) * (((u⁻¹ : ℝ)) : ℂ))) u :=
    HasDerivAt.cexp hmul
  have hdiv : HasDerivAt
      (fun v : ℝ => Complex.exp ((y + 1) * ((Real.log v : ℝ) : ℂ)) / (y + 1))
      (Complex.exp ((y + 1) * ((Real.log u : ℝ) : ℂ)) *
        ((y + 1) * (((u⁻¹ : ℝ)) : ℂ)) / (y + 1)) u :=
    hexp.div_const (y + 1)
  have hexp_log : Complex.exp (((Real.log u : ℝ)) : ℂ) = ((u : ℝ) : ℂ) := by
    rw [← Complex.ofReal_exp, Real.exp_log hu]
  have hder : Complex.exp ((y + 1) * ((Real.log u : ℝ) : ℂ)) *
        ((y + 1) * (((u⁻¹ : ℝ)) : ℂ)) / (y + 1)
      = chapter8UnitPow y u := by
    have e1 : ((y + 1 : ℂ)) * (((Real.log u : ℝ)) : ℂ)
        = y * (((Real.log u : ℝ)) : ℂ) + (((Real.log u : ℝ)) : ℂ) := by ring
    have huc : (((u : ℝ)) : ℂ) * (((u⁻¹ : ℝ)) : ℂ) = 1 := by
      rw [← Complex.ofReal_mul, mul_inv_cancel₀ hu0, Complex.ofReal_one]
    have hcancel : ((y + 1 : ℂ)) * (((u⁻¹ : ℝ)) : ℂ) / (y + 1) = (((u⁻¹ : ℝ)) : ℂ) := by
      rw [div_eq_iff hy1]
      ring
    have step1 : Complex.exp ((y + 1) * (((Real.log u : ℝ)) : ℂ))
          * ((y + 1) * (((u⁻¹ : ℝ)) : ℂ)) / (y + 1)
        = Complex.exp ((y + 1) * (((Real.log u : ℝ)) : ℂ)) * (((u⁻¹ : ℝ)) : ℂ) := by
      calc Complex.exp ((y + 1) * (((Real.log u : ℝ)) : ℂ))
              * ((y + 1) * (((u⁻¹ : ℝ)) : ℂ)) / (y + 1)
          = Complex.exp ((y + 1) * (((Real.log u : ℝ)) : ℂ))
              * ((((y + 1)) * (((u⁻¹ : ℝ)) : ℂ)) / (y + 1)) := by ring
        _ = Complex.exp ((y + 1) * (((Real.log u : ℝ)) : ℂ)) * (((u⁻¹ : ℝ)) : ℂ) := by
          rw [hcancel]
    rw [step1, e1, Complex.exp_add, hexp_log, mul_assoc, huc, mul_one]
    unfold chapter8UnitPow
    rw [ite_eq_right hu0]
  have hdiv2 : HasDerivAt (fun v : ℝ => Complex.exp ((y + 1) * ((Real.log v : ℝ) : ℂ)) / (y + 1))
      (chapter8UnitPow y u) u :=
    hder ▸ hdiv
  have hdiv3 : HasDerivAt (fun v : ℝ => chapter8UnitPow (y + 1) v / (y + 1))
      (chapter8UnitPow y u) u := by
    apply hdiv2.congr_of_eventuallyEq
    filter_upwards [eventually_ne_nhds hu0] with v hv
    unfold chapter8UnitPow
    rw [ite_eq_right hv]
  exact hdiv3

private lemma entry9_continuousOn_unitPow_Icc {y : ℂ} (hy : 0 < y.re) :
    ContinuousOn (chapter8UnitPow y) (Set.Icc 0 1) := by
  intro u hu
  rcases eq_or_lt_of_le hu.1 with h0 | hpos
  · subst h0
    have h0v : chapter8UnitPow y 0 = 0 := by
      unfold chapter8UnitPow
      simp
    unfold ContinuousWithinAt
    rw [h0v]
    exact entry9_tendsto_unitPow_nhdsWithin hy
  · have huIoi : u ∈ Set.Ioi (0 : ℝ) := Set.mem_Ioi.mpr hpos
    have hAt : ContinuousAt (chapter8UnitPow y) u :=
      (entry9_continuousOn_unitPow_Ioi (x := y)).continuousAt (isOpen_Ioi.mem_nhds huIoi)
    exact hAt.continuousWithinAt

private lemma entry9_integral_unitPow {y : ℂ} (hy : 0 < y.re) :
    ∫ v in (0 : ℝ)..1, chapter8UnitPow y v = 1 / (y + 1) := by
  have hy1 : y + 1 ≠ 0 := by
    intro hcon
    have hre : y.re + 1 = 0 := by
      have h := congrArg Complex.re hcon
      simpa using h
    linarith
  have hy1re : 0 < (y + 1).re := by
    rw [Complex.add_re, Complex.one_re]
    linarith
  have hF : ContinuousOn (fun v : ℝ => chapter8UnitPow (y + 1) v / (y + 1)) (Set.Icc 0 1) :=
    (entry9_continuousOn_unitPow_Icc hy1re).div_const _
  have hint : IntervalIntegrable (chapter8UnitPow y) volume 0 1 :=
    (entry9_continuousOn_unitPow_Icc hy).intervalIntegrable_of_Icc (by norm_num)
  have hderiv : ∀ v ∈ Set.Ioo (0 : ℝ) 1,
      HasDerivAt (fun w : ℝ => chapter8UnitPow (y + 1) w / (y + 1)) (chapter8UnitPow y v) v := by
    intro v hv
    exact entry9_hasDerivAt_unitPow_succ hy (Set.mem_Ioo.mp hv).1
  have hftc := intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le
    (show (0 : ℝ) ≤ 1 by norm_num) hF hderiv hint
  have hF1 : chapter8UnitPow (y + 1) 1 / (y + 1) = 1 / (y + 1) := by
    unfold chapter8UnitPow
    rw [ite_eq_right one_ne_zero, Real.log_one, Complex.ofReal_zero, mul_zero, Complex.exp_zero]
  have hF0 : chapter8UnitPow (y + 1) 0 / (y + 1) = 0 := by
    unfold chapter8UnitPow
    rw [ite_eq_left rfl, zero_div]
  rw [hF1, hF0, sub_zero] at hftc
  exact hftc

private lemma entry9_integrableOn_remainder_Ioc {x : ℂ} (hx : 0 < x.re) (N : ℕ) :
    MeasureTheory.IntegrableOn
      (fun v => (-1) ^ N * chapter8UnitPow (((N : ℂ) + 1) * x) v / (1 + chapter8UnitPow x v))
      (Set.Ioc 0 1) volume := by
  have hnum : ContinuousOn (fun v : ℝ => (-1 : ℂ) ^ N * chapter8UnitPow (((N : ℂ) + 1) * x) v)
      (Set.Icc 0 1) :=
    continuousOn_const.mul (entry9_continuousOn_unitPow_Icc (entry9_re_succ_mul_pos hx N))
  have hden : ContinuousOn (fun v : ℝ => (1 : ℂ) + chapter8UnitPow x v) (Set.Icc 0 1) :=
    continuousOn_const.add (entry9_continuousOn_unitPow_Icc hx)
  have hdiv : ContinuousOn
      (fun v : ℝ => (-1) ^ N * chapter8UnitPow (((N : ℂ) + 1) * x) v / (1 + chapter8UnitPow x v))
      (Set.Icc 0 1) :=
    hnum.div hden (fun v hv => entry9_one_add_unitPow_ne_Icc hx hv)
  exact hdiv.integrableOn_Icc.mono_set Set.Ioc_subset_Icc_self

private lemma entry9_partial_integral {x : ℂ} (hx : 0 < x.re) (N : ℕ) :
    ∫ v in (0 : ℝ)..1, chapter8UnitPowRatio x v
      = (∑ k ∈ range N, (-1) ^ k * (1 / ((((k : ℂ) + 1) * x) + 1)))
        + ∫ v in (0 : ℝ)..1,
            ((-1) ^ N * chapter8UnitPow (((N : ℂ) + 1) * x) v / (1 + chapter8UnitPow x v)) := by
  have h01 : (0 : ℝ) ≤ 1 := by norm_num
  have hEq : Set.EqOn (chapter8UnitPowRatio x)
      (fun v => (∑ k ∈ range N, (-1) ^ k * chapter8UnitPow (((k : ℂ) + 1) * x) v)
        + ((-1) ^ N * chapter8UnitPow (((N : ℂ) + 1) * x) v / (1 + chapter8UnitPow x v)))
      (Set.Ioc 0 1) := by
    intro v hv
    exact entry9_geom_partial hx ⟨le_of_lt hv.1, hv.2⟩ N
  have hsum_on : ∀ k ∈ range N, MeasureTheory.IntegrableOn
      (fun v => (-1 : ℂ) ^ k * chapter8UnitPow (((k : ℂ) + 1) * x) v) (Set.Ioc 0 1) volume := by
    intro k _
    have hnum : ContinuousOn (fun v : ℝ => (-1 : ℂ) ^ k * chapter8UnitPow (((k : ℂ) + 1) * x) v)
        (Set.Icc 0 1) :=
      continuousOn_const.mul (entry9_continuousOn_unitPow_Icc (entry9_re_succ_mul_pos hx k))
    exact hnum.integrableOn_Icc.mono_set Set.Ioc_subset_Icc_self
  have hRI : MeasureTheory.IntegrableOn
      (fun v => (-1) ^ N * chapter8UnitPow (((N : ℂ) + 1) * x) v / (1 + chapter8UnitPow x v))
      (Set.Ioc 0 1) volume :=
    entry9_integrableOn_remainder_Ioc hx N
  have hsumI : MeasureTheory.Integrable
      (fun v => ∑ k ∈ range N, (-1 : ℂ) ^ k * chapter8UnitPow (((k : ℂ) + 1) * x) v)
      (volume.restrict (Set.Ioc 0 1)) :=
    MeasureTheory.integrable_finsetSum _ (fun k hk => hsum_on k hk)
  have hterm : ∀ k ∈ range N,
      (∫ v in Set.Ioc (0 : ℝ) 1, (-1 : ℂ) ^ k * chapter8UnitPow (((k : ℂ) + 1) * x) v ∂volume)
        = (-1) ^ k * (1 / ((((k : ℂ) + 1) * x) + 1)) := by
    intro k _
    rw [MeasureTheory.integral_const_mul, ← intervalIntegral.integral_of_le h01,
      entry9_integral_unitPow (entry9_re_succ_mul_pos hx k)]
  have hval : (∫ v in Set.Ioc (0 : ℝ) 1,
        (∑ k ∈ range N, (-1 : ℂ) ^ k * chapter8UnitPow (((k : ℂ) + 1) * x) v) ∂volume)
      = ∑ k ∈ range N, (-1) ^ k * (1 / ((((k : ℂ) + 1) * x) + 1)) := by
    rw [MeasureTheory.integral_finsetSum _ (fun k hk => hsum_on k hk)]
    exact Finset.sum_congr rfl (fun k hk => hterm k hk)
  have e1 : (∫ v in (0 : ℝ)..1, chapter8UnitPowRatio x v)
      = ∫ v in Set.Ioc (0 : ℝ) 1, chapter8UnitPowRatio x v ∂volume :=
    intervalIntegral.integral_of_le h01
  have e2 : (∫ v in (0 : ℝ)..1,
        ((-1) ^ N * chapter8UnitPow (((N : ℂ) + 1) * x) v / (1 + chapter8UnitPow x v)))
      = ∫ v in Set.Ioc (0 : ℝ) 1,
        ((-1) ^ N * chapter8UnitPow (((N : ℂ) + 1) * x) v / (1 + chapter8UnitPow x v)) ∂volume :=
    intervalIntegral.integral_of_le h01
  have haeEq : ∀ᵐ v ∂(volume : Measure ℝ), v ∈ Set.Ioc (0 : ℝ) 1 →
      chapter8UnitPowRatio x v
        = (∑ k ∈ range N, (-1) ^ k * chapter8UnitPow (((k : ℂ) + 1) * x) v)
          + ((-1) ^ N * chapter8UnitPow (((N : ℂ) + 1) * x) v / (1 + chapter8UnitPow x v)) :=
    Eventually.of_forall fun v hv => hEq hv
  have hcongr := MeasureTheory.setIntegral_congr_ae measurableSet_Ioc haeEq
  rw [e1, e2]
  exact (hcongr.trans (MeasureTheory.integral_add hsumI hRI)).trans (by rw [hval])

private lemma entry9_tendsto_remainder_integral {x : ℂ} (hx : 0 < x.re) :
    Filter.Tendsto
      (fun N : ℕ => ∫ v in (0 : ℝ)..1,
        ((-1) ^ N * chapter8UnitPow (((N : ℂ) + 1) * x) v / (1 + chapter8UnitPow x v)))
      Filter.atTop (nhds 0) := by
  have h01 : (0 : ℝ) ≤ 1 := by norm_num
  have h1c : ∀ᵐ v ∂(volume : Measure ℝ), v ≠ 1 := by
    rw [MeasureTheory.ae_iff]
    have hset : {v : ℝ | ¬ v ≠ 1} = {1} := by
      ext v
      simp
    rw [hset]
    exact Real.volume_singleton
  have hAES : ∀ N : ℕ, AEStronglyMeasurable
      (fun v => (-1 : ℂ) ^ N * chapter8UnitPow (((N : ℂ) + 1) * x) v / (1 + chapter8UnitPow x v))
      (volume.restrict (Set.Ioc 0 1)) := by
    intro N
    have hnum : ContinuousOn (fun v : ℝ => (-1 : ℂ) ^ N * chapter8UnitPow (((N : ℂ) + 1) * x) v)
        (Set.Icc 0 1) :=
      continuousOn_const.mul (entry9_continuousOn_unitPow_Icc (entry9_re_succ_mul_pos hx N))
    have hden : ContinuousOn (fun v : ℝ => (1 : ℂ) + chapter8UnitPow x v) (Set.Icc 0 1) :=
      continuousOn_const.add (entry9_continuousOn_unitPow_Icc hx)
    have hdiv : ContinuousOn
        (fun v : ℝ => (-1 : ℂ) ^ N *
          chapter8UnitPow (((N : ℂ) + 1) * x) v / (1 + chapter8UnitPow x v))
        (Set.Icc 0 1) :=
      hnum.div hden (fun v hv => entry9_one_add_unitPow_ne_Icc hx hv)
    exact (hdiv.mono Set.Ioc_subset_Icc_self).aestronglyMeasurable measurableSet_Ioc
  have hBint : MeasureTheory.Integrable (fun v : ℝ => ‖((1 : ℂ) + chapter8UnitPow x v)⁻¹‖)
      (volume.restrict (Set.Ioc 0 1)) := by
    have hden : ContinuousOn (fun v : ℝ => (1 : ℂ) + chapter8UnitPow x v) (Set.Icc 0 1) :=
      continuousOn_const.add (entry9_continuousOn_unitPow_Icc hx)
    have hBcont : ContinuousOn
        (fun v : ℝ => ‖((1 : ℂ) + chapter8UnitPow x v)⁻¹‖) (Set.Icc 0 1) := by
      have h1 := hden.inv₀ (fun v hv => entry9_one_add_unitPow_ne_Icc hx hv)
      have h2 := h1.norm
      simpa [Pi.inv_apply] using h2
    exact hBcont.integrableOn_Icc.mono_set Set.Ioc_subset_Icc_self
  have hbound : ∀ N : ℕ, ∀ᵐ v ∂(volume.restrict (Set.Ioc (0 : ℝ) 1)),
      ‖(-1 : ℂ) ^ N * chapter8UnitPow (((N : ℂ) + 1) * x) v / (1 + chapter8UnitPow x v)‖
        ≤ ‖((1 : ℂ) + chapter8UnitPow x v)⁻¹‖ := by
    intro N
    rw [MeasureTheory.ae_restrict_iff' measurableSet_Ioc]
    filter_upwards with v hv
    have hv_pos : 0 < v := (Set.mem_Ioc.mp hv).1
    have hv_le1 : v ≤ 1 := (Set.mem_Ioc.mp hv).2
    have hD : (1 : ℂ) + chapter8UnitPow x v ≠ 0 :=
      entry9_one_add_unitPow_ne_Icc hx ⟨le_of_lt hv_pos, hv_le1⟩
    have h1N : ‖(-1 : ℂ) ^ N‖ = 1 := by simp
    have hU1 : ‖chapter8UnitPow (((N : ℂ) + 1) * x) v‖ ≤ 1 := by
      have hnorm : ‖chapter8UnitPow (((N : ℂ) + 1) * x) v‖ = v ^ ((((N : ℝ) + 1) * x.re)) := by
        have hwre : ((((N : ℂ) + 1) * x)).re = (((N : ℝ) + 1) * x.re) := by
          have h1 : ((((N : ℂ) + 1) * x)) = (((((N : ℝ) + 1 : ℝ)) : ℂ) * x) := by
            rw [Complex.ofReal_add, Complex.ofReal_one, Complex.ofReal_natCast]
          rw [h1, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero]
        rw [entry9_norm_unitPow_of_pos hv_pos, hwre]
      rw [hnorm]
      apply Real.rpow_le_one (le_of_lt hv_pos) hv_le1
      apply mul_nonneg _ hx.le
      have hN : (0 : ℝ) ≤ (N : ℝ) := Nat.cast_nonneg N
      linarith
    rw [norm_div, norm_mul, h1N, one_mul, norm_inv, div_eq_mul_inv]
    have hle : ‖chapter8UnitPow (((N : ℂ) + 1) * x) v‖ * ‖(1 : ℂ) + chapter8UnitPow x v‖⁻¹
        ≤ 1 * ‖(1 : ℂ) + chapter8UnitPow x v‖⁻¹ :=
      mul_le_mul_of_nonneg_right hU1 (inv_nonneg.mpr (norm_nonneg _))
    rwa [one_mul] at hle
  have hae : ∀ᵐ v ∂(volume.restrict (Set.Ioc (0 : ℝ) 1)),
      Filter.Tendsto
        (fun N : ℕ => (-1 : ℂ) ^ N *
          chapter8UnitPow (((N : ℂ) + 1) * x) v / (1 + chapter8UnitPow x v))
        Filter.atTop (nhds 0) := by
    rw [MeasureTheory.ae_restrict_iff' measurableSet_Ioc]
    filter_upwards [h1c] with v hv1 hvIoc
    have hv_pos : 0 < v := (Set.mem_Ioc.mp hvIoc).1
    have hv_le1 : v ≤ 1 := (Set.mem_Ioc.mp hvIoc).2
    have hv_lt1 : v < 1 := lt_of_le_of_ne hv_le1 hv1
    have hnorm : ∀ N : ℕ,
        ‖chapter8UnitPow (((N : ℂ) + 1) * x) v‖ = v ^ ((((N : ℝ) + 1) * x.re)) := by
      intro N
      have hwre : ((((N : ℂ) + 1) * x)).re = (((N : ℝ) + 1) * x.re) := by
        have h1 : ((((N : ℂ) + 1) * x)) = (((((N : ℝ) + 1 : ℝ)) : ℂ) * x) := by
          rw [Complex.ofReal_add, Complex.ofReal_one, Complex.ofReal_natCast]
        rw [h1, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero]
      rw [entry9_norm_unitPow_of_pos hv_pos, hwre]
    have hpow : Filter.Tendsto
        (fun N : ℕ => v ^ ((((N : ℝ) + 1) * x.re))) Filter.atTop (nhds 0) := by
      have hvr : v ^ x.re < 1 := Real.rpow_lt_one (le_of_lt hv_pos) hv_lt1 hx
      have hvr0 : 0 ≤ v ^ x.re := Real.rpow_nonneg (le_of_lt hv_pos) _
      have hbase := tendsto_pow_atTop_nhds_zero_of_lt_one hvr0 hvr
      have hshift : Filter.Tendsto (fun N : ℕ => (v ^ x.re) ^ (N + 1)) Filter.atTop (nhds 0) := by
        have hmul := hbase.const_mul (v ^ x.re)
        simpa [pow_succ'] using hmul
      have heq : (fun N : ℕ => v ^ ((((N : ℝ) + 1) * x.re)))
          = (fun N : ℕ => (v ^ x.re) ^ (N + 1)) := by
        funext N
        have hcast : ((((N + 1 : ℕ)) : ℝ)) = (N : ℝ) + 1 := by push_cast; ring
        rw [← hcast, ← Real.rpow_natCast _ (N + 1), ← Real.rpow_mul (le_of_lt hv_pos)]
        congr 1
        ring
      rw [heq]
      exact hshift
    have hDbound : Filter.Tendsto
        (fun N : ℕ => v ^ ((((N : ℝ) + 1) * x.re)) / ‖(1 : ℂ) + chapter8UnitPow x v‖)
        Filter.atTop (nhds 0) := by
      have h2 := hpow.div_const (‖(1 : ℂ) + chapter8UnitPow x v‖)
      rwa [zero_div] at h2
    refine squeeze_zero_norm' (Eventually.of_forall fun N : ℕ => ?_) hDbound
    have h1N : ‖(-1 : ℂ) ^ N‖ = 1 := by simp
    have e : ‖(-1 : ℂ) ^ N * chapter8UnitPow (((N : ℂ) + 1) * x) v / (1 + chapter8UnitPow x v)‖
        = v ^ ((((N : ℝ) + 1) * x.re)) / ‖(1 : ℂ) + chapter8UnitPow x v‖ := by
      rw [norm_div, norm_mul, h1N, one_mul, hnorm N]
    exact le_of_eq e
  have hdct := MeasureTheory.tendsto_integral_of_dominated_convergence
    (F := fun N v => (-1 : ℂ) ^ N *
      chapter8UnitPow (((N : ℂ) + 1) * x) v / (1 + chapter8UnitPow x v))
    (f := fun _ => 0)
    (fun v => ‖((1 : ℂ) + chapter8UnitPow x v)⁻¹‖)
    (μ := volume.restrict (Set.Ioc 0 1))
    hAES hBint hbound hae
  have hgoal : (fun N : ℕ => ∫ v in (0 : ℝ)..1,
        ((-1) ^ N * chapter8UnitPow (((N : ℂ) + 1) * x) v /
          (1 + chapter8UnitPow x v)))
      = (fun N : ℕ => ∫ v in Set.Ioc (0 : ℝ) 1,
        ((-1) ^ N * chapter8UnitPow (((N : ℂ) + 1) * x) v /
          (1 + chapter8UnitPow x v)) ∂volume) := by
    funext N
    exact intervalIntegral.integral_of_le h01
  rw [hgoal]
  simpa using hdct

private lemma entry9_tendsto_partial {x : ℂ} (hx : 0 < x.re) :
    Filter.Tendsto (fun N : ℕ => ∑ k ∈ range N, (-1) ^ k * (1 / ((((k : ℂ) + 1) * x) + 1)))
      Filter.atTop (nhds (∫ v in (0 : ℝ)..1, chapter8UnitPowRatio x v)) := by
  have hrem := entry9_tendsto_remainder_integral hx
  have heq : (fun N : ℕ => ∑ k ∈ range N, (-1) ^ k * (1 / ((((k : ℂ) + 1) * x) + 1)))
      = fun N : ℕ => (∫ v in (0 : ℝ)..1, chapter8UnitPowRatio x v)
        - ∫ v in (0 : ℝ)..1,
          ((-1) ^ N * chapter8UnitPow (((N : ℂ) + 1) * x) v / (1 + chapter8UnitPow x v)) := by
    funext N
    have h := entry9_partial_integral hx N
    rw [h]
    ring
  rw [heq]
  simpa using Filter.Tendsto.sub tendsto_const_nhds hrem

private def entry9RealDigamma (x : ℝ) : ℝ :=
  deriv Real.Gamma x / Real.Gamma x

private theorem entry9_hasDerivAt_logGamma {y : ℝ} (hy : 0 < y) :
    HasDerivAt (Real.log ∘ Real.Gamma) (entry9RealDigamma y) y := by
  have hdiff : DifferentiableAt ℝ Real.Gamma y :=
    Real.differentiableAt_Gamma (fun m => by
      have hm0 : (0 : ℝ) ≤ (m : ℝ) := Nat.cast_nonneg m
      have hlt : -((m : ℝ)) < y := by linarith
      exact ne_of_gt hlt)
  have hne : Real.Gamma y ≠ 0 := (Real.Gamma_pos_of_pos hy).ne'
  exact hdiff.hasDerivAt.log hne

private theorem entry9_realDigamma_add_one {y : ℝ} (hy : 0 < y) :
    entry9RealDigamma (y + 1) = entry9RealDigamma y + 1 / y := by
  have hy_ne : y ≠ 0 := ne_of_gt hy
  have hdiff_y : DifferentiableAt ℝ Real.Gamma y :=
    Real.differentiableAt_Gamma (fun m => by
      have hm0 : (0 : ℝ) ≤ (m : ℝ) := Nat.cast_nonneg m
      have hlt : -((m : ℝ)) < y := by linarith
      exact ne_of_gt hlt)
  have hy1_pos : (0 : ℝ) < y + 1 := by linarith
  have hdiff_y1 : DifferentiableAt ℝ Real.Gamma (y + 1) :=
    Real.differentiableAt_Gamma (fun m => by
      have hm0 : (0 : ℝ) ≤ (m : ℝ) := Nat.cast_nonneg m
      have hlt : -((m : ℝ)) < y + 1 := by linarith
      exact ne_of_gt hlt)
  have h_left : HasDerivAt (fun s => Real.Gamma (s + 1))
      (deriv Real.Gamma (y + 1)) y :=
    HasDerivAt.comp_add_const y 1 hdiff_y1.hasDerivAt
  have h_right : HasDerivAt (fun s => s * Real.Gamma s)
      (1 * Real.Gamma y + y * deriv Real.Gamma y) y :=
    (hasDerivAt_id' y).mul hdiff_y.hasDerivAt
  have heq : (fun s => Real.Gamma (s + 1)) =ᶠ[𝓝 y]
      (fun s => s * Real.Gamma s) := by
    filter_upwards [eventually_ne_nhds hy_ne] with s hs using
      Real.Gamma_add_one hs
  have h_left' : HasDerivAt (fun s => s * Real.Gamma s)
      (deriv Real.Gamma (y + 1)) y :=
    h_left.congr_of_eventuallyEq heq.symm
  have hder_eq : deriv Real.Gamma (y + 1) =
      1 * Real.Gamma y + y * deriv Real.Gamma y :=
    HasDerivAt.unique h_left' h_right
  have hG_y_pos : (0 : ℝ) < Real.Gamma y := Real.Gamma_pos_of_pos hy
  have hG_y_ne : Real.Gamma y ≠ 0 := ne_of_gt hG_y_pos
  have hG_y1_eq : Real.Gamma (y + 1) = y * Real.Gamma y :=
    Real.Gamma_add_one hy_ne
  have hG_y1_ne : Real.Gamma (y + 1) ≠ 0 := by
    rw [hG_y1_eq]
    exact mul_ne_zero hy_ne hG_y_ne
  unfold entry9RealDigamma
  rw [hder_eq, hG_y1_eq]
  field_simp
  ring

private theorem entry9_realDigamma_bounds {y : ℝ} (hy : 0 < y) :
    Real.log y ≤ entry9RealDigamma (y + 1) ∧
      entry9RealDigamma (y + 1) ≤ Real.log (y + 1) := by
  have hy1_pos : (0 : ℝ) < y + 1 := by linarith
  have hy2_pos : (0 : ℝ) < (y + 1) + 1 := by linarith
  have hx_mem : y ∈ Set.Ioi (0 : ℝ) := hy
  have hy1_mem : y + 1 ∈ Set.Ioi (0 : ℝ) := hy1_pos
  have hy2_mem : (y + 1) + 1 ∈ Set.Ioi (0 : ℝ) := hy2_pos
  have hxy1 : y < y + 1 := by linarith
  have hxy2 : y + 1 < (y + 1) + 1 := by linarith
  have hderiv_y1 := entry9_hasDerivAt_logGamma hy1_pos
  have hle1 := Real.convexOn_log_Gamma.slope_le_of_hasDerivAt hx_mem hy1_mem
    hxy1 hderiv_y1
  have hle2 := Real.convexOn_log_Gamma.le_slope_of_hasDerivAt hy1_mem hy2_mem
    hxy2 hderiv_y1
  have hslope1 : slope (Real.log ∘ Real.Gamma) y (y + 1) = Real.log y := by
    rw [slope_def_field]
    have hden : (y + 1) - y = 1 := by ring
    rw [hden, div_one]
    have hG : Real.Gamma (y + 1) = y * Real.Gamma y :=
      Real.Gamma_add_one (ne_of_gt hy)
    have hlog : Real.log (y * Real.Gamma y) =
        Real.log y + Real.log (Real.Gamma y) :=
      Real.log_mul (ne_of_gt hy) (ne_of_gt (Real.Gamma_pos_of_pos hy))
    simp only [Function.comp_apply]
    rw [hG, hlog]
    ring
  have hslope2 : slope (Real.log ∘ Real.Gamma) (y + 1) ((y + 1) + 1) =
      Real.log (y + 1) := by
    rw [slope_def_field]
    have hden : ((y + 1) + 1) - (y + 1) = 1 := by ring
    rw [hden, div_one]
    have hG : Real.Gamma ((y + 1) + 1) = (y + 1) * Real.Gamma (y + 1) :=
      Real.Gamma_add_one (ne_of_gt hy1_pos)
    have hlog : Real.log ((y + 1) * Real.Gamma (y + 1)) =
        Real.log (y + 1) + Real.log (Real.Gamma (y + 1)) :=
      Real.log_mul (ne_of_gt hy1_pos)
        (ne_of_gt (Real.Gamma_pos_of_pos hy1_pos))
    simp only [Function.comp_apply]
    rw [hG, hlog]
    ring
  rw [hslope1] at hle1
  rw [hslope2] at hle2
  exact ⟨hle1, hle2⟩

private theorem entry9_complexDigamma_ofReal {y : ℝ} (hy : 0 < y) :
    Complex.digamma (y : ℂ) = (entry9RealDigamma y : ℂ) := by
  have hC : ∀ m : ℕ, (y : ℂ) ≠ -(m : ℂ) := by
    intro m hm
    have hre := congrArg Complex.re hm
    rw [Complex.ofReal_re] at hre
    rw [Complex.neg_re, Complex.natCast_re] at hre
    have hm0 : (0 : ℝ) ≤ (m : ℝ) := Nat.cast_nonneg m
    linarith
  have hR : ∀ m : ℕ, y ≠ -(m : ℝ) := by
    intro m hm
    have hm0 : (0 : ℝ) ≤ (m : ℝ) := Nat.cast_nonneg m
    linarith
  have hC_diff : DifferentiableAt ℂ Complex.Gamma (y : ℂ) :=
    Complex.differentiableAt_Gamma _ hC
  have hR_diff : DifferentiableAt ℝ Real.Gamma y :=
    Real.differentiableAt_Gamma hR
  have hC_has := hC_diff.hasDerivAt
  have hR_has := hR_diff.hasDerivAt
  have hC_ofReal : HasDerivAt (fun t : ℝ => Complex.Gamma (t : ℂ))
      (deriv Complex.Gamma (y : ℂ)) y :=
    hC_has.comp_ofReal
  have hR_ofReal : HasDerivAt (fun t : ℝ => ((Real.Gamma t : ℝ) : ℂ))
      ((deriv Real.Gamma y : ℝ) : ℂ) y :=
    hR_has.ofReal_comp
  have hfun : (fun t : ℝ => Complex.Gamma (t : ℂ))
      = (fun t : ℝ => ((Real.Gamma t : ℝ) : ℂ)) := by
    funext t
    exact Complex.Gamma_ofReal t
  have hderiv : deriv Complex.Gamma (y : ℂ)
      = ((deriv Real.Gamma y : ℝ) : ℂ) := by
    have hC_rw : HasDerivAt (fun t : ℝ => ((Real.Gamma t : ℝ) : ℂ))
        (deriv Complex.Gamma (y : ℂ)) y := by
      rw [← hfun]
      exact hC_ofReal
    exact HasDerivAt.unique hC_rw hR_ofReal
  rw [Complex.digamma_def, logDeriv_apply]
  unfold entry9RealDigamma
  rw [hderiv, Complex.Gamma_ofReal, Complex.ofReal_div]

private theorem entry9_realDigamma_diff_tendsto {a b : ℝ} (ha : 0 < a)
    (hb : 0 < b) :
    Filter.Tendsto
      (fun M : ℕ => entry9RealDigamma (a + (M : ℝ)) -
        entry9RealDigamma (b + (M : ℝ)))
      Filter.atTop (nhds 0) := by
  have hg : Filter.Tendsto
      (fun M : ℕ => Real.log ((M : ℝ) + a - 1) - Real.log ((M : ℝ) + b))
      Filter.atTop (nhds 0) := by
    have hbase : Filter.Tendsto (fun M : ℕ => (M : ℝ) + b)
        Filter.atTop Filter.atTop :=
      tendsto_atTop_add_const_right _ _ tendsto_natCast_atTop_atTop
    have hlog := (Real.tendsto_log_comp_add_sub_log (a - b - 1)).comp hbase
    refine hlog.congr' (Eventually.of_forall fun M => ?_)
    have e : (M : ℝ) + b + (a - b - 1) = (M : ℝ) + a - 1 := by ring
    simp only [Function.comp_apply, e]
  have hh : Filter.Tendsto
      (fun M : ℕ => Real.log ((M : ℝ) + a) - Real.log ((M : ℝ) + b - 1))
      Filter.atTop (nhds 0) := by
    have hbase : Filter.Tendsto (fun M : ℕ => (M : ℝ) + (b - 1))
        Filter.atTop Filter.atTop :=
      tendsto_atTop_add_const_right _ _ tendsto_natCast_atTop_atTop
    have hlog := (Real.tendsto_log_comp_add_sub_log (a - b + 1)).comp hbase
    refine hlog.congr' (Eventually.of_forall fun M => ?_)
    simp only [Function.comp_apply]
    have e1 : (M : ℝ) + (b - 1) + (a - b + 1) = (M : ℝ) + a := by ring
    have e2 : (M : ℝ) + (b - 1) = (M : ℝ) + b - 1 := by ring
    rw [e1, e2]
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' hg hh ?_ ?_
  · filter_upwards [eventually_ge_atTop 1] with M hM
    have hMR : (1 : ℝ) ≤ (M : ℝ) := by exact_mod_cast hM
    have hy1_pos : (0 : ℝ) < a + (M : ℝ) - 1 := by linarith
    have hy2_pos : (0 : ℝ) < b + (M : ℝ) - 1 := by linarith
    have harg1 : (a + (M : ℝ) - 1) + 1 = a + (M : ℝ) := by ring
    have harg2 : (b + (M : ℝ) - 1) + 1 = b + (M : ℝ) := by ring
    have hb1 := entry9_realDigamma_bounds hy1_pos
    have hb2 := entry9_realDigamma_bounds hy2_pos
    rw [harg1] at hb1
    rw [harg2] at hb2
    have e1 : (M : ℝ) + a - 1 = a + (M : ℝ) - 1 := by ring
    have e2 : (M : ℝ) + b = b + (M : ℝ) := by ring
    rw [e1, e2]
    linarith [hb1.1, hb2.2]
  · filter_upwards [eventually_ge_atTop 1] with M hM
    have hMR : (1 : ℝ) ≤ (M : ℝ) := by exact_mod_cast hM
    have hy1_pos : (0 : ℝ) < a + (M : ℝ) - 1 := by linarith
    have hy2_pos : (0 : ℝ) < b + (M : ℝ) - 1 := by linarith
    have harg1 : (a + (M : ℝ) - 1) + 1 = a + (M : ℝ) := by ring
    have harg2 : (b + (M : ℝ) - 1) + 1 = b + (M : ℝ) := by ring
    have hb1 := entry9_realDigamma_bounds hy1_pos
    have hb2 := entry9_realDigamma_bounds hy2_pos
    rw [harg1] at hb1
    rw [harg2] at hb2
    have e1 : (M : ℝ) + a = a + (M : ℝ) := by ring
    have e2 : (M : ℝ) + b - 1 = b + (M : ℝ) - 1 := by ring
    rw [e1, e2]
    linarith [hb1.2, hb2.1]

private theorem entry9_complexDigamma_diff_ofReal {a b : ℝ} (ha : 0 < a)
    (hb : 0 < b) :
    Filter.Tendsto
      (fun M : ℕ => Complex.digamma (((a + (M : ℝ) : ℝ)) : ℂ) -
        Complex.digamma (((b + (M : ℝ) : ℝ)) : ℂ))
      Filter.atTop (nhds 0) := by
  have h_real := entry9_realDigamma_diff_tendsto ha hb
  have h_ofReal : Filter.Tendsto
      (fun M : ℕ => Complex.ofReal (entry9RealDigamma (a + (M : ℝ)) -
        entry9RealDigamma (b + (M : ℝ))))
      Filter.atTop (nhds (Complex.ofReal 0)) :=
    (Complex.continuous_ofReal.tendsto 0).comp h_real
  rw [Complex.ofReal_zero] at h_ofReal
  refine h_ofReal.congr' (Eventually.of_forall fun M => ?_)
  have haM : 0 < a + (M : ℝ) := by
    have hM0 : (0 : ℝ) ≤ (M : ℝ) := Nat.cast_nonneg M
    linarith
  have hbM : 0 < b + (M : ℝ) := by
    have hM0 : (0 : ℝ) ≤ (M : ℝ) := Nat.cast_nonneg M
    linarith
  change Complex.ofReal (entry9RealDigamma (a + (M : ℝ)) -
      entry9RealDigamma (b + (M : ℝ)))
    = Complex.digamma (((a + (M : ℝ) : ℝ)) : ℂ) -
      Complex.digamma (((b + (M : ℝ) : ℝ)) : ℂ)
  rw [entry9_complexDigamma_ofReal haM, entry9_complexDigamma_ofReal hbM]
  rw [Complex.ofReal_sub]

private theorem entry9_s0_avoid {x : ℂ} (hx : 0 < x.re) :
    ∀ m : ℕ, (1 / (2 * x) + 1 / 2 : ℂ) ≠ -(m : ℂ) := by
  intro m hm
  have hpos : (0 : ℝ) < (1 / (2 * x) + 1 / 2 : ℂ).re := by
    have h := entry9_re_inv_two_mul_pos hx
    have h12 : ((1 / 2 : ℂ)).re = 1 / 2 := by simp
    rw [Complex.add_re, h12]
    linarith
  have hre := congrArg Complex.re hm
  rw [Complex.neg_re, Complex.natCast_re] at hre
  have hm0 : (0 : ℝ) ≤ ((m : ℕ) : ℝ) := Nat.cast_nonneg m
  linarith

private theorem entry9_t0_avoid {x : ℂ} (hx : 0 < x.re) :
    ∀ m : ℕ, (1 / (2 * x) + 1 : ℂ) ≠ -(m : ℂ) := by
  intro m hm
  have hpos : (0 : ℝ) < (1 / (2 * x) + 1 : ℂ).re := by
    have h := entry9_re_inv_two_mul_pos hx
    rw [Complex.add_re, Complex.one_re]
    linarith
  have hre := congrArg Complex.re hm
  rw [Complex.neg_re, Complex.natCast_re] at hre
  have hm0 : (0 : ℝ) ≤ ((m : ℕ) : ℝ) := Nat.cast_nonneg m
  linarith

private theorem entry9_s0_add_ne {x : ℂ} (hx : 0 < x.re) (m : ℕ) :
    (1 / (2 * x) + 1 / 2 : ℂ) + (m : ℂ) ≠ 0 := by
  intro hcon
  have hpos : (0 : ℝ) < ((1 / (2 * x) + 1 / 2 : ℂ) + (m : ℂ)).re := by
    have h := entry9_re_inv_two_mul_pos hx
    have h12 : ((1 / 2 : ℂ)).re = 1 / 2 := by simp
    have hm0 : (0 : ℝ) ≤ ((m : ℕ) : ℝ) := Nat.cast_nonneg m
    rw [Complex.add_re, Complex.add_re, h12, Complex.natCast_re]
    linarith
  rw [hcon] at hpos
  simp at hpos

private theorem entry9_t0_add_ne {x : ℂ} (hx : 0 < x.re) (m : ℕ) :
    (1 / (2 * x) + 1 : ℂ) + (m : ℂ) ≠ 0 := by
  intro hcon
  have hpos : (0 : ℝ) < ((1 / (2 * x) + 1 : ℂ) + (m : ℂ)).re := by
    have h := entry9_re_inv_two_mul_pos hx
    have hm0 : (0 : ℝ) ≤ ((m : ℕ) : ℝ) := Nat.cast_nonneg m
    rw [Complex.add_re, Complex.add_re, Complex.one_re,
      Complex.natCast_re]
    linarith
  rw [hcon] at hpos
  simp at hpos

private theorem entry9_succ_mul_add_ne {x : ℂ} (hx : 0 < x.re) (k : ℕ) :
    (((k : ℂ) + 1) * x + 1 : ℂ) ≠ 0 := by
  intro hcon
  have hpos : (0 : ℝ) < ((((k : ℂ) + 1) * x + 1 : ℂ)).re := by
    have h1 := entry9_re_succ_mul_pos hx k
    rw [Complex.add_re, Complex.one_re]
    linarith
  rw [hcon] at hpos
  simp at hpos

private theorem entry9_even_denom {x : ℂ} (hx : 0 < x.re) (m : ℕ) :
    ((((2 * m : ℕ)) : ℂ) + 1) * x + 1
      = 2 * x * ((1 / (2 * x) + 1 / 2 : ℂ) + (m : ℂ)) := by
  have hxne := entry9_x_ne_zero hx
  have h2x : (2 : ℂ) * x ≠ 0 := mul_ne_zero (by norm_num) hxne
  have hcast : ((((2 * m : ℕ)) : ℂ)) = 2 * (m : ℂ) := by push_cast; ring
  rw [hcast]
  field_simp
  ring

private theorem entry9_odd_denom {x : ℂ} (hx : 0 < x.re) (m : ℕ) :
    ((((2 * m + 1 : ℕ)) : ℂ) + 1) * x + 1
      = 2 * x * ((1 / (2 * x) + 1 : ℂ) + (m : ℂ)) := by
  have hxne := entry9_x_ne_zero hx
  have h2x : (2 : ℂ) * x ≠ 0 := mul_ne_zero (by norm_num) hxne
  have hcast : ((((2 * m + 1 : ℕ)) : ℂ)) = 2 * (m : ℂ) + 1 := by
    push_cast
    ring
  rw [hcast]
  field_simp
  ring

private theorem entry9_even_pow (m : ℕ) : (-1 : ℂ) ^ (2 * m) = 1 := by
  rw [pow_mul]
  simp

private theorem entry9_odd_pow (m : ℕ) : (-1 : ℂ) ^ (2 * m + 1) = -1 := by
  rw [pow_succ, entry9_even_pow, one_mul]

private theorem entry9_even_term {x : ℂ} (hx : 0 < x.re) (m : ℕ) :
    x * ((-1 : ℂ) ^ (2 * m) *
        (1 / (((((2 * m : ℕ)) : ℂ) + 1) * x + 1)))
      = 1 / (2 * ((1 / (2 * x) + 1 / 2 : ℂ) + (m : ℂ))) := by
  have hxne := entry9_x_ne_zero hx
  have hs0 := entry9_s0_add_ne hx m
  have hD := entry9_succ_mul_add_ne hx (2 * m)
  rw [entry9_even_pow, one_mul, entry9_even_denom hx m]
  have h2s : (2 : ℂ) * ((1 / (2 * x) + 1 / 2 : ℂ) + (m : ℂ)) ≠ 0 :=
    mul_ne_zero (by norm_num) hs0
  field_simp

private theorem entry9_odd_term {x : ℂ} (hx : 0 < x.re) (m : ℕ) :
    x * ((-1 : ℂ) ^ (2 * m + 1) *
        (1 / (((((2 * m + 1 : ℕ)) : ℂ) + 1) * x + 1)))
      = -(1 / (2 * ((1 / (2 * x) + 1 : ℂ) + (m : ℂ)))) := by
  have hxne := entry9_x_ne_zero hx
  have ht0 := entry9_t0_add_ne hx m
  have hD := entry9_succ_mul_add_ne hx (2 * m + 1)
  rw [entry9_odd_pow, entry9_odd_denom hx m]
  have h2t : (2 : ℂ) * ((1 / (2 * x) + 1 : ℂ) + (m : ℂ)) ≠ 0 :=
    mul_ne_zero (by norm_num) ht0
  field_simp

private theorem entry9_paired_sum {x : ℂ} (hx : 0 < x.re) (M : ℕ) :
    x * ∑ k ∈ range (2 * M),
          ((-1 : ℂ) ^ k * (1 / (((((k : ℕ)) : ℂ) + 1) * x + 1)))
      = ∑ m ∈ range M,
        (1 / (2 * ((1 / (2 * x) + 1 / 2 : ℂ) + (m : ℂ))) -
          1 / (2 * ((1 / (2 * x) + 1 : ℂ) + (m : ℂ)))) := by
  induction M with
  | zero => simp
  | succ M ih =>
    have h2S : 2 * (M + 1) = (2 * M + 1) + 1 := by ring
    rw [h2S, Finset.sum_range_succ, Finset.sum_range_succ]
    rw [Finset.sum_range_succ]
    rw [mul_add, mul_add, ih]
    have he := entry9_even_term hx M
    have ho := entry9_odd_term hx M
    rw [he, ho]
    ring

private theorem entry9_paired_eq_digamma {x : ℂ} (hx : 0 < x.re) (M : ℕ) :
    x * ∑ k ∈ range (2 * M),
          ((-1 : ℂ) ^ k * (1 / (((((k : ℕ)) : ℂ) + 1) * x + 1)))
      = (1 / 2 : ℂ) *
        ((Complex.digamma ((1 / (2 * x) + 1 / 2 : ℂ) + (M : ℂ)) -
          Complex.digamma ((1 / (2 * x) + 1 : ℂ) + (M : ℂ))) -
          (Complex.digamma (1 / (2 * x) + 1 / 2 : ℂ) -
            Complex.digamma (1 / (2 * x) + 1 : ℂ))) := by
  have hpair := entry9_paired_sum hx M
  have hs0 := entry9_s0_avoid hx
  have ht0 := entry9_t0_avoid hx
  have hdig_s :=
    Complex.digamma_apply_add_nat (s := (1 / (2 * x) + 1 / 2 : ℂ)) hs0 M
  have hdig_t :=
    Complex.digamma_apply_add_nat (s := (1 / (2 * x) + 1 : ℂ)) ht0 M
  have h12 : ∀ A : ℂ, A ≠ 0 → 1 / (2 * A) = (1 / 2 : ℂ) * A⁻¹ := by
    intro A hA
    field_simp
  have hsum : ∑ m ∈ range M,
        (1 / (2 * ((1 / (2 * x) + 1 / 2 : ℂ) + (m : ℂ))) -
          1 / (2 * ((1 / (2 * x) + 1 : ℂ) + (m : ℂ))))
      = (1 / 2 : ℂ) *
        (∑ m ∈ range M,
          (((1 / (2 * x) + 1 / 2 : ℂ) + (m : ℂ))⁻¹ -
            (((1 / (2 * x) + 1 : ℂ) + (m : ℂ))⁻¹))) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro m _
    rw [h12 _ (entry9_s0_add_ne hx m), h12 _ (entry9_t0_add_ne hx m)]
    ring
  have hsub : ∑ m ∈ range M,
        (((1 / (2 * x) + 1 / 2 : ℂ) + (m : ℂ))⁻¹ -
          (((1 / (2 * x) + 1 : ℂ) + (m : ℂ))⁻¹))
      = (∑ m ∈ range M,
          (((1 / (2 * x) + 1 / 2 : ℂ) + (m : ℂ))⁻¹)) -
        ∑ m ∈ range M, (((1 / (2 * x) + 1 : ℂ) + (m : ℂ))⁻¹) :=
    Finset.sum_sub_distrib _ _
  have hs_eq : ∑ m ∈ range M,
        (((1 / (2 * x) + 1 / 2 : ℂ) + (m : ℂ))⁻¹)
      = Complex.digamma ((1 / (2 * x) + 1 / 2 : ℂ) + (M : ℂ)) -
        Complex.digamma (1 / (2 * x) + 1 / 2 : ℂ) := by
    linear_combination -hdig_s
  have ht_eq : ∑ m ∈ range M,
        (((1 / (2 * x) + 1 : ℂ) + (m : ℂ))⁻¹)
      = Complex.digamma ((1 / (2 * x) + 1 : ℂ) + (M : ℂ)) -
        Complex.digamma (1 / (2 * x) + 1 : ℂ) := by
    linear_combination -hdig_t
  rw [hpair, hsum, hsub, hs_eq, ht_eq]
  ring

private theorem entry9_real_D_tendsto {xr : ℝ} (hxr : 0 < xr) :
    Filter.Tendsto
      (fun M : ℕ =>
        Complex.digamma ((1 / (2 * (xr : ℂ)) + 1 / 2 : ℂ) + (M : ℂ)) -
          Complex.digamma ((1 / (2 * (xr : ℂ)) + 1 : ℂ) + (M : ℂ)))
      Filter.atTop (nhds 0) := by
  have hs0R : (0 : ℝ) < 1 / (2 * xr) + 1 / 2 := by
    have h2x : (0 : ℝ) < 2 * xr := by linarith
    have hpos : (0 : ℝ) < 1 / (2 * xr) := by positivity
    linarith
  have ht0R : (0 : ℝ) < 1 / (2 * xr) + 1 := by
    have h2x : (0 : ℝ) < 2 * xr := by linarith
    have hpos : (0 : ℝ) < 1 / (2 * xr) := by positivity
    linarith
  have hdiff := entry9_complexDigamma_diff_ofReal hs0R ht0R
  have hs0C : (1 / (2 * (xr : ℂ)) + 1 / 2 : ℂ)
      = ((1 / (2 * xr) + 1 / 2 : ℝ) : ℂ) := by
    push_cast
    ring
  have ht0C : (1 / (2 * (xr : ℂ)) + 1 : ℂ)
      = ((1 / (2 * xr) + 1 : ℝ) : ℂ) := by
    push_cast
    ring
  refine hdiff.congr' (Eventually.of_forall fun M => ?_)
  have hM : ((M : ℕ) : ℂ) = (((M : ℝ)) : ℂ) := by
    rw [Complex.ofReal_natCast]
  change Complex.digamma (((1 / (2 * xr) + 1 / 2 + (M : ℝ) : ℝ)) : ℂ) -
      Complex.digamma (((1 / (2 * xr) + 1 + (M : ℝ) : ℝ)) : ℂ)
    = Complex.digamma ((1 / (2 * (xr : ℂ)) + 1 / 2 : ℂ) + (M : ℂ)) -
      Complex.digamma ((1 / (2 * (xr : ℂ)) + 1 : ℂ) + (M : ℂ))
  rw [hs0C, ht0C, hM, ← Complex.ofReal_add, ← Complex.ofReal_add]

private theorem entry9_tendsto_two_mul :
    Filter.Tendsto (fun M : ℕ => 2 * M) Filter.atTop Filter.atTop := by
  rw [tendsto_atTop_atTop]
  intro N
  use N
  intro M hM
  calc N ≤ M := hM
    _ ≤ 2 * M := by
      rw [two_mul]
      exact Nat.le_add_right M M

private theorem entry9_real_hkey {xr : ℝ} (hxr : 0 < xr) :
    (1 / 2 : ℂ) *
        (Complex.digamma (1 / (2 * (xr : ℂ)) + 1) -
          Complex.digamma (1 / (2 * (xr : ℂ)) + 1 / 2))
      = (xr : ℂ) * ∫ u in (0 : ℝ)..1,
        chapter8UnitPowRatio (xr : ℂ) u := by
  have hx : (0 : ℝ) < ((xr : ℂ)).re := by
    rw [Complex.ofReal_re]
    exact hxr
  have hlim := entry9_tendsto_partial hx
  have hxlim : Filter.Tendsto
      (fun N : ℕ => (xr : ℂ) * ∑ k ∈ range N,
        ((-1 : ℂ) ^ k * (1 / (((((k : ℕ)) : ℂ) + 1) * (xr : ℂ) + 1))))
      Filter.atTop
      (nhds ((xr : ℂ) * ∫ u in (0 : ℝ)..1,
        chapter8UnitPowRatio (xr : ℂ) u)) :=
    hlim.const_mul (xr : ℂ)
  have hx_even : Filter.Tendsto
      (fun M : ℕ => (xr : ℂ) * ∑ k ∈ range (2 * M),
        ((-1 : ℂ) ^ k * (1 / (((((k : ℕ)) : ℂ) + 1) * (xr : ℂ) + 1))))
      Filter.atTop
      (nhds ((xr : ℂ) * ∫ u in (0 : ℝ)..1,
        chapter8UnitPowRatio (xr : ℂ) u)) :=
    hxlim.comp entry9_tendsto_two_mul
  have hD := entry9_real_D_tendsto hxr
  have hD0 : (Complex.digamma ((1 / (2 * (xr : ℂ)) + 1 / 2 : ℂ)) -
      Complex.digamma ((1 / (2 * (xr : ℂ)) + 1 : ℂ)))
      = Complex.digamma (1 / (2 * (xr : ℂ)) + 1 / 2) -
        Complex.digamma (1 / (2 * (xr : ℂ)) + 1) := rfl
  have htarget : Filter.Tendsto
      (fun M : ℕ => (xr : ℂ) * ∑ k ∈ range (2 * M),
        ((-1 : ℂ) ^ k * (1 / (((((k : ℕ)) : ℂ) + 1) * (xr : ℂ) + 1))))
      Filter.atTop
      (nhds ((1 / 2 : ℂ) *
        (Complex.digamma (1 / (2 * (xr : ℂ)) + 1) -
          Complex.digamma (1 / (2 * (xr : ℂ)) + 1 / 2)))) := by
    have hsub : Filter.Tendsto
        (fun M : ℕ =>
          (Complex.digamma ((1 / (2 * (xr : ℂ)) + 1 / 2 : ℂ) + (M : ℂ)) -
            Complex.digamma ((1 / (2 * (xr : ℂ)) + 1 : ℂ) + (M : ℂ))) -
            (Complex.digamma (1 / (2 * (xr : ℂ)) + 1 / 2) -
              Complex.digamma (1 / (2 * (xr : ℂ)) + 1)))
        Filter.atTop
        (nhds (0 - (Complex.digamma (1 / (2 * (xr : ℂ)) + 1 / 2) -
          Complex.digamma (1 / (2 * (xr : ℂ)) + 1)))) :=
      hD.sub_const _
    have hmul := hsub.const_mul (1 / 2 : ℂ)
    have heq : (1 / 2 : ℂ) * (0 - (Complex.digamma (1 / (2 * (xr : ℂ)) + 1 / 2) -
        Complex.digamma (1 / (2 * (xr : ℂ)) + 1)))
        = (1 / 2 : ℂ) * (Complex.digamma (1 / (2 * (xr : ℂ)) + 1) -
          Complex.digamma (1 / (2 * (xr : ℂ)) + 1 / 2)) := by
      ring
    rw [heq] at hmul
    refine hmul.congr' (Eventually.of_forall fun M => ?_)
    have hpair := entry9_paired_eq_digamma hx M
    change (1 / 2 : ℂ) *
        ((Complex.digamma ((1 / (2 * (xr : ℂ)) + 1 / 2 : ℂ) + (M : ℂ)) -
          Complex.digamma ((1 / (2 * (xr : ℂ)) + 1 : ℂ) + (M : ℂ))) -
          (Complex.digamma (1 / (2 * (xr : ℂ)) + 1 / 2) -
            Complex.digamma (1 / (2 * (xr : ℂ)) + 1)))
      = (xr : ℂ) * ∑ k ∈ range (2 * M),
        ((-1 : ℂ) ^ k * (1 / (((((k : ℕ)) : ℂ) + 1) * (xr : ℂ) + 1)))
    rw [hpair]
  exact (tendsto_nhds_unique hx_even htarget).symm

private theorem entry9_ratio_hasDerivAt_param {x : ℂ} (hx : 0 < x.re)
    {t : ℝ} (ht : t ∈ Set.Ioc (0 : ℝ) 1) :
    HasDerivAt (fun y : ℂ => chapter8UnitPowRatio y t)
      (((Real.log t : ℝ) : ℂ) * chapter8UnitPow x t /
        (1 + chapter8UnitPow x t) ^ 2) x := by
  have ht_pos : (0 : ℝ) < t := (Set.mem_Ioc.mp ht).1
  have ht0 : t ≠ 0 := ne_of_gt ht_pos
  have hden : (1 : ℂ) + chapter8UnitPow x t ≠ 0 :=
    entry9_one_add_unitPow_ne hx ht_pos
  set L : ℂ := ((Real.log t : ℝ) : ℂ) with hL
  have hPow : ∀ y : ℂ, chapter8UnitPow y t = Complex.exp (y * L) := by
    intro y
    unfold chapter8UnitPow
    rw [ite_eq_right ht0]
  have hRatio : (fun y : ℂ => chapter8UnitPowRatio y t)
      = (fun y : ℂ => Complex.exp (y * L) / (1 + Complex.exp (y * L))) := by
    funext y
    unfold chapter8UnitPowRatio
    rw [hPow y]
  have hlin : HasDerivAt (fun y : ℂ => y * L) L x := by
    have h := (hasDerivAt_id x).mul_const L
    rwa [one_mul] at h
  have hexp : HasDerivAt (fun y : ℂ => Complex.exp (y * L))
      (Complex.exp (x * L) * L) x :=
    hlin.cexp
  have hdenF : HasDerivAt (fun y : ℂ => (1 : ℂ) + Complex.exp (y * L))
      (Complex.exp (x * L) * L) x := by
    have h := (hasDerivAt_const x (1 : ℂ)).add hexp
    rwa [zero_add] at h
  have hdiv := hexp.div hdenF (by simpa [hPow x] using hden)
  have heq : (Complex.exp (x * L) * L * (1 + Complex.exp (x * L)) -
      Complex.exp (x * L) * (Complex.exp (x * L) * L)) /
        (1 + Complex.exp (x * L)) ^ 2
      = L * Complex.exp (x * L) / (1 + Complex.exp (x * L)) ^ 2 := by
    ring
  have hdiv2 : HasDerivAt (fun y : ℂ => Complex.exp (y * L) /
      (1 + Complex.exp (y * L)))
      (L * Complex.exp (x * L) / (1 + Complex.exp (x * L)) ^ 2) x :=
    heq ▸ hdiv
  have htarget : L * Complex.exp (x * L) / (1 + Complex.exp (x * L)) ^ 2
      = L * chapter8UnitPow x t / (1 + chapter8UnitPow x t) ^ 2 := by
    rw [← hPow x]
  rw [hRatio]
  exact htarget ▸ hdiv2

private theorem entry9_denom_lower_bound {x0 : ℂ} (hx0 : 0 < x0.re) :
    ∃ c : ℝ, 0 < c ∧ ∀ x ∈ Metric.ball x0 (x0.re / 2),
      ∀ t ∈ Set.Ioc (0 : ℝ) 1,
        c ≤ ‖(1 : ℂ) + chapter8UnitPow x t‖ := by
  have hr : (0 : ℝ) < x0.re / 2 := by linarith
  set r : ℝ := x0.re / 2 with hr_def
  set delta : ℝ := x0.re / 2 with hdelta_def
  set M : ℝ := ‖x0‖ + r with hM_def
  have hM_pos : (0 : ℝ) < M := by
    have h1 : (0 : ℝ) ≤ ‖x0‖ := norm_nonneg _
    linarith
  have hdelta_pos : (0 : ℝ) < delta := hr
  set K : ℝ := M / delta with hK_def
  have hK_pos : (0 : ℝ) < K := div_pos hM_pos hdelta_pos
  set eps : ℝ := min 1 (Real.pi / (2 * K)) with heps_def
  have hpi : (0 : ℝ) < Real.pi / (2 * K) := by positivity
  have heps_pos : (0 : ℝ) < eps := lt_min_iff.mpr ⟨by norm_num, hpi⟩
  have heps_le1 : eps ≤ 1 := min_le_left _ _
  have heps_le_pi : eps ≤ Real.pi / (2 * K) := min_le_right _ _
  have hKeps : K * eps ≤ Real.pi / 2 := by
    have h1 : K * eps ≤ K * (Real.pi / (2 * K)) :=
      mul_le_mul_of_nonneg_left heps_le_pi (le_of_lt hK_pos)
    have h2 : K * (Real.pi / (2 * K)) = Real.pi / 2 := by
      field_simp
    linarith
  set c : ℝ := 1 - Real.exp (-eps) with hc_def
  have hexp_lt1 : Real.exp (-eps) < 1 := by
    rw [Real.exp_lt_one_iff]
    linarith
  have hexp_pos : (0 : ℝ) < Real.exp (-eps) := Real.exp_pos _
  have hc_pos : (0 : ℝ) < c := by linarith
  have hc_le1 : c ≤ 1 := by
    unfold c
    linarith
  refine ⟨c, hc_pos, fun x hx t ht => ?_⟩
  have ht_pos : (0 : ℝ) < t := (Set.mem_Ioc.mp ht).1
  have ht_le1 : t ≤ 1 := (Set.mem_Ioc.mp ht).2
  have ht0 : t ≠ 0 := ne_of_gt ht_pos
  have hL_nonpos : Real.log t ≤ 0 :=
    Real.log_nonpos (le_of_lt ht_pos) ht_le1
  have hdist : dist x x0 < r := Metric.mem_ball.mp hx
  have hnorm : ‖x - x0‖ < r := by
    rwa [dist_eq_norm] at hdist
  have hre_bound : |x.re - x0.re| < r := by
    have h1 : |x.re - x0.re| ≤ ‖x - x0‖ := by
      have h2 := Complex.abs_re_le_norm (x - x0)
      rwa [Complex.sub_re] at h2
    exact lt_of_le_of_lt h1 hnorm
  have hx_re : delta < x.re := by
    have h3 : -r < x.re - x0.re := by
      have h4 := neg_lt_of_abs_lt hre_bound
      linarith [h4]
    linarith
  have hx_re_pos : (0 : ℝ) < x.re := lt_trans hdelta_pos hx_re
  have hx_re_ge : delta ≤ x.re := le_of_lt hx_re
  have hnorm_x : ‖x‖ < M := by
    have h1 : ‖x‖ ≤ ‖x0‖ + ‖x - x0‖ := by
      have h2 := norm_add_le x0 (x - x0)
      have e : x0 + (x - x0) = x := by abel
      rwa [e] at h2
    linarith
  have him_le : |x.im| ≤ M := by
    have h1 : |x.im| ≤ ‖x‖ := Complex.abs_im_le_norm x
    linarith
  have hPow : chapter8UnitPow x t
      = Complex.exp (x * ((Real.log t : ℝ) : ℂ)) := by
    unfold chapter8UnitPow
    rw [ite_eq_right ht0]
  set w : ℂ := x * ((Real.log t : ℝ) : ℂ) with hw_def
  have ha : w.re = x.re * Real.log t := by
    rw [hw_def, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im]
    ring
  have hb : w.im = x.im * Real.log t := by
    rw [hw_def, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im]
    ring
  have ha_nonpos : w.re ≤ 0 := by
    rw [ha]
    exact mul_nonpos_of_nonneg_of_nonpos (le_of_lt hx_re_pos) hL_nonpos
  have habs : |w.im| ≤ K * |w.re| := by
    have e1 : |w.im| = |x.im| * |Real.log t| := by
      rw [hb, abs_mul]
    have e2 : |w.re| = x.re * |Real.log t| := by
      rw [ha, abs_mul, abs_of_nonneg (le_of_lt hx_re_pos)]
    have hK_def2 : K * |w.re| = (M / delta) * (x.re * |Real.log t|) := by
      rw [hK_def, e2]
    have hle : |x.im| * |Real.log t|
        ≤ (M / delta) * (x.re * |Real.log t|) := by
      have h3 : |x.im| ≤ (M / delta) * x.re := by
        rw [div_mul_eq_mul_div, le_div_iff₀ hdelta_pos]
        calc |x.im| * delta ≤ M * delta := by gcongr
          _ ≤ M * x.re := by gcongr
      calc |x.im| * |Real.log t|
          ≤ ((M / delta) * x.re) * |Real.log t| := by gcongr
        _ = (M / delta) * (x.re * |Real.log t|) := by ring
    rwa [e1, hK_def2]
  have hPow_w : chapter8UnitPow x t = Complex.exp w := hPow
  rw [hPow_w]
  have hexp_norm : ‖Complex.exp w‖ = Real.exp w.re := Complex.norm_exp w
  have hexp_re : (Complex.exp w).re
      = Real.exp w.re * Real.cos w.im := Complex.exp_re w
  by_cases hcase : |w.re| ≤ eps
  · have hb_le : |w.im| ≤ Real.pi / 2 := by
      have h1 : K * |w.re| ≤ K * eps :=
        mul_le_mul_of_nonneg_left hcase (le_of_lt hK_pos)
      have h2 : |w.im| ≤ K * eps := le_trans habs h1
      exact le_trans h2 hKeps
    have hmem : w.im ∈ Set.Icc (-(Real.pi / 2)) (Real.pi / 2) := by
      have h3 := abs_le.mp hb_le
      exact Set.mem_Icc.mpr h3
    have hcos : (0 : ℝ) ≤ Real.cos w.im :=
      Real.cos_nonneg_of_mem_Icc hmem
    have hexp_nonneg : (0 : ℝ) ≤ (Complex.exp w).re := by
      rw [hexp_re]
      exact mul_nonneg (le_of_lt (Real.exp_pos _)) hcos
    have hre_ge : (1 : ℝ) ≤ ((1 : ℂ) + Complex.exp w).re := by
      rw [Complex.add_re, Complex.one_re]
      linarith
    have hnorm_ge : (1 : ℝ) ≤ ‖(1 : ℂ) + Complex.exp w‖ := by
      have h1 := Complex.abs_re_le_norm ((1 : ℂ) + Complex.exp w)
      have h2 : |((1 : ℂ) + Complex.exp w).re|
          = ((1 : ℂ) + Complex.exp w).re :=
        abs_of_nonneg (by linarith)
      linarith
    exact le_trans hc_le1 hnorm_ge
  · push Not at hcase
    have ha_eq : |w.re| = -w.re := abs_of_nonpos ha_nonpos
    have hw_lt : w.re < -eps := by linarith
    have hexp_lt : Real.exp w.re < Real.exp (-eps) :=
      Real.exp_lt_exp.mpr hw_lt
    have h1 : (1 : ℝ) - ‖Complex.exp w‖ ≤ ‖(1 : ℂ) + Complex.exp w‖ := by
      have h2 := norm_sub_norm_le (1 : ℂ) (-Complex.exp w)
      rw [norm_one] at h2
      have e1 : (1 : ℂ) - (-Complex.exp w) = 1 + Complex.exp w := by
        abel
      have e2 : ‖(-Complex.exp w : ℂ)‖ = ‖Complex.exp w‖ := norm_neg _
      rwa [e1, e2] at h2
    rw [hexp_norm] at h1
    have h2 : c < 1 - Real.exp w.re := by
      unfold c
      linarith
    linarith

private theorem entry9_deriv_bound {x0 : ℂ} (hx0 : 0 < x0.re) (c : ℝ)
    (hc : 0 < c)
    (hlower : ∀ x ∈ Metric.ball x0 (x0.re / 2),
      ∀ t ∈ Set.Ioc (0 : ℝ) 1, c ≤ ‖(1 : ℂ) + chapter8UnitPow x t‖)
    {x : ℂ} (hx : x ∈ Metric.ball x0 (x0.re / 2))
    {t : ℝ} (ht : t ∈ Set.Ioc (0 : ℝ) 1) :
    ‖((Real.log t : ℝ) : ℂ) * chapter8UnitPow x t /
        (1 + chapter8UnitPow x t) ^ 2‖
      ≤ (1 / c ^ 2) * (-Real.log t) := by
  have ht_pos : (0 : ℝ) < t := (Set.mem_Ioc.mp ht).1
  have ht_le1 : t ≤ 1 := (Set.mem_Ioc.mp ht).2
  have ht0 : t ≠ 0 := ne_of_gt ht_pos
  have hlog_nonpos : Real.log t ≤ 0 :=
    Real.log_nonpos (le_of_lt ht_pos) ht_le1
  have habs_log : |Real.log t| = -Real.log t := abs_of_nonpos hlog_nonpos
  have hdist : dist x x0 < x0.re / 2 := Metric.mem_ball.mp hx
  have hnorm : ‖x - x0‖ < x0.re / 2 := by
    rwa [dist_eq_norm] at hdist
  have hre_bound : |x.re - x0.re| < x0.re / 2 := by
    have h1 : |x.re - x0.re| ≤ ‖x - x0‖ := by
      have h2 := Complex.abs_re_le_norm (x - x0)
      rwa [Complex.sub_re] at h2
    exact lt_of_le_of_lt h1 hnorm
  have hx_re : (0 : ℝ) < x.re := by
    have h3 : -(x0.re / 2) < x.re - x0.re := by
      have h4 := neg_lt_of_abs_lt hre_bound
      linarith [h4]
    linarith
  have hPow : chapter8UnitPow x t
      = Complex.exp (x * ((Real.log t : ℝ) : ℂ)) := by
    unfold chapter8UnitPow
    rw [ite_eq_right ht0]
  have ha : (x * ((Real.log t : ℝ) : ℂ)).re = x.re * Real.log t := by
    rw [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im]
    ring
  have ha_nonpos : (x * ((Real.log t : ℝ) : ℂ)).re ≤ 0 := by
    rw [ha]
    exact mul_nonpos_of_nonneg_of_nonpos (le_of_lt hx_re) hlog_nonpos
  have hexp_le1 : ‖chapter8UnitPow x t‖ ≤ 1 := by
    rw [hPow, Complex.norm_exp]
    exact Real.exp_le_one_iff.mpr ha_nonpos
  have hden_ge : c ≤ ‖(1 : ℂ) + chapter8UnitPow x t‖ := hlower x hx t ht
  have hden_pos : (0 : ℝ) < ‖(1 : ℂ) + chapter8UnitPow x t‖ :=
    lt_of_lt_of_le hc hden_ge
  have hsq_ge : c ^ 2 ≤ ‖(1 : ℂ) + chapter8UnitPow x t‖ ^ 2 := by
    apply pow_le_pow_left₀ (le_of_lt hc) hden_ge 2
  have hsq_pos : (0 : ℝ) < ‖(1 : ℂ) + chapter8UnitPow x t‖ ^ 2 := by
    positivity
  have hc_sq_pos : (0 : ℝ) < c ^ 2 := by positivity
  have hdiv_le : 1 / ‖(1 : ℂ) + chapter8UnitPow x t‖ ^ 2 ≤ 1 / c ^ 2 := by
    apply one_div_le_one_div_of_le hc_sq_pos hsq_ge
  have hnorm_eq : ‖((Real.log t : ℝ) : ℂ) * chapter8UnitPow x t /
        (1 + chapter8UnitPow x t) ^ 2‖
      = |Real.log t| * ‖chapter8UnitPow x t‖ /
        ‖(1 : ℂ) + chapter8UnitPow x t‖ ^ 2 := by
    have h_ofReal : ‖(((Real.log t : ℝ)) : ℂ)‖ = |Real.log t| :=
      RCLike.norm_ofReal _
    rw [norm_div, norm_mul, norm_pow, h_ofReal]
  rw [hnorm_eq, habs_log]
  have hle1 : (-Real.log t) * ‖chapter8UnitPow x t‖ /
        ‖(1 : ℂ) + chapter8UnitPow x t‖ ^ 2
      ≤ (-Real.log t) * 1 / ‖(1 : ℂ) + chapter8UnitPow x t‖ ^ 2 := by
    apply div_le_div_of_nonneg_right _ (le_of_lt hsq_pos)
    apply mul_le_mul_of_nonneg_left hexp_le1
    linarith
  have hle2 : (-Real.log t) * 1 / ‖(1 : ℂ) + chapter8UnitPow x t‖ ^ 2
      ≤ (1 / c ^ 2) * (-Real.log t) := by
    have h3 : (-Real.log t) * 1 / ‖(1 : ℂ) + chapter8UnitPow x t‖ ^ 2
        = (-Real.log t) * (1 / ‖(1 : ℂ) + chapter8UnitPow x t‖ ^ 2) := by
      ring
    rw [h3]
    have h4 : (1 / c ^ 2) * (-Real.log t)
        = (-Real.log t) * (1 / c ^ 2) := by ring
    rw [h4]
    apply mul_le_mul_of_nonneg_left hdiv_le
    linarith
  have heq : (-Real.log t) * ‖chapter8UnitPow x t‖ /
        ‖(1 : ℂ) + chapter8UnitPow x t‖ ^ 2
      = |Real.log t| * ‖chapter8UnitPow x t‖ /
        ‖(1 : ℂ) + chapter8UnitPow x t‖ ^ 2 := by
    rw [← habs_log]
  linarith [hle1, hle2, heq]

private theorem entry9_bound_integrable (c : ℝ) :
    IntervalIntegrable (fun t : ℝ => (1 / c ^ 2) * (-Real.log t))
      volume 0 1 := by
  have hlog : IntervalIntegrable Real.log volume 0 1 :=
    intervalIntegral.intervalIntegrable_log'
  have hneg : IntervalIntegrable (-Real.log) volume 0 1 := hlog.neg
  have hmul := hneg.const_mul (1 / c ^ 2)
  simpa using hmul

private theorem entry9_F'_continuousOn {x0 : ℂ} (hx0 : 0 < x0.re) :
    ContinuousOn
      (fun t : ℝ => ((Real.log t : ℝ) : ℂ) * chapter8UnitPow x0 t /
        (1 + chapter8UnitPow x0 t) ^ 2)
      (Set.Ioc 0 1) := by
  have hsub : Set.Ioc (0 : ℝ) 1 ⊆ {0}ᶜ := by
    intro t ht
    have ht_pos : (0 : ℝ) < t := (Set.mem_Ioc.mp ht).1
    simp only [Set.mem_compl_iff, Set.mem_singleton_iff]
    exact ne_of_gt ht_pos
  have hlog : ContinuousOn (fun t : ℝ => ((Real.log t : ℝ) : ℂ))
      (Set.Ioc 0 1) :=
    Complex.continuous_ofReal.comp_continuousOn
      (Real.continuousOn_log.mono hsub)
  have hexp : ContinuousOn (chapter8UnitPow x0) (Set.Ioc 0 1) :=
    (entry9_continuousOn_unitPow_Ioi (x := x0)).mono
      Set.Ioc_subset_Ioi_self
  have hden : ContinuousOn (fun t : ℝ => (1 : ℂ) + chapter8UnitPow x0 t)
      (Set.Ioc 0 1) :=
    continuousOn_const.add hexp
  have hden2 : ContinuousOn
      (fun t : ℝ => ((1 : ℂ) + chapter8UnitPow x0 t) ^ 2)
      (Set.Ioc 0 1) :=
    hden.pow 2
  have hnum : ContinuousOn
      (fun t : ℝ => ((Real.log t : ℝ) : ℂ) * chapter8UnitPow x0 t)
      (Set.Ioc 0 1) :=
    hlog.mul hexp
  apply hnum.div hden2
  intro t ht
  have ht_pos : (0 : ℝ) < t := (Set.mem_Ioc.mp ht).1
  have hne : (1 : ℂ) + chapter8UnitPow x0 t ≠ 0 :=
    entry9_one_add_unitPow_ne hx0 ht_pos
  exact pow_ne_zero 2 hne

private theorem entry9_integral_differentiableOn :
    DifferentiableOn ℂ
      (fun x : ℂ => ∫ t in (0 : ℝ)..1, chapter8UnitPowRatio x t)
      {x : ℂ | 0 < x.re} := by
  intro x0 hx0
  have hx0' : (0 : ℝ) < x0.re := hx0
  obtain ⟨c, hc_pos, hlower⟩ := entry9_denom_lower_bound hx0'
  set s : Set ℂ := Metric.ball x0 (x0.re / 2) with hs_def
  have hr_pos : (0 : ℝ) < x0.re / 2 := by linarith
  have hs_mem : s ∈ nhds x0 := Metric.ball_mem_nhds x0 hr_pos
  have hF_int : IntervalIntegrable (chapter8UnitPowRatio x0) volume 0 1 :=
    entry9_intervalIntegrable hx0'
  have hIoc_eq : Set.uIoc (0 : ℝ) 1 = Set.Ioc (0 : ℝ) 1 :=
    Set.uIoc_of_le (by norm_num)
  have hF_meas : ∀ᶠ x in nhds x0,
      AEStronglyMeasurable (chapter8UnitPowRatio x)
        (volume.restrict (Set.uIoc 0 1)) := by
    filter_upwards [hs_mem] with x hx
    have hx_re : (0 : ℝ) < x.re := by
      have hdist : dist x x0 < x0.re / 2 := Metric.mem_ball.mp hx
      have hnorm : ‖x - x0‖ < x0.re / 2 := by
        rwa [dist_eq_norm] at hdist
      have hre_bound : |x.re - x0.re| < x0.re / 2 := by
        have h1 : |x.re - x0.re| ≤ ‖x - x0‖ := by
          have h2 := Complex.abs_re_le_norm (x - x0)
          rwa [Complex.sub_re] at h2
        exact lt_of_le_of_lt h1 hnorm
      have h3 : -(x0.re / 2) < x.re - x0.re := by
        have h4 := neg_lt_of_abs_lt hre_bound
        linarith [h4]
      linarith
    have hcont := entry9_continuousOn_ratio_Icc hx_re
    rw [hIoc_eq]
    exact (hcont.mono Set.Ioc_subset_Icc_self).aestronglyMeasurable
      measurableSet_Ioc
  have hF'_meas : AEStronglyMeasurable
      (fun t : ℝ => ((Real.log t : ℝ) : ℂ) * chapter8UnitPow x0 t /
        (1 + chapter8UnitPow x0 t) ^ 2)
      (volume.restrict (Set.uIoc 0 1)) := by
    rw [hIoc_eq]
    exact (entry9_F'_continuousOn hx0').aestronglyMeasurable
      measurableSet_Ioc
  have h_bound : ∀ᵐ t ∂volume, t ∈ Set.uIoc (0 : ℝ) 1 →
      ∀ x ∈ s, ‖((Real.log t : ℝ) : ℂ) * chapter8UnitPow x t /
        (1 + chapter8UnitPow x t) ^ 2‖
        ≤ (1 / c ^ 2) * (-Real.log t) := by
    refine Eventually.of_forall fun t ht x hx => ?_
    have htIoc : t ∈ Set.Ioc (0 : ℝ) 1 := by
      rwa [hIoc_eq] at ht
    exact entry9_deriv_bound hx0' c hc_pos hlower hx htIoc
  have hbound_int : IntervalIntegrable
      (fun t : ℝ => (1 / c ^ 2) * (-Real.log t)) volume 0 1 :=
    entry9_bound_integrable c
  have h_diff : ∀ᵐ t ∂volume, t ∈ Set.uIoc (0 : ℝ) 1 →
      ∀ x ∈ s, HasDerivAt (fun y : ℂ => chapter8UnitPowRatio y t)
        (((Real.log t : ℝ) : ℂ) * chapter8UnitPow x t /
          (1 + chapter8UnitPow x t) ^ 2) x := by
    refine Eventually.of_forall fun t ht x hx => ?_
    have htIoc : t ∈ Set.Ioc (0 : ℝ) 1 := by
      rwa [hIoc_eq] at ht
    have hx_re : (0 : ℝ) < x.re := by
      have hdist : dist x x0 < x0.re / 2 := Metric.mem_ball.mp hx
      have hnorm : ‖x - x0‖ < x0.re / 2 := by
        rwa [dist_eq_norm] at hdist
      have hre_bound : |x.re - x0.re| < x0.re / 2 := by
        have h1 : |x.re - x0.re| ≤ ‖x - x0‖ := by
          have h2 := Complex.abs_re_le_norm (x - x0)
          rwa [Complex.sub_re] at h2
        exact lt_of_le_of_lt h1 hnorm
      have h3 : -(x0.re / 2) < x.re - x0.re := by
        have h4 := neg_lt_of_abs_lt hre_bound
        linarith [h4]
      linarith
    exact entry9_ratio_hasDerivAt_param hx_re htIoc
  have hderiv :=
    intervalIntegral.hasDerivAt_integral_of_dominated_loc_of_deriv_le
      (μ := volume) (a := (0 : ℝ)) (b := 1)
      (F := fun x t => chapter8UnitPowRatio x t)
      (F' := fun x t => ((Real.log t : ℝ) : ℂ) * chapter8UnitPow x t /
        (1 + chapter8UnitPow x t) ^ 2)
      (bound := fun t => (1 / c ^ 2) * (-Real.log t))
      (s := s) (x₀ := x0) hs_mem hF_meas hF_int hF'_meas h_bound
      hbound_int h_diff
  exact hderiv.2.differentiableAt.differentiableWithinAt

private theorem entry9_isOpen_re_pos : IsOpen {x : ℂ | 0 < x.re} := by
  have h : {x : ℂ | 0 < x.re} = Complex.re ⁻¹' Set.Ioi 0 := rfl
  rw [h]
  exact Complex.continuous_re.isOpen_preimage _ isOpen_Ioi

private theorem entry9_convex_re_pos : Convex ℝ {x : ℂ | 0 < x.re} :=
  convex_halfSpace_re_gt 0

private theorem entry9_preconnected_re_pos :
    IsPreconnected {x : ℂ | 0 < x.re} :=
  entry9_convex_re_pos.isPreconnected

private theorem entry9_gamma_differentiableOn :
    DifferentiableOn ℂ Complex.Gamma {z : ℂ | 0 < z.re} := by
  intro z hz
  have hz' : (0 : ℝ) < z.re := hz
  have havoid : ∀ m : ℕ, z ≠ -(m : ℂ) := by
    intro m hm
    have hre := congrArg Complex.re hm
    rw [Complex.neg_re, Complex.natCast_re] at hre
    have hm0 : (0 : ℝ) ≤ ((m : ℕ) : ℝ) := Nat.cast_nonneg m
    linarith
  exact (Complex.differentiableAt_Gamma _ havoid).differentiableWithinAt

private theorem entry9_digamma_analyticOn :
    AnalyticOnNhd ℂ Complex.digamma {z : ℂ | 0 < z.re} := by
  have hGamma := entry9_gamma_differentiableOn
  have hderiv := hGamma.deriv entry9_isOpen_re_pos
  have hne : ∀ z ∈ {z : ℂ | 0 < z.re}, Complex.Gamma z ≠ 0 := by
    intro z hz
    have hz' : (0 : ℝ) < z.re := hz
    have havoid : ∀ m : ℕ, z ≠ -(m : ℂ) := by
      intro m hm
      have hre := congrArg Complex.re hm
      rw [Complex.neg_re, Complex.natCast_re] at hre
      have hm0 : (0 : ℝ) ≤ ((m : ℕ) : ℝ) := Nat.cast_nonneg m
      linarith
    exact Complex.Gamma_ne_zero havoid
  have hdiv : DifferentiableOn ℂ
      (fun z => deriv Complex.Gamma z / Complex.Gamma z)
      {z : ℂ | 0 < z.re} :=
    hderiv.div hGamma hne
  have hdig : DifferentiableOn ℂ Complex.digamma {z : ℂ | 0 < z.re} := hdiv
  exact hdig.analyticOnNhd entry9_isOpen_re_pos

private theorem entry9_t0_differentiableOn :
    DifferentiableOn ℂ (fun x : ℂ => 1 / (2 * x) + 1)
      {x : ℂ | 0 < x.re} := by
  have h2x : DifferentiableOn ℂ (fun x : ℂ => 2 * x) {x : ℂ | 0 < x.re} :=
    differentiableOn_id.const_mul 2
  have hne : ∀ x ∈ {x : ℂ | 0 < x.re}, (2 : ℂ) * x ≠ 0 := by
    intro x hx
    have hx' : (0 : ℝ) < x.re := hx
    exact mul_ne_zero (by norm_num) (entry9_x_ne_zero hx')
  have hinv := (differentiableOn_const (1 : ℂ)).div h2x hne
  simpa using hinv.add_const (1 : ℂ)

private theorem entry9_s0_differentiableOn :
    DifferentiableOn ℂ (fun x : ℂ => 1 / (2 * x) + 1 / 2)
      {x : ℂ | 0 < x.re} := by
  have h2x : DifferentiableOn ℂ (fun x : ℂ => 2 * x) {x : ℂ | 0 < x.re} :=
    differentiableOn_id.const_mul 2
  have hne : ∀ x ∈ {x : ℂ | 0 < x.re}, (2 : ℂ) * x ≠ 0 := by
    intro x hx
    have hx' : (0 : ℝ) < x.re := hx
    exact mul_ne_zero (by norm_num) (entry9_x_ne_zero hx')
  have hinv := (differentiableOn_const (1 : ℂ)).div h2x hne
  simpa using hinv.add_const (1 / 2 : ℂ)

private theorem entry9_F_analyticOn :
    AnalyticOnNhd ℂ
      (fun x : ℂ => x * ∫ t in (0 : ℝ)..1, chapter8UnitPowRatio x t)
      {x : ℂ | 0 < x.re} := by
  have hF : DifferentiableOn ℂ
      (fun x : ℂ => x * ∫ t in (0 : ℝ)..1, chapter8UnitPowRatio x t)
      {x : ℂ | 0 < x.re} :=
    differentiableOn_id.mul entry9_integral_differentiableOn
  exact hF.analyticOnNhd entry9_isOpen_re_pos

private theorem entry9_G_analyticOn :
    AnalyticOnNhd ℂ
      (fun x : ℂ => (1 / 2 : ℂ) *
        (Complex.digamma (1 / (2 * x) + 1) -
          Complex.digamma (1 / (2 * x) + 1 / 2)))
      {x : ℂ | 0 < x.re} := by
  have hdig : DifferentiableOn ℂ Complex.digamma {z : ℂ | 0 < z.re} :=
    entry9_digamma_analyticOn.differentiableOn
  have hmem_t0 : ∀ x ∈ {x : ℂ | 0 < x.re},
      (1 / (2 * x) + 1 : ℂ) ∈ {z : ℂ | 0 < z.re} := by
    intro x hx
    have hx' : (0 : ℝ) < x.re := hx
    have h := entry9_re_inv_two_mul_pos hx'
    have hre : (1 / (2 * x) + 1 : ℂ).re = (1 / (2 * x)).re + 1 := by
      rw [Complex.add_re, Complex.one_re]
    have hpos : (0 : ℝ) < (1 / (2 * x) + 1 : ℂ).re := by
      rw [hre]
      linarith
    exact hpos
  have hmem_s0 : ∀ x ∈ {x : ℂ | 0 < x.re},
      (1 / (2 * x) + 1 / 2 : ℂ) ∈ {z : ℂ | 0 < z.re} := by
    intro x hx
    have hx' : (0 : ℝ) < x.re := hx
    have h := entry9_re_inv_two_mul_pos hx'
    have h12 : ((1 / 2 : ℂ)).re = 1 / 2 := by simp
    have hre : (1 / (2 * x) + 1 / 2 : ℂ).re
        = (1 / (2 * x)).re + 1 / 2 := by
      rw [Complex.add_re, h12]
    have hpos : (0 : ℝ) < (1 / (2 * x) + 1 / 2 : ℂ).re := by
      rw [hre]
      linarith
    exact hpos
  have ht0 : DifferentiableOn ℂ
      (fun x : ℂ => Complex.digamma (1 / (2 * x) + 1))
      {x : ℂ | 0 < x.re} :=
    hdig.comp entry9_t0_differentiableOn hmem_t0
  have hs0 : DifferentiableOn ℂ
      (fun x : ℂ => Complex.digamma (1 / (2 * x) + 1 / 2))
      {x : ℂ | 0 < x.re} :=
    hdig.comp entry9_s0_differentiableOn hmem_s0
  have hsub := ht0.sub hs0
  have hmul := hsub.const_mul (1 / 2 : ℂ)
  have hG : DifferentiableOn ℂ
      (fun x : ℂ => (1 / 2 : ℂ) *
        (Complex.digamma (1 / (2 * x) + 1) -
          Complex.digamma (1 / (2 * x) + 1 / 2)))
      {x : ℂ | 0 < x.re} := by
    simpa [mul_sub] using hmul
  exact hG.analyticOnNhd entry9_isOpen_re_pos

private theorem entry9_hkey_all {x : ℂ} (hx : 0 < x.re) :
    (1 / 2 : ℂ) *
        (Complex.digamma (1 / (2 * x) + 1) -
          Complex.digamma (1 / (2 * x) + 1 / 2))
      = x * ∫ u in (0 : ℝ)..1, chapter8UnitPowRatio x u := by
  have hF := entry9_F_analyticOn
  have hG := entry9_G_analyticOn
  have hU := entry9_preconnected_re_pos
  have h1_mem : (1 : ℂ) ∈ {x : ℂ | 0 < x.re} := by
    change (0 : ℝ) < (1 : ℂ).re
    rw [Complex.one_re]
    norm_num
  have hEq : Set.EqOn
      (fun x : ℂ => x * ∫ t in (0 : ℝ)..1, chapter8UnitPowRatio x t)
      (fun x : ℂ => (1 / 2 : ℂ) *
        (Complex.digamma (1 / (2 * x) + 1) -
          Complex.digamma (1 / (2 * x) + 1 / 2)))
      {x : ℂ | 0 < x.re} := by
    apply AnalyticOnNhd.eqOn_of_preconnected_of_mem_closure hF hG hU h1_mem
    have hseq_tendsto : Filter.Tendsto
        (fun n : ℕ => (((1 + 1 / ((n : ℝ) + 1) : ℝ)) : ℂ))
        Filter.atTop (nhds 1) := by
      have h0 : Filter.Tendsto (fun n : ℕ => 1 / ((n : ℝ) + 1))
          Filter.atTop (nhds 0) :=
        tendsto_one_div_add_atTop_nhds_zero_nat
      have h1 : Filter.Tendsto (fun n : ℕ => 1 + 1 / ((n : ℝ) + 1))
          Filter.atTop (nhds (1 + 0)) :=
        tendsto_const_nhds.add h0
      rw [add_zero] at h1
      have h2 : Filter.Tendsto
          (fun n : ℕ => (((1 + 1 / ((n : ℝ) + 1) : ℝ)) : ℂ))
          Filter.atTop (nhds (((1 : ℝ)) : ℂ)) :=
        (Complex.continuous_ofReal.tendsto 1).comp h1
      rwa [Complex.ofReal_one] at h2
    have hmem : ∀ᶠ n : ℕ in Filter.atTop,
        (((1 + 1 / ((n : ℝ) + 1) : ℝ)) : ℂ) ∈
          ({z | (fun x : ℂ => x * ∫ t in (0 : ℝ)..1,
              chapter8UnitPowRatio x t) z =
              (fun x : ℂ => (1 / 2 : ℂ) *
                (Complex.digamma (1 / (2 * x) + 1) -
                  Complex.digamma (1 / (2 * x) + 1 / 2))) z} \
            {(1 : ℂ)}) := by
      refine Eventually.of_forall fun n => ?_
      have hpos1 : (0 : ℝ) < 1 / ((n : ℝ) + 1) := by positivity
      have hxr_pos : (0 : ℝ) < 1 + 1 / ((n : ℝ) + 1) := by linarith
      have hne_real : (1 + 1 / ((n : ℝ) + 1) : ℝ) ≠ 1 := by
        intro hcon
        have h1 : (1 : ℝ) / ((n : ℝ) + 1) = 0 := by linarith
        have h2 : (0 : ℝ) < 1 / ((n : ℝ) + 1) := hpos1
        linarith
      have hne : (((1 + 1 / ((n : ℝ) + 1) : ℝ)) : ℂ) ≠ 1 := by
        intro hcon
        have h1 : (1 + 1 / ((n : ℝ) + 1) : ℝ) = 1 := by
          have h2 := congrArg Complex.re hcon
          rw [Complex.ofReal_re, Complex.one_re] at h2
          exact h2
        exact hne_real h1
      have hEq_n := (entry9_real_hkey hxr_pos).symm
      constructor
      · change (fun x : ℂ => x * ∫ t in (0 : ℝ)..1,
            chapter8UnitPowRatio x t)
            (((1 + 1 / ((n : ℝ) + 1) : ℝ)) : ℂ) = _
        change (((1 + 1 / ((n : ℝ) + 1) : ℝ)) : ℂ) * _ = _
        exact hEq_n
      · simp only [Set.mem_singleton_iff]
        exact hne
    exact mem_closure_of_tendsto hseq_tendsto hmem
  have hx_mem : x ∈ {x : ℂ | 0 < x.re} := hx
  have hFG := hEq hx_mem
  simp only at hFG
  exact hFG.symm

/-- Source: Bruce C. Berndt, Ramanujan's Notebooks, Part I, Chapter 8.

Canonical-`Complex.digamma` form of `ramanujan_part1_ch8_entry9_qgamma`.
-/
theorem ramanujan_part1_ch8_entry9_qgamma_digamma (x : ℂ) (hx : 0 < x.re) :
    x ≠ 0 ∧
      IntervalIntegrable (chapter8UnitPowRatio x) volume 0 1 ∧
      (∀ u : ℝ, u ∈ Set.Icc 0 1 →
        1 + chapter8UnitPow x u ≠ 0) ∧
      Complex.Gamma (1 / (2 * x) + 1) ≠ 0 ∧
      Complex.Gamma (1 / x + 1) ≠ 0 ∧
      Complex.digamma (1 / (2 * x) + 1) =
        Complex.digamma (1 / x + 1) - (Real.log 2 : ℂ) +
          x * ∫ u in (0 : ℝ)..1, chapter8UnitPowRatio x u := by
  refine ⟨entry9_x_ne_zero hx, entry9_intervalIntegrable hx, ?_, ?_, ?_, ?_⟩
  · intro u hu
    exact entry9_one_add_unitPow_ne_Icc hx hu
  · exact entry9_gamma_ne_one_div_two_mul_add hx
  · exact entry9_gamma_ne_one_div_add hx
  · have hdup := Complex.digamma_two_mul (s := 1 / (2 * x) + 1 / 2)
      (entry9_two_mul_side hx)
    rw [entry9_two_mul_lhs hx, entry9_two_mul_rhs] at hdup
    have hlog2 : ((Real.log 2 : ℝ) : ℂ) = Complex.log 2 := by
      have h : ((Real.log 2 : ℝ) : ℂ) = Complex.log ((2 : ℝ) : ℂ) :=
        Complex.ofReal_log (by norm_num)
      rw [h]
      congr 1
    have hkey := entry9_hkey_all hx
    rw [hdup, hlog2]
    linear_combination hkey

/-- Source: Bruce C. Berndt, Ramanujan's Notebooks, Part I, Chapter 8.

Proves `Wanted` entry `ramanujan_part1_ch8_entry9_qgamma`.
-/
theorem ramanujan_part1_ch8_entry9_qgamma (x : ℂ) (hx : 0 < x.re) :
    x ≠ 0 ∧
      IntervalIntegrable (chapter8UnitPowRatio x) volume 0 1 ∧
      (∀ u : ℝ, u ∈ Set.Icc 0 1 →
        1 + chapter8UnitPow x u ≠ 0) ∧
      Complex.Gamma (1 / (2 * x) + 1) ≠ 0 ∧
      Complex.Gamma (1 / x + 1) ≠ 0 ∧
      chapter8Digamma (1 / (2 * x) + 1) =
        chapter8Digamma (1 / x + 1) - (Real.log 2 : ℂ) +
          x * ∫ u in (0 : ℝ)..1, chapter8UnitPowRatio x u := by
  have h := ramanujan_part1_ch8_entry9_qgamma_digamma x hx
  obtain ⟨hne0, hInt, hden, hG1, hG2, hdig⟩ := h
  refine ⟨hne0, hInt, hden, hG1, hG2, ?_⟩
  simpa only [chapter8Digamma_eq_digamma] using hdig

end
end Entry9Qgamma
end MathlibExt.Analysis.Ramanujan.Part1Ch8
end
