/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import Mathlib.Analysis.PSeries

public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
public import Mathlib.NumberTheory.Harmonic.EulerMascheroni
import Mathlib.Analysis.Calculus.SmoothSeries
import Mathlib.Analysis.Complex.LocallyUniformLimit
import MathlibExt.Analysis.SpecialFunctions.Gamma.Digamma
import Mathlib.NumberTheory.ZetaValues
import Mathlib.Tactic.Abel
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Push
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Set

@[expose] public section

/-!
# Ramanujan's Notebooks, Part I, Chapter 6, Entry 2

Away from the negative integers, `ψ(z+1) + γ` is complex differentiable and its derivative is
the absolutely convergent series `∑ 1/(z+k+1)²`. The general Gamma and digamma facts used here
live in `MathlibExt.Analysis.SpecialFunctions.Gamma.Digamma`.
-/

namespace MathlibExt.Analysis.Ramanujan.Part1Ch6

namespace Entry2Stirlingseries

open scoped Nat Real BigOperators Interval Polynomial ContDiff
open Asymptotics Filter Finset Complex Topology MeasureTheory

noncomputable section

def chapter6HarmonicInterpolation (z : ℂ) : ℂ :=
  (Real.eulerMascheroniConstant : ℂ) +
    deriv Complex.Gamma (z + 1) / Complex.Gamma (z + 1)

/-- Shifted pole-avoidance: if `z` avoids `{-1, -2, …}` then `z + 1` avoids
`{0, -1, -2, …}`, the poles of `Complex.Gamma`. -/
private lemma aux_pole_shift (z : ℂ) (hz : ∀ k : ℕ, z ≠ -((k + 1 : ℕ) : ℂ)) :
    ∀ m : ℕ, z + 1 ≠ -((m : ℕ) : ℂ) := by
  intro m
  cases m with
  | zero =>
    have h := hz 0
    simp only [Nat.zero_add, Nat.cast_one] at h
    simp only [Nat.cast_zero, neg_zero]
    intro hcon
    apply h
    linear_combination hcon
  | succ m =>
    have h := hz (m + 1)
    intro hcon
    apply h
    push_cast at hcon ⊢
    linear_combination hcon

/-- The interpolation function (unfolded) is differentiable away from poles. -/
private lemma aux_interpFun_diffble (z : ℂ) (hz : ∀ k : ℕ, z ≠ -((k + 1 : ℕ) : ℂ)) :
    DifferentiableAt ℂ (fun w : ℂ => (Real.eulerMascheroniConstant : ℂ)
      + deriv Complex.Gamma (w + 1) / Complex.Gamma (w + 1)) z := by
  have hz1 : ∀ m : ℕ, z + 1 ≠ -((m : ℕ) : ℂ) := aux_pole_shift z hz
  have hnum : DifferentiableAt ℂ (fun w : ℂ => deriv Complex.Gamma (w + 1)) z :=
    ((Complex.analyticAt_Gamma _ hz1).deriv.differentiableAt).comp z
      (differentiableAt_id.add_const 1)
  have hden : DifferentiableAt ℂ (fun w : ℂ => Complex.Gamma (w + 1)) z :=
    ((Complex.differentiableAt_Gamma (z + 1) hz1)).comp z
      (differentiableAt_id.add_const 1)
  have hne : Complex.Gamma (z + 1) ≠ 0 := Complex.Gamma_ne_zero hz1
  have hmain : DifferentiableAt ℂ
      (fun w : ℂ => (Real.eulerMascheroniConstant : ℂ)
        + deriv Complex.Gamma (w + 1) / Complex.Gamma (w + 1)) z :=
    (differentiableAt_const _).add (hnum.div hden hne)
  exact hmain

/-- Transfer: complex interpolation derivative at `↑y` is the real series. -/
private lemma aux_transfer (y : ℝ) (hy : 0 < y) :
    deriv (fun w : ℂ => (Real.eulerMascheroniConstant : ℂ)
      + deriv Complex.Gamma (w + 1) / Complex.Gamma (w + 1)) (↑y)
      = ((∑' j : ℕ, 1 / (y + (j : ℝ) + 1) ^ 2 : ℝ) : ℂ) := by
  have hU : ∀ k : ℕ, (↑y : ℂ) ≠ -(((k + 1 : ℕ)) : ℂ) := by
    intro k hcon
    have hcon2 : y = -(((k + 1 : ℕ)) : ℝ) := by
      have h := congrArg Complex.re hcon
      simpa using h
    have hle : y ≤ 0 := by
      rw [hcon2]
      have : (0 : ℝ) ≤ (((k + 1 : ℕ)) : ℝ) := Nat.cast_nonneg _
      linarith
    linarith
  have hC := (aux_interpFun_diffble _ hU).hasDerivAt
  have hC' := hC.comp_ofReal
  have hR := (Real.hasDerivAt_tsum_digamma_series y hy).ofReal_comp
  have hpt : ∀ t : ℝ, 0 < t →
      ((Real.eulerMascheroniConstant : ℂ)
        + deriv Complex.Gamma (↑t + 1) / Complex.Gamma (↑t + 1))
      = ↑(∑' j : ℕ, (1 / ((j : ℝ) + 1) - 1 / (t + (j : ℝ) + 1))) := by
    intro t ht
    have e1 : (↑t : ℂ) + 1 = ↑(t + 1) := by push_cast; ring
    rw [e1]
    have hser := (Real.hasSum_digamma_series t ht).tsum_eq
    have hlog := Real.deriv_log_Gamma (t + 1) (by linarith)
    have hdig := Complex.deriv_Gamma_ofReal (t + 1) (by linarith)
    rw [hser, hlog]
    conv_rhs => rw [Complex.ofReal_add, Complex.ofReal_div]
    rw [← hdig, ← Complex.Gamma_ofReal]
    ring
  have heq : (fun t : ℝ => (Real.eulerMascheroniConstant : ℂ)
        + deriv Complex.Gamma (↑t + 1) / Complex.Gamma (↑t + 1))
      =ᶠ[𝓝 y] (fun t => ↑(∑' j : ℕ, (1 / ((j : ℝ) + 1) - 1 / (t + (j : ℝ) + 1)))) := by
    apply Filter.eventuallyEq_of_mem (Ioi_mem_nhds hy)
    intro t ht
    simp only [Set.mem_Ioi] at ht
    exact hpt t ht
  have hC'' := hC'.congr_of_eventuallyEq heq.symm
  have hfin := hC''.unique hR
  exact hfin

/-- Right half-plane. -/
private def H : Set ℂ := {z | 0 < z.re}

private lemma H_isOpen : IsOpen H := by
  have heq : H = Complex.re ⁻¹' Set.Ioi (0 : ℝ) := rfl
  rw [heq]
  exact isOpen_Ioi.preimage Complex.continuous_re

private lemma H_convex : Convex ℝ H := by
  have heq : H = Complex.reLm ⁻¹' Set.Ioi (0 : ℝ) := rfl
  rw [heq]
  exact (convex_Ioi 0).linear_preimage _

private lemma H_preconnected : IsPreconnected H := H_convex.isPreconnected

private lemma H_mem_one : (1 : ℂ) ∈ H := by
  show (0 : ℝ) < (1 : ℂ).re
  simp

private lemma H_avoids (w : ℂ) (hw : w ∈ H) (m : ℕ) : w ≠ -((m : ℕ) : ℂ) := by
  intro hcon
  have hre : w.re = -((m : ℕ) : ℝ) := by
    have h := congrArg Complex.re hcon
    simpa using h
  have hpos : (0 : ℝ) < w.re := hw
  have hnn : (0 : ℝ) ≤ ((m : ℕ) : ℝ) := Nat.cast_nonneg m
  linarith

/-- Trigamma summand. -/
private def triTerm (k : ℕ) (w : ℂ) : ℂ := 1 / (w + ((k + 1 : ℕ) : ℂ)) ^ 2

private lemma triTerm_diffOn (k : ℕ) : DifferentiableOn ℂ (triTerm k) H := by
  intro w hw
  have hne : w + ((k + 1 : ℕ) : ℂ) ≠ 0 := by
    intro hcon
    have hrew : (w + ((k + 1 : ℕ) : ℂ)).re = w.re + ((k + 1 : ℕ) : ℝ) := by
      simp [Complex.add_re]
    rw [hcon] at hrew
    simp only [Complex.zero_re] at hrew
    have hpos : (0 : ℝ) < w.re := hw
    have hnn : (0 : ℝ) ≤ ((k + 1 : ℕ) : ℝ) := Nat.cast_nonneg _
    linarith
  have h2 : (w + ((k + 1 : ℕ) : ℂ)) ^ 2 ≠ 0 := pow_ne_zero 2 hne
  have hbase : DifferentiableAt ℂ (fun w : ℂ => (w + ((k + 1 : ℕ) : ℂ)) ^ 2) w :=
    (differentiableAt_id.add_const _).pow 2
  have hinv : DifferentiableAt ℂ (fun w : ℂ => ((w + ((k + 1 : ℕ) : ℂ)) ^ 2)⁻¹) w :=
    hbase.inv h2
  have hcongr : (fun w : ℂ => ((w + ((k + 1 : ℕ) : ℂ)) ^ 2)⁻¹) = triTerm k := by
    funext v
    simp [triTerm, one_div]
  rw [hcongr] at hinv
  exact hinv.differentiableWithinAt

private lemma tri_majorant_summable :
    Summable (fun k : ℕ => (1 : ℝ) / ((k + 1 : ℕ) : ℝ) ^ 2) := by
  exact (summable_nat_add_iff 1).mpr (Real.summable_one_div_nat_pow.mpr one_lt_two)

private lemma tri_bound (k : ℕ) (w : ℂ) (hw : w ∈ H) :
    ‖triTerm k w‖ ≤ 1 / ((k + 1 : ℕ) : ℝ) ^ 2 := by
  have hpos : (0 : ℝ) < w.re := hw
  have hrew : (w + ((k + 1 : ℕ) : ℂ)).re = w.re + ((k + 1 : ℕ) : ℝ) := by
    simp [Complex.add_re]
  have hle : ((k + 1 : ℕ) : ℝ) ≤ ‖w + ((k + 1 : ℕ) : ℂ)‖ := by
    have h := Complex.re_le_norm (w + ((k + 1 : ℕ) : ℂ))
    rw [hrew] at h
    have hnn : (0 : ℝ) ≤ ((k + 1 : ℕ) : ℝ) := Nat.cast_nonneg _
    linarith
  have hsq : ((k + 1 : ℕ) : ℝ) ^ 2 ≤ ‖w + ((k + 1 : ℕ) : ℂ)‖ ^ 2 :=
    pow_le_pow_left₀ (by positivity) hle 2
  have hpos2 : (0 : ℝ) < ((k + 1 : ℕ) : ℝ) ^ 2 := by positivity
  simp only [triTerm, norm_div, norm_one, norm_pow]
  exact one_div_le_one_div_of_le hpos2 hsq

private lemma F2_diffOn : DifferentiableOn ℂ (fun w => ∑' k : ℕ, triTerm k w) H :=
  Complex.differentiableOn_tsum_of_summable_norm
    tri_majorant_summable triTerm_diffOn H_isOpen tri_bound

private lemma F2_analytic : AnalyticOnNhd ℂ (fun w => ∑' k : ℕ, triTerm k w) H :=
  F2_diffOn.analyticOnNhd H_isOpen

/-- Interpolation function (unfolded). -/
private def Jfun (w : ℂ) : ℂ :=
  (Real.eulerMascheroniConstant : ℂ) + deriv Complex.Gamma (w + 1) / Complex.Gamma (w + 1)

private lemma Jfun_analyticOnH : AnalyticOnNhd ℂ Jfun H := by
  intro w hw
  have hw1 : ∀ m : ℕ, w + 1 ≠ -((m : ℕ) : ℂ) := by
    intro m hcon
    have hrew : (w + 1).re = w.re + 1 := by simp [Complex.add_re]
    have hcon2 : (w + 1).re = -((m : ℕ) : ℝ) := by
      have h := congrArg Complex.re hcon
      simpa using h
    have hpos : (0 : ℝ) < w.re := hw
    have hnn : (0 : ℝ) ≤ ((m : ℕ) : ℝ) := Nat.cast_nonneg m
    linarith
  have hG : AnalyticAt ℂ Complex.Gamma (w + 1) := Complex.analyticAt_Gamma _ hw1
  have hshift : AnalyticAt ℂ (fun w : ℂ => w + 1) w :=
    (analyticAt_id.add analyticAt_const).congr (Filter.Eventually.of_forall fun v => rfl)
  have hnumcomp : AnalyticAt ℂ ((deriv Complex.Gamma) ∘ (fun w : ℂ => w + 1)) w :=
    AnalyticAt.comp (f := (fun w : ℂ => w + 1)) (x := w) hG.deriv hshift
  have hnum : AnalyticAt ℂ (fun w : ℂ => deriv Complex.Gamma (w + 1)) w :=
    hnumcomp.congr (Filter.Eventually.of_forall fun v => rfl)
  have hdencomp : AnalyticAt ℂ (Complex.Gamma ∘ (fun w : ℂ => w + 1)) w :=
    AnalyticAt.comp (f := (fun w : ℂ => w + 1)) (x := w) hG hshift
  have hden : AnalyticAt ℂ (fun w : ℂ => Complex.Gamma (w + 1)) w :=
    hdencomp.congr (Filter.Eventually.of_forall fun v => rfl)
  have hne : (fun w : ℂ => Complex.Gamma (w + 1)) w ≠ 0 :=
    Complex.Gamma_ne_zero hw1
  have hdiv : AnalyticAt ℂ ((fun w : ℂ => deriv Complex.Gamma (w + 1)) /
      (fun w : ℂ => Complex.Gamma (w + 1))) w :=
    hnum.div hden hne
  have hadd : AnalyticAt ℂ ((fun _ : ℂ => (Real.eulerMascheroniConstant : ℂ)) +
      ((fun w : ℂ => deriv Complex.Gamma (w + 1)) /
        (fun w : ℂ => Complex.Gamma (w + 1)))) w :=
    analyticAt_const.add hdiv
  exact hadd.congr (Filter.Eventually.of_forall fun v => rfl)

private lemma F1_analyticOnH : AnalyticOnNhd ℂ (deriv Jfun) H := Jfun_analyticOnH.deriv

/-- Cast of the real trigamma tsum to `triTerm`. -/
private lemma cast_tri (y : ℝ) (j : ℕ) :
    ((1 / (y + (j : ℝ) + 1) ^ 2 : ℝ) : ℂ) = triTerm j (↑y) := by
  have hden : ((y + (j : ℝ) + 1 : ℝ) : ℂ) = (↑y + ((j + 1 : ℕ) : ℂ)) := by
    push_cast
    ring
  simp only [triTerm, ← hden, Complex.ofReal_div, Complex.ofReal_one,
    Complex.ofReal_pow]

private lemma Jfun_eq : Jfun = (fun w : ℂ => (Real.eulerMascheroniConstant : ℂ)
    + deriv Complex.Gamma (w + 1) / Complex.Gamma (w + 1)) := rfl

/-- Agreement of `deriv Jfun` with the trigamma tsum on positive reals. -/
private lemma agree_ofReal (y : ℝ) (hy : 0 < y) :
    deriv Jfun (↑y) = ∑' k : ℕ, triTerm k (↑y) := by
  rw [Jfun_eq, aux_transfer y hy, Complex.ofReal_tsum]
  exact tsum_congr (cast_tri y)

/-- The two analytic functions agree frequently near `1`. -/
private lemma freq_eq :
    ∃ᶠ z in 𝓝[≠] (1 : ℂ), deriv Jfun z = (fun w => ∑' k : ℕ, triTerm k w) z := by
  by_contra hcon
  push_neg at hcon
  rw [eventually_nhdsWithin_iff, Metric.eventually_nhds_iff] at hcon
  obtain ⟨ε, hε, hP⟩ := hcon
  set δ := min (ε / 2) (1 / 2) with hδdef
  have hδpos : 0 < δ := lt_min (by linarith) (by norm_num)
  have hδlt : δ < ε := lt_of_le_of_lt (min_le_left _ _) (by linarith)
  set y : ℝ := 1 + δ with hydef
  have hy : 0 < y := by linarith
  have hmem : (↑y : ℂ) ∈ Metric.ball (1 : ℂ) ε := by
    rw [Metric.mem_ball, dist_eq_norm]
    have hsub : (↑y : ℂ) - 1 = ((δ : ℝ) : ℂ) := by
      rw [hydef]
      push_cast
      ring
    rw [hsub, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hδpos]
    -- goal: δ < ε as reals
    exact hδlt
  have hne : (↑y : ℂ) ≠ 1 := by
    intro hc
    have h := congrArg Complex.re hc
    simp [hydef] at h
    linarith
  have hdist : dist (↑y : ℂ) 1 < ε := Metric.mem_ball.mp hmem
  have hPy := hP hdist (by simpa using hne)
  have hag := agree_ofReal y hy
  exact hPy hag

/-- Identity on the half-plane. -/
private lemma eqOnH : Set.EqOn (deriv Jfun) (fun w => ∑' k : ℕ, triTerm k w) H :=
  AnalyticOnNhd.eqOn_of_preconnected_of_frequently_eq
    F1_analyticOnH F2_analytic H_preconnected H_mem_one freq_eq

/-- `HasSum` of the trigamma series on the half-plane. -/
private lemma hasSumH (w : ℂ) (hw : w ∈ H) :
    HasSum (fun k : ℕ => 1 / (w + ((k + 1 : ℕ) : ℂ)) ^ 2) (deriv Jfun w) := by
  have hsum : Summable (fun k : ℕ => triTerm k w) :=
    Summable.of_norm_bounded tri_majorant_summable (fun k => tri_bound k w hw)
  have hval : deriv Jfun w = ∑' k : ℕ, triTerm k w := eqOnH hw
  rw [hval]
  simpa [triTerm] using hsum.hasSum

/-- Every `z ∈ U` has a ball contained in `U`. -/
private lemma U_ball (z : ℂ) (hz : ∀ k : ℕ, z ≠ -((k + 1 : ℕ) : ℂ)) :
    ∃ r : ℝ, 0 < r ∧ ∀ w ∈ Metric.ball z r, ∀ k : ℕ, w ≠ -((k + 1 : ℕ) : ℂ) := by
  set M : ℝ := ‖z‖ with hMdef
  set B : ℕ := ⌈M + 2⌉₊ with hBdef
  have hMB : M + 2 ≤ (B : ℝ) := Nat.le_ceil (M + 2)
  have hBpos : 0 < B := by
    have hpos : (0 : ℝ) < M + 2 := by
      have hnn : (0 : ℝ) ≤ M := norm_nonneg _
      linarith
    exact Nat.ceil_pos.mpr hpos
  set f : ℕ → ℝ := fun m => ‖z - (-(((m + 1 : ℕ)) : ℂ))‖ with hfdef
  have hfpos : ∀ m : ℕ, m ∈ Finset.range B → 0 < f m := by
    intro m _
    have hshow : f m = ‖z - (-(((m + 1 : ℕ)) : ℂ))‖ := rfl
    rw [hshow, norm_pos_iff]
    exact sub_ne_zero.mpr (hz m)
  have hIrng : ((Finset.range B).image f).Nonempty :=
    ⟨f 0, Finset.mem_image.mpr ⟨0, Finset.mem_range.mpr hBpos, rfl⟩⟩
  set d : ℝ := ((Finset.range B).image f).min' hIrng with hddef
  have hdpos : 0 < d := by
    obtain ⟨m, hm, hfm⟩ := Finset.mem_image.mp (Finset.min'_mem _ hIrng)
    rw [hddef, ← hfm]
    exact hfpos m hm
  have hdle : ∀ m : ℕ, m ∈ Finset.range B → d ≤ f m := by
    intro m hm
    rw [hddef]
    exact Finset.min'_le _ _ (Finset.mem_image.mpr ⟨m, hm, rfl⟩)
  refine ⟨min d 1 / 2, div_pos (lt_min hdpos one_pos) two_pos, fun w hw k hcon => ?_⟩
  rw [Metric.mem_ball, dist_eq_norm] at hw
  have htri2 : f k ≤ ‖z - w‖ + ‖w - (-(((k + 1 : ℕ)) : ℂ))‖ := by
    have heq : z - (-(((k + 1 : ℕ)) : ℂ))
        = (z - w) + (w - (-(((k + 1 : ℕ)) : ℂ))) := by
      abel
    have hshow : f k = ‖z - (-(((k + 1 : ℕ)) : ℂ))‖ := rfl
    rw [hshow, heq]
    exact norm_add_le _ _
  have h2 : ‖w - (-(((k + 1 : ℕ)) : ℂ))‖ = 0 := by
    rw [hcon, sub_self, norm_zero]
  have hsym : ‖z - w‖ = ‖w - z‖ := norm_sub_rev _ _
  have hdm_lt : f k < min d 1 / 2 := by linarith [htri2, h2, hsym, hw]
  have hr1 : min d 1 / 2 ≤ 1 / 2 := by
    have h : min d 1 ≤ 1 := min_le_right d 1
    linarith
  have hr2 : min d 1 / 2 ≤ d / 2 := by
    have h : min d 1 ≤ d := min_le_left d 1
    linarith
  by_cases hcase : k < B
  · have hmem : k ∈ Finset.range B := Finset.mem_range.mpr hcase
    have hle := hdle k hmem
    linarith
  · have hmB : B ≤ k := not_lt.mp hcase
    have hmB' : (B : ℝ) ≤ ((k + 1 : ℕ) : ℝ) := by
      calc (B : ℝ) ≤ (k : ℝ) := Nat.cast_le.mpr hmB
        _ ≤ ((k + 1 : ℕ) : ℝ) := Nat.cast_le.mpr (Nat.le_succ k)
    have hdm_eq : f k = ‖z + (((k + 1 : ℕ)) : ℂ)‖ := by
      have hshow : f k = ‖z - (-(((k + 1 : ℕ)) : ℂ))‖ := rfl
      rw [hshow, sub_neg_eq_add]
    have hfar : (2 : ℝ) ≤ f k := by
      rw [hdm_eq]
      have htri3 := norm_add_le (z + (((k + 1 : ℕ)) : ℂ)) (-z)
      have heq : (z + (((k + 1 : ℕ)) : ℂ)) + -z = (((k + 1 : ℕ)) : ℂ) := by abel
      rw [heq, Complex.norm_natCast, norm_neg] at htri3
      linarith [hMB, hmB']
    linarith [hr1]

/-- Shifts preserve `U`. -/
private lemma U_shift (z : ℂ) (hz : ∀ k : ℕ, z ≠ -((k + 1 : ℕ) : ℂ)) (j : ℕ) :
    ∀ k : ℕ, z + ((j : ℕ) : ℂ) ≠ -((k + 1 : ℕ) : ℂ) := by
  intro k hcon
  apply hz (k + j)
  push_cast at hcon ⊢
  linear_combination hcon

/-- Value recurrence for `Jfun`. -/
private lemma Jfun_shift (z : ℂ) (hz : ∀ k : ℕ, z ≠ -((k + 1 : ℕ) : ℂ)) :
    Jfun (z + 1) = Jfun z + 1 / (z + 1) := by
  have hz1 : z + 1 ≠ 0 := by
    intro hcon
    have h := hz 0
    simp only [Nat.zero_add, Nat.cast_one] at h
    apply h
    linear_combination hcon
  have hG1 : ∀ m : ℕ, z + 1 ≠ -((m : ℕ) : ℂ) := aux_pole_shift z hz
  have hzU1 : ∀ k : ℕ, z + 1 ≠ -(((k + 1 : ℕ)) : ℂ) := by
    intro k hcon
    apply hz (k + 1)
    push_cast at hcon ⊢
    linear_combination hcon
  have hG2 : ∀ m : ℕ, z + 1 + 1 ≠ -((m : ℕ) : ℂ) := aux_pole_shift (z + 1) hzU1
  have hC1 : HasDerivAt Complex.Gamma (deriv Complex.Gamma (z + 1)) (z + 1) :=
    (Complex.differentiableAt_Gamma _ hG1).hasDerivAt
  have hC2 : HasDerivAt Complex.Gamma (deriv Complex.Gamma (z + 1 + 1)) (z + 1 + 1) :=
    (Complex.differentiableAt_Gamma _ hG2).hasDerivAt
  have hL : HasDerivAt (Complex.Gamma ∘ (fun t : ℂ => t + 1))
      (deriv Complex.Gamma (z + 1 + 1) * 1) (z + 1) :=
    HasDerivAt.comp (z + 1) hC2 ((hasDerivAt_id' (z + 1)).add_const 1)
  have hR : HasDerivAt (fun t : ℂ => t * Complex.Gamma t)
      (1 * Complex.Gamma (z + 1) + (z + 1) * deriv Complex.Gamma (z + 1)) (z + 1) :=
    (hasDerivAt_id' (z + 1)).mul hC1
  have hmem : z + 1 ∈ ({0} : Set ℂ)ᶜ := by simpa using hz1
  have heq : (Complex.Gamma ∘ (fun t : ℂ => t + 1))
      =ᶠ[𝓝 (z + 1)] (fun t : ℂ => t * Complex.Gamma t) := by
    apply Filter.eventuallyEq_of_mem (isOpen_compl_singleton.mem_nhds hmem)
    intro t ht
    have ht0 : t ≠ 0 := by simpa using ht
    show Complex.Gamma (t + 1) = t * Complex.Gamma t
    exact Complex.Gamma_add_one t ht0
  have huniq := (hL.congr_of_eventuallyEq heq.symm).unique hR
  have hGne1 : Complex.Gamma (z + 1) ≠ 0 := Complex.Gamma_ne_zero hG1
  have hGre : Complex.Gamma (z + 1 + 1) = (z + 1) * Complex.Gamma (z + 1) :=
    Complex.Gamma_add_one _ hz1
  have hD : deriv Complex.Gamma (z + 1 + 1)
      = Complex.Gamma (z + 1) + (z + 1) * deriv Complex.Gamma (z + 1) := by
    linear_combination huniq
  simp only [Jfun]
  rw [hGre, hD]
  field_simp
  ring

/-- Derivative recurrence for `Jfun`. -/
private lemma Jfun_deriv_shift (z : ℂ) (hz : ∀ k : ℕ, z ≠ -((k + 1 : ℕ) : ℂ)) :
    deriv Jfun (z + 1) = deriv Jfun z - 1 / (z + 1) ^ 2 := by
  have hz1 : z + 1 ≠ 0 := by
    intro hcon
    have h := hz 0
    simp only [Nat.zero_add, Nat.cast_one] at h
    apply h
    linear_combination hcon
  have hzU1 : ∀ k : ℕ, z + 1 ≠ -(((k + 1 : ℕ)) : ℂ) := by
    intro k hcon
    apply hz (k + 1)
    push_cast at hcon ⊢
    linear_combination hcon
  obtain ⟨r, hrpos, hball⟩ := U_ball z hz
  have heq : (fun w => Jfun (w + 1)) =ᶠ[𝓝 z] (fun w => Jfun w + 1 / (w + 1)) := by
    apply Filter.eventuallyEq_of_mem (Metric.ball_mem_nhds z hrpos)
    intro w hw
    exact Jfun_shift w (hball w hw)
  have hdz : DifferentiableAt ℂ Jfun z := by
    rw [Jfun_eq]
    exact aux_interpFun_diffble z hz
  have hdz1 : DifferentiableAt ℂ Jfun (z + 1) := by
    rw [Jfun_eq]
    exact aux_interpFun_diffble _ hzU1
  have hL : HasDerivAt (fun w => Jfun (w + 1)) (deriv Jfun (z + 1)) z := by
    have hcomp : HasDerivAt (Jfun ∘ (fun w : ℂ => w + 1)) (deriv Jfun (z + 1) * 1) z := by
      have houter : HasDerivAt Jfun (deriv Jfun (z + 1))
          ((fun w : ℂ => w + 1) z) := hdz1.hasDerivAt
      exact HasDerivAt.comp z houter ((hasDerivAt_id' z).add_const 1)
    have hconv : (fun w => Jfun (w + 1)) =ᶠ[𝓝 z] (Jfun ∘ (fun w : ℂ => w + 1)) :=
      Filter.Eventually.of_forall fun w => rfl
    have hL' := hcomp.congr_of_eventuallyEq hconv
    simpa using hL'
  have hR : HasDerivAt (fun w => Jfun w + 1 / (w + 1))
      (deriv Jfun z + -1 / (z + 1) ^ 2) z := by
    have h1 : HasDerivAt (fun w : ℂ => w + 1) 1 z := ((hasDerivAt_id' z).add_const 1)
    have h2 : HasDerivAt (fun w : ℂ => ((w + 1))⁻¹) (-1 / (z + 1) ^ 2) z :=
      h1.inv hz1
    have h2' : HasDerivAt (fun w : ℂ => 1 / (w + 1)) (-1 / (z + 1) ^ 2) z := by
      have hconv2 : (fun w : ℂ => 1 / (w + 1)) =ᶠ[𝓝 z] (fun w : ℂ => ((w + 1))⁻¹) :=
        Filter.Eventually.of_forall fun w => one_div (w + 1)
      exact h2.congr_of_eventuallyEq hconv2
    exact hdz.hasDerivAt.add h2'
  have huniq := (hL.congr_of_eventuallyEq heq.symm).unique hR
  linear_combination huniq

/-- Summability of `triTerm` at any `z`. -/
private lemma tri_summable (z : ℂ) :
    Summable (fun k : ℕ => triTerm k z) := by
  apply Summable.of_norm_bounded (Complex.summable_norm_one_div_add_nat_succ_sq z)
  intro k
  exact le_rfl

/-- Value recurrence for the trigamma tsum. -/
private lemma tri_shift (z : ℂ) :
    ∑' k : ℕ, triTerm k z = triTerm 0 z + ∑' k : ℕ, triTerm k (z + 1) := by
  have hsum := tri_summable z
  have hsplit := Summable.sum_add_tsum_nat_add (f := fun k : ℕ => triTerm k z) 1 hsum
  rw [Finset.sum_range_one] at hsplit
  have hden : ∀ i : ℕ, (z + (((i + 1 + 1 : ℕ)) : ℂ))
      = ((z + 1) + (((i + 1 : ℕ)) : ℂ)) := by
    intro i
    push_cast
    ring
  have htail : (∑' i : ℕ, triTerm (i + 1) z) = ∑' k : ℕ, triTerm k (z + 1) := by
    apply tsum_congr
    intro i
    simp only [triTerm, hden i]
  rw [htail] at hsplit
  exact hsplit.symm

/-- One-step extension of `HasSum` backwards along the shift. -/
private lemma step (z : ℂ) (hz : ∀ k : ℕ, z ≠ -((k + 1 : ℕ) : ℂ))
    (hH : HasSum (fun k : ℕ => 1 / ((z + 1) + ((k + 1 : ℕ) : ℂ)) ^ 2)
      (deriv Jfun (z + 1))) :
    HasSum (fun k : ℕ => 1 / (z + ((k + 1 : ℕ) : ℂ)) ^ 2) (deriv Jfun z) := by
  have hfsum := tri_summable z
  have hgsum := tri_summable (z + 1)
  have hH' : HasSum (fun k : ℕ => triTerm k (z + 1)) (deriv Jfun (z + 1)) := by
    simpa [triTerm] using hH
  have hL : deriv Jfun (z + 1) = ∑' k : ℕ, triTerm k (z + 1) :=
    hH'.unique hgsum.hasSum
  have hD := Jfun_deriv_shift z hz
  have hval := tri_shift z
  have ht0 : triTerm 0 z = 1 / (z + 1) ^ 2 := by
    simp only [triTerm]
    norm_num
  have hgoal : deriv Jfun z = triTerm 0 z + ∑' k : ℕ, triTerm k (z + 1) := by
    rw [← hL, ht0, hD]
    ring
  rw [hgoal]
  have key := hfsum.hasSum
  rw [hval] at key
  simpa [triTerm] using key

/-- Extension from the half-plane to any `w ∈ U` by induction on the shift. -/
private lemma extend (n : ℕ) (w : ℂ) (hw : ∀ k : ℕ, w ≠ -((k + 1 : ℕ) : ℂ))
    (hmem : w + ((n : ℕ) : ℂ) ∈ H) :
    HasSum (fun k : ℕ => 1 / (w + ((k + 1 : ℕ) : ℂ)) ^ 2) (deriv Jfun w) := by
  induction n generalizing w with
  | zero =>
    simp only [Nat.cast_zero, add_zero] at hmem
    exact hasSumH w hmem
  | succ n ih =>
    have hw1 : ∀ k : ℕ, (w + 1) ≠ -((k + 1 : ℕ) : ℂ) := by
      intro k hcon
      apply hw (k + 1)
      push_cast at hcon ⊢
      linear_combination hcon
    have hcast : w + (((n + 1 : ℕ)) : ℂ) = (w + 1) + ((n : ℕ) : ℂ) := by
      push_cast
      ring
    rw [hcast] at hmem
    exact step w hw (ih (w + 1) hw1 hmem)

/-- Main `HasSum` on all of `U`. -/
private lemma main_hasSum (z : ℂ) (hz : ∀ k : ℕ, z ≠ -((k + 1 : ℕ) : ℂ)) :
    HasSum (fun k : ℕ => 1 / (z + ((k + 1 : ℕ) : ℂ)) ^ 2) (deriv Jfun z) := by
  set t : ℝ := max 0 (-z.re + 1) with htdef
  set n : ℕ := ⌈t⌉₊ with hndef
  have hnt : t ≤ (n : ℝ) := Nat.le_ceil t
  have hmem : z + ((n : ℕ) : ℂ) ∈ H := by
    show (0 : ℝ) < (z + ((n : ℕ) : ℂ)).re
    have hrew : (z + ((n : ℕ) : ℂ)).re = z.re + (n : ℝ) := by
      simp [Complex.add_re]
    rw [hrew]
    have h1 : -z.re + 1 ≤ (n : ℝ) := le_trans (le_max_right _ _) hnt
    linarith
  exact extend n z hz hmem

/-- Source: Bruce C. Berndt, Ramanujan's Notebooks, Part I, Chapter 6.
Proves `Wanted` entry `ramanujan_part1_ch6_entry2_stirlingseries`.
-/
theorem ramanujan_part1_ch6_entry2_stirlingseries (z : ℂ)
    (hz : ∀ k : ℕ, z ≠ -((k + 1 : ℕ) : ℂ)) :
    DifferentiableAt ℂ chapter6HarmonicInterpolation z ∧
      HasSum (fun k : ℕ => 1 / (z + (k + 1 : ℕ)) ^ 2)
        (deriv chapter6HarmonicInterpolation z) ∧
      Summable (fun k : ℕ => ‖(1 / (z + (k + 1 : ℕ)) ^ 2 : ℂ)‖) := by
  have hJ : chapter6HarmonicInterpolation = Jfun := rfl
  refine ⟨?_, ?_, ?_⟩
  · rw [hJ, Jfun_eq]
    exact aux_interpFun_diffble z hz
  · rw [hJ]
    exact main_hasSum z hz
  · exact Complex.summable_norm_one_div_add_nat_succ_sq z

end

end Entry2Stirlingseries

end MathlibExt.Analysis.Ramanujan.Part1Ch6
