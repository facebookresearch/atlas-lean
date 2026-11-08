/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import Mathlib.Analysis.PSeriesComplex

public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Analysis.Asymptotics.Defs
import Mathlib.Analysis.Calculus.ContDiff.Basic
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.Calculus.SmoothSeries
import Mathlib.Analysis.Complex.AbelLimit
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Complex.Exponential
import Mathlib.Analysis.Complex.Trigonometric
import Mathlib.Analysis.Normed.Group.FunctionSeries
import Mathlib.Analysis.SpecialFunctions.Complex.Log
import Mathlib.Analysis.SpecialFunctions.Complex.LogBounds
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
public import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.SpecialFunctions.Pow.Complex
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Arctan
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Basic.Complex.Basic
public import Mathlib.Data.Finset.Defs
public import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.MeasureTheory.Integral.DominatedConvergence
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
public import Mathlib.MeasureTheory.Measure.MeasureSpaceDef
import Mathlib.NumberTheory.Bernoulli
import Mathlib.NumberTheory.Harmonic.Defs
public import Mathlib.NumberTheory.LSeries.RiemannZeta
public import Mathlib.Order.Filter.Basic
public import Mathlib.Topology.Algebra.InfiniteSum.Basic
public import Mathlib.Topology.Basic
import Mathlib.Tactic.Continuity
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

@[expose] public section

section
/-!
# Ramanujan's Notebooks, Part I, Chapter 9

Statements of entries from B. C. Berndt, *Ramanujan's Notebooks, Part I*
(Springer, 1985), with proofs.
-/

namespace MathlibExt.Analysis.Ramanujan.Part1Ch9

namespace Entry13Bernoulligen

open scoped Nat Real BigOperators Interval Polynomial ContDiff
open Filter Finset Topology MeasureTheory

noncomputable section

def chapter9ClausenTerm (m : ℕ) (x : ℝ) (k : ℕ) : ℝ :=
  if Even m then
    Real.sin (((k + 1 : ℕ) : ℝ) * x) / (((k + 1 : ℕ) : ℝ) ^ m)
  else
    Real.cos (((k + 1 : ℕ) : ℝ) * x) / (((k + 1 : ℕ) : ℝ) ^ m)

def chapter9Clausen (m : ℕ) (x : ℝ) : ℝ :=
  if m = 0 then 0
  else if m = 1 then -Real.log |2 * Real.sin (x / 2)|
  else ∑' k : ℕ, chapter9ClausenTerm m x k

def chapter9Entry13Integrand (n : ℕ) (u : ℝ) : ℝ :=
  u ^ n / 2 * (Real.cos (u / 2) / Real.sin (u / 2))

private lemma chapter9ClausenTerm_base_pos (m : ℕ) (k : ℕ) :
    (0 : ℝ) < ((((k + 1 : ℕ)) : ℝ) ^ m) := by
  apply pow_pos
  have hcast : ((((k + 1 : ℕ))) : ℝ) = (k : ℝ) + 1 := by push_cast; ring
  have hnn : (0 : ℝ) ≤ (k : ℝ) := Nat.cast_nonneg k
  linarith

/-- Norm bound for the Clausen summand: `‖term‖ ≤ 1 / (k+1)^m`. -/
theorem chapter9ClausenTerm_norm_bound (m : ℕ) (x : ℝ) (k : ℕ) :
    ‖chapter9ClausenTerm m x k‖ ≤ 1 / ((((k + 1 : ℕ)) : ℝ) ^ m) := by
  have hpos := chapter9ClausenTerm_base_pos m k
  unfold chapter9ClausenTerm
  split_ifs with h
  · rw [Real.norm_eq_abs, abs_div, abs_of_pos hpos]
    exact div_le_div_of_nonneg_right (Real.abs_sin_le_one _) (le_of_lt hpos)
  · rw [Real.norm_eq_abs, abs_div, abs_of_pos hpos]
    exact div_le_div_of_nonneg_right (Real.abs_cos_le_one _) (le_of_lt hpos)

private lemma chapter9ClausenTerm_shift_summable (m : ℕ) (hm : 2 ≤ m) :
    Summable (fun k : ℕ => (1 : ℝ) / ((((k + 1 : ℕ)) : ℝ) ^ m)) := by
  have h : Summable (fun n : ℕ => (1 : ℝ) / ((n : ℝ) ^ m)) :=
    (Real.summable_one_div_nat_pow).mpr (by omega)
  exact (summable_nat_add_iff 1).mpr h

/-- The Clausen series is summable for `2 ≤ m`. -/
theorem chapter9ClausenTerm_summable_of_two_le (m : ℕ) (x : ℝ) (hm : 2 ≤ m) :
    Summable (chapter9ClausenTerm m x) :=
  Summable.of_norm_bounded (chapter9ClausenTerm_shift_summable m hm)
    (chapter9ClausenTerm_norm_bound m x)

/-- `chapter9Clausen` at `m = 0` vanishes. -/
theorem chapter9Clausen_zero (x : ℝ) : chapter9Clausen 0 x = 0 := by
  rfl

/-- `chapter9Clausen` at `m = 1` is the log-sine closed form. -/
theorem chapter9Clausen_one (x : ℝ) :
    chapter9Clausen 1 x = -Real.log |2 * Real.sin (x / 2)| := by
  rfl

/-- `chapter9Clausen` for `2 ≤ m` is the Clausen series. -/
theorem chapter9Clausen_of_two_le (m : ℕ) (x : ℝ) (hm : 2 ≤ m) :
    chapter9Clausen m x = ∑' k : ℕ, chapter9ClausenTerm m x k := by
  unfold chapter9Clausen
  split_ifs with h0 h1
  · omega
  · omega
  · rfl

private def entry13F0 (n : ℕ) : ℝ := if n = 1 then 1 else 0

private def entry13Ext (n : ℕ) (u : ℝ) : ℝ :=
  if u = 0 then entry13F0 n else chapter9Entry13Integrand n u

private lemma sin_half_ne_zero_of_mem {x u : ℝ} (hx : |x| < 2 * Real.pi)
    (hu : u ∈ Set.uIcc 0 x) (hu0 : u ≠ 0) : Real.sin (u / 2) ≠ 0 := by
  intro hsin
  rw [Real.sin_eq_zero_iff] at hsin
  obtain ⟨k, hk⟩ := hsin
  have hpi : 0 < Real.pi := Real.pi_pos
  have hu_eq : u = 2 * (k : ℝ) * Real.pi := by linarith
  have habs : |u| ≤ |x| := by
    rw [Set.mem_uIcc] at hu
    rcases hu with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · by_cases hxnn : 0 ≤ x
      · calc |u| = u := abs_of_nonneg (by linarith)
          _ ≤ x := h2
          _ = |x| := (abs_of_nonneg hxnn).symm
      · have hxlt : x < 0 := lt_of_not_ge hxnn
        linarith
    · by_cases hxnn : x ≤ 0
      · calc |u| = -u := abs_of_nonpos (by linarith)
          _ ≤ -x := by linarith
          _ = |x| := (abs_of_nonpos hxnn).symm
      · have hxlt : 0 < x := lt_of_not_ge hxnn
        linarith
  have hk0 : (k : ℝ) ≠ 0 := by
    intro hk0'
    have : u = 0 := by
      rw [hu_eq, hk0']; ring
    exact hu0 this
  have hk1 : (1 : ℝ) ≤ |(k : ℝ)| := by
    have hne : (k : ℤ) ≠ 0 := by
      intro hz; apply hk0; rw [hz]; simp
    have h1 : 1 ≤ |k| := Int.one_le_abs hne
    have h2 : ((1 : ℤ) : ℝ) ≤ (((|k| : ℤ)) : ℝ) := by exact_mod_cast h1
    rwa [Int.cast_one, Int.cast_abs] at h2
  have h2pi : 2 * Real.pi ≤ |u| := by
    rw [hu_eq]
    rw [show (2 * (k : ℝ) * Real.pi) = (2 * Real.pi) * (k : ℝ) from by ring]
    rw [abs_mul]
    have hnn : (0 : ℝ) ≤ 2 * Real.pi := by positivity
    calc 2 * Real.pi = (2 * Real.pi) * 1 := by ring
      _ ≤ (2 * Real.pi) * |(k : ℝ)| := by
          apply mul_le_mul_of_nonneg_left hk1 hnn
      _ = |2 * Real.pi| * |(k : ℝ)| := by rw [abs_of_nonneg hnn]
  linarith

private lemma sin_div_tendsto :
    Filter.Tendsto (fun y : ℝ => Real.sin y / y)
      (nhdsWithin 0 {0}ᶜ) (nhds 1) := by
  have h := (Real.hasDerivAt_sin 0).tendsto_slope
  rw [Real.cos_zero] at h
  have heq : ∀ y : ℝ, slope Real.sin 0 y = Real.sin y / y := by
    intro y
    simp [slope, sub_zero, Real.sin_zero, div_eq_inv_mul, smul_eq_mul]
  exact h.congr' (Eventually.of_forall (fun y => heq y))

private lemma half_tendsto_punctured :
    Filter.Tendsto (fun u : ℝ => u / 2)
      (nhdsWithin 0 {0}ᶜ) (nhdsWithin 0 {0}ᶜ) := by
  apply tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _ _ _
  · have hcont : Continuous (fun u : ℝ => u / 2) := by continuity
    have h0 : Filter.Tendsto (fun u : ℝ => u / 2)
      (nhdsWithin 0 {0}ᶜ) (nhds (0 / 2)) :=
      (hcont.tendsto 0).mono_left nhdsWithin_le_nhds
    simpa using h0
  · filter_upwards [self_mem_nhdsWithin] with u hu
    simp only [Set.mem_compl_iff, Set.mem_singleton_iff] at hu ⊢
    exact div_ne_zero hu two_ne_zero

private lemma sin_half_div_tendsto :
    Filter.Tendsto (fun u : ℝ => Real.sin (u / 2) / (u / 2))
      (nhdsWithin 0 {0}ᶜ) (nhds 1) :=
  sin_div_tendsto.comp half_tendsto_punctured

private lemma half_div_sin_tendsto :
    Filter.Tendsto (fun u : ℝ => (u / 2) / Real.sin (u / 2))
      (nhdsWithin 0 {0}ᶜ) (nhds 1) := by
  have h := sin_half_div_tendsto.inv₀ one_ne_zero
  rw [inv_one] at h
  exact h.congr' (Eventually.of_forall (fun u => inv_div _ _))

private lemma entry13_pointwise_eq (n : ℕ) (hn : 1 ≤ n) (u : ℝ) :
    chapter9Entry13Integrand n u =
      u ^ (n - 1) * Real.cos (u / 2) * ((u / 2) / Real.sin (u / 2)) := by
  unfold chapter9Entry13Integrand
  by_cases hs : Real.sin (u / 2) = 0
  · rw [hs, div_zero, div_zero, mul_zero, mul_zero]
  · have hns : n - 1 + 1 = n := Nat.sub_add_cancel hn
    have hpow : u ^ n = u ^ (n - 1) * u := by
      have h := pow_succ u (n - 1)
      rwa [hns] at h
    rw [hpow]
    field_simp

private lemma zero_pow_eq_entry13F0 (n : ℕ) (hn : 1 ≤ n) :
    (0 : ℝ) ^ (n - 1) = entry13F0 n := by
  unfold entry13F0
  by_cases hn1 : n = 1
  · subst hn1; simp
  · have hne : n - 1 ≠ 0 := by omega
    simp only [hn1, ite_false]
    exact zero_pow hne

private lemma entry13_tendsto (n : ℕ) (hn : 1 ≤ n) :
    Filter.Tendsto (chapter9Entry13Integrand n)
      (nhdsWithin 0 {0}ᶜ) (nhds (entry13F0 n)) := by
  have hpow : Filter.Tendsto (fun u : ℝ => u ^ (n - 1))
      (nhdsWithin 0 {0}ᶜ) (nhds ((0 : ℝ) ^ (n - 1))) :=
    ((continuous_pow (n - 1)).tendsto 0).mono_left nhdsWithin_le_nhds
  have hcos : Filter.Tendsto (fun u : ℝ => Real.cos (u / 2))
      (nhdsWithin 0 {0}ᶜ) (nhds 1) := by
    have hc : Filter.Tendsto (fun u : ℝ => Real.cos (u / 2))
        (nhds (0 : ℝ)) (nhds (Real.cos (0 / 2))) :=
      (Real.continuous_cos.comp (by continuity : Continuous (fun u : ℝ => u / 2))).tendsto 0
    simpa using hc.mono_left nhdsWithin_le_nhds
  have hprod := (hpow.mul hcos).mul half_div_sin_tendsto
  rw [zero_pow_eq_entry13F0 n hn] at hprod
  simp only [mul_one] at hprod
  exact hprod.congr' (Eventually.of_forall (fun u => (entry13_pointwise_eq n hn u).symm))

private lemma entry13Ext_continuousAt_zero (n : ℕ) (hn : 1 ≤ n) :
    ContinuousAt (entry13Ext n) 0 := by
  have hg := entry13_tendsto n hn
  have heq : (entry13Ext n) =ᶠ[nhdsWithin 0 {0}ᶜ] (chapter9Entry13Integrand n) := by
    filter_upwards [self_mem_nhdsWithin] with u hu
    simp only [Set.mem_compl_iff, Set.mem_singleton_iff] at hu
    simp [entry13Ext, hu]
  have hF : Filter.Tendsto (entry13Ext n) (nhdsWithin 0 {0}ᶜ) (nhds (entry13F0 n)) :=
    hg.congr' heq.symm
  have h0 : Filter.Tendsto (entry13Ext n) (nhdsWithin 0 {0}) (nhds (entry13F0 n)) := by
    rw [nhdsWithin_singleton]
    have hthis : entry13Ext n 0 = entry13F0 n := by simp [entry13Ext]
    have hpu := tendsto_pure_nhds (entry13Ext n) 0
    rwa [hthis] at hpu
  have hall := hF.sup h0
  rw [← nhdsWithin_union, Set.compl_union_self, nhdsWithin_univ] at hall
  change Filter.Tendsto (entry13Ext n) (nhds 0) (nhds (entry13Ext n 0))
  have hval : entry13Ext n 0 = entry13F0 n := by simp [entry13Ext]
  rwa [hval]

private lemma entry13Ext_continuousAt_of_ne (n : ℕ) (x : ℝ) (hx : |x| < 2 * Real.pi)
    (u : ℝ) (hu : u ∈ Set.uIcc 0 x) (hu0 : u ≠ 0) :
    ContinuousAt (entry13Ext n) u := by
  have hsin := sin_half_ne_zero_of_mem hx hu hu0
  have hg : ContinuousAt (chapter9Entry13Integrand n) u := by
    unfold chapter9Entry13Integrand
    apply ContinuousAt.mul
    · exact (continuous_pow n).continuousAt.div_const 2
    · apply ContinuousAt.div
      · exact (Real.continuous_cos.comp
          (by continuity : Continuous (fun u : ℝ => u / 2))).continuousAt
      · exact (Real.continuous_sin.comp
          (by continuity : Continuous (fun u : ℝ => u / 2))).continuousAt
      · exact hsin
  have heq : (entry13Ext n) =ᶠ[nhds u] (chapter9Entry13Integrand n) := by
    have hmem : ({0}ᶜ : Set ℝ) ∈ nhds u := compl_singleton_mem_nhds hu0
    filter_upwards [hmem] with v hv
    simp only [Set.mem_compl_iff, Set.mem_singleton_iff] at hv
    simp [entry13Ext, hv]
  exact hg.congr heq.symm

private lemma entry13Ext_continuousOn (n : ℕ) (x : ℝ) (hn : 1 ≤ n)
    (hx : |x| < 2 * Real.pi) :
    ContinuousOn (entry13Ext n) (Set.uIcc 0 x) := by
  intro u hu
  by_cases hu0 : u = 0
  · subst hu0
    exact (entry13Ext_continuousAt_zero n hn).continuousWithinAt
  · exact (entry13Ext_continuousAt_of_ne n x hx u hu hu0).continuousWithinAt

private lemma entry13_ae_eq (n : ℕ) (x : ℝ) :
    (chapter9Entry13Integrand n) =ᵐ[volume.restrict (Set.uIoc 0 x)] (entry13Ext n) := by
  change ∀ᵐ u ∂ (volume.restrict (Set.uIoc 0 x)),
    chapter9Entry13Integrand n u = entry13Ext n u
  rw [MeasureTheory.ae_iff]
  have hsub : {a | ¬ chapter9Entry13Integrand n a = entry13Ext n a} ⊆ ({0} : Set ℝ) := by
    intro u hu
    have hu : ¬ chapter9Entry13Integrand n u = entry13Ext n u := hu
    simp only [Set.mem_singleton_iff]
    by_contra hne
    exact hu (by simp [entry13Ext, hne])
  have h0 : (volume.restrict (Set.uIoc 0 x)) ({0} : Set ℝ) = 0 := by simp
  exact MeasureTheory.measure_mono_null hsub h0

private lemma entry13_intervalIntegrable (n : ℕ) (x : ℝ) (hn : 1 ≤ n)
    (hx : |x| < 2 * Real.pi) :
    IntervalIntegrable (chapter9Entry13Integrand n) volume 0 x := by
  have hF : IntervalIntegrable (entry13Ext n) volume 0 x :=
    (entry13Ext_continuousOn n x hn hx).intervalIntegrable
  exact (intervalIntegrable_congr_ae (entry13_ae_eq n x)).mpr hF

/-! ## Abel regularization: definitions -/

/-- Abel denominator `D_r(u) = 1 - 2r cos u + r^2`. -/
private def entry13D (r u : ℝ) : ℝ := 1 - 2 * r * Real.cos u + r ^ 2

/-- Closed form of the regularized `m = 1` Clausen sum. -/
private def entry13c1closed (r x : ℝ) : ℝ := -(1 / 2) * Real.log (entry13D r x)

/-- Regularized Clausen sum `∑' k, r^(k+1) T_m(x,k)`. -/
private def entry13cm (m : ℕ) (r x : ℝ) : ℝ :=
  ∑' k : ℕ, r ^ (k + 1) * chapter9ClausenTerm m x k

/-- Combined regularized value: closed form at `m = 1`, series otherwise. -/
private def entry13C (m : ℕ) (r x : ℝ) : ℝ :=
  if m = 1 then entry13c1closed r x else entry13cm m r x

/-- Poisson-type kernel `K_r(u) = r sin u / D_r(u)`. -/
private def entry13K (r u : ℝ) : ℝ := r * Real.sin u / entry13D r u

/-- Sign `s_j = (-1)^(j(j+1)/2)`. -/
private def entry13s (j : ℕ) : ℝ := (-1 : ℝ) ^ (j * (j + 1) / 2)

/-- Derivative sign: `+1` if `j+1` even, `-1` otherwise. -/
private def entry13eps (j : ℕ) : ℝ := if Even (j + 1) then 1 else -1

private lemma entry13D_eq_sq (r u : ℝ) :
    entry13D r u = (1 - r) ^ 2 + 2 * r * (1 - Real.cos u) := by
  unfold entry13D
  ring

private lemma entry13D_pos {r : ℝ} (hr0 : 0 ≤ r) (hr1 : r < 1) (u : ℝ) :
    0 < entry13D r u := by
  rw [entry13D_eq_sq]
  have h1 : 0 < (1 - r) ^ 2 := by
    have : (0 : ℝ) < 1 - r := by linarith
    positivity
  have h2 : 0 ≤ 2 * r * (1 - Real.cos u) := by
    have hcos : Real.cos u ≤ 1 := Real.cos_le_one u
    have : (0 : ℝ) ≤ 1 - Real.cos u := by linarith
    positivity
  linarith

private lemma entry13D_ne_zero {r : ℝ} (hr0 : 0 ≤ r) (hr1 : r < 1) (u : ℝ) :
    entry13D r u ≠ 0 :=
  ne_of_gt (entry13D_pos hr0 hr1 u)

private lemma entry13D_ge_two_mul (r u : ℝ) :
    2 * r * (1 - Real.cos u) ≤ entry13D r u := by
  rw [entry13D_eq_sq]
  have : (0 : ℝ) ≤ (1 - r) ^ 2 := sq_nonneg _
  linarith

/-- Half-angle identity `1 - cos u = 2 sin^2(u/2)`. -/
private lemma entry13_one_sub_cos (u : ℝ) :
    1 - Real.cos u = 2 * Real.sin (u / 2) ^ 2 := by
  have h2 : u = 2 * (u / 2) := by ring
  conv_lhs => rw [h2, Real.cos_two_mul]
  have hsq := Real.sin_sq_add_cos_sq (u / 2)
  linarith

/-! ## Helper H1: the log series (the only complex step) -/

/-- The complex point `w = r e^{ix}`. -/
private def entry13w (r x : ℝ) : ℂ := (r : ℂ) * Complex.exp ((x : ℂ) * Complex.I)

private lemma entry13w_re (r x : ℝ) : (entry13w r x).re = r * Real.cos x := by
  unfold entry13w
  rw [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
    Complex.exp_ofReal_mul_I_re, Complex.exp_ofReal_mul_I_im]
  ring

private lemma entry13w_im (r x : ℝ) : (entry13w r x).im = r * Real.sin x := by
  unfold entry13w
  rw [Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
    Complex.exp_ofReal_mul_I_re, Complex.exp_ofReal_mul_I_im]
  ring

private lemma entry13w_norm {r : ℝ} (hr0 : 0 ≤ r) (x : ℝ) :
    ‖entry13w r x‖ = r := by
  unfold entry13w
  rw [norm_mul, Complex.norm_real, Complex.norm_exp_ofReal_mul_I,
    Real.norm_of_nonneg hr0, mul_one]

private lemma entry13w_pow (r x : ℝ) (n : ℕ) :
    entry13w r x ^ n =
      ((r ^ n : ℝ) : ℂ) * Complex.exp (((((n : ℝ) * x : ℝ)) : ℂ) * Complex.I) := by
  unfold entry13w
  rw [mul_pow, ← Complex.ofReal_pow, ← Complex.exp_nat_mul]
  congr 1
  rw [Complex.ofReal_mul, Complex.ofReal_natCast]
  congr 1
  ring

private lemma entry13w_pow_div_re (r x : ℝ) (n : ℕ) :
    (entry13w r x ^ n / (n : ℂ)).re
      = r ^ n * Real.cos ((n : ℝ) * x) / (n : ℝ) := by
  by_cases hn : n = 0
  · subst hn
    simp
  · rw [entry13w_pow]
    have hcast : ((((n : ℝ))) : ℂ) = (n : ℂ) := Complex.ofReal_natCast n
    have hdiv : ((((r ^ n : ℝ)) : ℂ)
          * Complex.exp (((((n : ℝ) * x : ℝ)) : ℂ) * Complex.I) / (n : ℂ))
        = ((((r ^ n / (n : ℝ) : ℝ))) : ℂ)
          * Complex.exp (((((n : ℝ) * x : ℝ)) : ℂ) * Complex.I) := by
      rw [Complex.ofReal_div, hcast]
      ring
    rw [hdiv, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
      Complex.exp_ofReal_mul_I_re]
    simp only [zero_mul, sub_zero]
    ring

private lemma entry13_norm_one_sub_w (r x : ℝ) :
    ‖(1 : ℂ) - entry13w r x‖ ^ 2 = entry13D r x := by
  rw [Complex.sq_norm, Complex.normSq_apply]
  have hre : ((1 : ℂ) - entry13w r x).re = 1 - r * Real.cos x := by
    simp [Complex.sub_re, entry13w_re]
  have him : ((1 : ℂ) - entry13w r x).im = -(r * Real.sin x) := by
    simp [Complex.sub_im, entry13w_im]
  rw [hre, him]
  unfold entry13D
  have hsq := Real.sin_sq_add_cos_sq x
  linear_combination (r ^ 2) * hsq

private lemma entry13_neglog_re (r x : ℝ) :
    (-Complex.log (1 - entry13w r x)).re = entry13c1closed r x := by
  have hnorm : ‖(1 : ℂ) - entry13w r x‖ ^ 2 = entry13D r x :=
    entry13_norm_one_sub_w r x
  have hlog : Real.log (entry13D r x)
      = 2 * Real.log ‖(1 : ℂ) - entry13w r x‖ := by
    conv_lhs => rw [← hnorm]
    rw [Real.log_pow]
    norm_num
  rw [Complex.neg_re, Complex.log_re]
  unfold entry13c1closed
  rw [hlog]
  ring

private lemma entry13_H1_unshifted {r : ℝ} (hr0 : 0 ≤ r) (hr1 : r < 1) (x : ℝ) :
    HasSum (fun n : ℕ => r ^ n * Real.cos ((n : ℝ) * x) / (n : ℝ))
      (entry13c1closed r x) := by
  have hnorm : ‖entry13w r x‖ < 1 := by
    rw [entry13w_norm hr0 x]
    exact hr1
  have h := Complex.hasSum_taylorSeries_neg_log hnorm
  have hr := Complex.hasSum_re h
  rw [entry13_neglog_re] at hr
  have hterm : ∀ n : ℕ, r ^ n * Real.cos ((n : ℝ) * x) / (n : ℝ)
      = (entry13w r x ^ n / (n : ℂ)).re :=
    fun n => (entry13w_pow_div_re r x n).symm
  exact HasSum.congr_fun hr hterm

private lemma entry13_H1_hasSum {r : ℝ} (hr0 : 0 ≤ r) (hr1 : r < 1) (x : ℝ) :
    HasSum (fun k : ℕ => r ^ (k + 1) * chapter9ClausenTerm 1 x k)
      (entry13c1closed r x) := by
  have hr2 := entry13_H1_unshifted hr0 hr1 x
  have hshift := (hasSum_nat_add_iff'
    (f := fun n : ℕ => r ^ n * Real.cos ((n : ℝ) * x) / (n : ℝ))
    (g := entry13c1closed r x) 1).mpr hr2
  rw [Finset.sum_range_one] at hshift
  simp only [Nat.cast_zero, pow_zero, zero_mul, Real.cos_zero, div_zero,
    sub_zero] at hshift
  have hT : ∀ k : ℕ, r ^ (k + 1) * chapter9ClausenTerm 1 x k
      = r ^ (k + 1) * Real.cos (((k + 1 : ℕ) : ℝ) * x) / ((k + 1 : ℕ) : ℝ) := by
    intro k
    have hne : ¬Even (1 : ℕ) := by
      rw [Nat.even_iff]
      decide
    unfold chapter9ClausenTerm
    simp only [hne, ite_false, pow_one]
    ring
  exact HasSum.congr_fun hshift hT

private lemma entry13_H1_tsum {r : ℝ} (hr0 : 0 ≤ r) (hr1 : r < 1) (x : ℝ) :
    entry13cm 1 r x = entry13c1closed r x :=
  (entry13_H1_hasSum hr0 hr1 x).tsum_eq

/-! ## Helper H2: derivatives in `x` -/

private lemma entry13D_hasDerivAt (r x : ℝ) :
    HasDerivAt (fun x => entry13D r x) (2 * r * Real.sin x) x := by
  have hcos : HasDerivAt Real.cos (-Real.sin x) x := Real.hasDerivAt_cos x
  have hmul : HasDerivAt (fun y => 2 * r * Real.cos y)
      (2 * r * (-Real.sin x)) x :=
    HasDerivAt.const_mul (2 * r) hcos
  have h1 : HasDerivAt (fun y => 1 - 2 * r * Real.cos y)
      (0 - 2 * r * (-Real.sin x)) x :=
    (hasDerivAt_const x (1 : ℝ)).sub hmul
  have h2 : HasDerivAt (fun y => 1 - 2 * r * Real.cos y + r ^ 2)
      ((0 - 2 * r * (-Real.sin x)) + 0) x :=
    h1.add (hasDerivAt_const x (r ^ 2))
  have hderiv : (0 - 2 * r * (-Real.sin x)) + 0 = 2 * r * Real.sin x := by
    ring
  rw [hderiv] at h2
  have hfun : (fun y => 1 - 2 * r * Real.cos y + r ^ 2)
      = (fun x => entry13D r x) := by
    unfold entry13D
    rfl
  rw [hfun] at h2
  exact h2

private lemma entry13c1closed_hasDerivAt {r : ℝ} (hr0 : 0 ≤ r) (hr1 : r < 1)
    (x : ℝ) :
    HasDerivAt (fun x => entry13c1closed r x) (-entry13K r x) x := by
  have hD := entry13D_hasDerivAt r x
  have hne : entry13D r x ≠ 0 := entry13D_ne_zero hr0 hr1 x
  have hlog := hD.log hne
  have hmul := HasDerivAt.const_mul (-(1 / 2) : ℝ) hlog
  have hderiv : (-(1 / 2) : ℝ) * ((2 * r * Real.sin x) / entry13D r x)
      = -(r * Real.sin x / entry13D r x) := by
    ring
  rw [hderiv] at hmul
  have hfun : (fun y => (-(1 / 2) : ℝ) * Real.log (entry13D r y))
      = (fun x => entry13c1closed r x) := by
    unfold entry13c1closed
    rfl
  have hK : -(r * Real.sin x / entry13D r x) = -entry13K r x := by
    unfold entry13K
    rfl
  rw [hfun, hK] at hmul
  exact hmul

private lemma entry13_clausenTerm_norm_le_one (m : ℕ) (x : ℝ) (k : ℕ) :
    ‖chapter9ClausenTerm m x k‖ ≤ 1 := by
  have hbase : (1 : ℝ) ≤ (((k + 1 : ℕ) : ℝ) ^ m) := by
    apply one_le_pow₀
    have hcast : (((k + 1 : ℕ)) : ℝ) = (k : ℝ) + 1 := by push_cast; ring
    rw [hcast]
    have hnn : (0 : ℝ) ≤ (k : ℝ) := Nat.cast_nonneg k
    linarith
  have hpos := chapter9ClausenTerm_base_pos m k
  have h2 : (1 : ℝ) / ((((k + 1 : ℕ)) : ℝ) ^ m) ≤ 1 := by
    rw [div_le_one hpos]
    exact hbase
  exact le_trans (chapter9ClausenTerm_norm_bound m x k) h2

private lemma entry13_sin_term_hasDerivAt (m k : ℕ) (x : ℝ) :
    HasDerivAt
      (fun y => Real.sin (((k + 1 : ℕ) : ℝ) * y) / (((k + 1 : ℕ) : ℝ) ^ (m + 1)))
      (Real.cos (((k + 1 : ℕ) : ℝ) * x) / (((k + 1 : ℕ) : ℝ) ^ m)) x := by
  set C : ℝ := ((k + 1 : ℕ) : ℝ) with hC
  have hCpos : (0 : ℝ) < C := by
    rw [hC]
    have h0 : (0 : ℕ) < k + 1 := by omega
    exact_mod_cast h0
  have hC0 : C ≠ 0 := ne_of_gt hCpos
  have hlin : HasDerivAt (fun y : ℝ => C * y) C x := by
    have h := HasDerivAt.const_mul C (hasDerivAt_id x)
    simpa using h
  have hsin : HasDerivAt (fun y => Real.sin (C * y) / C ^ (m + 1))
      (Real.cos (C * x) * C / C ^ (m + 1)) x :=
    HasDerivAt.div_const hlin.sin (C ^ (m + 1))
  have hpow : C ^ (m + 1) = C ^ m * C := pow_succ C m
  have hCm0 : C ^ m ≠ 0 := pow_ne_zero m hC0
  have hderiv : Real.cos (C * x) * C / C ^ (m + 1)
      = Real.cos (C * x) / C ^ m := by
    rw [hpow, div_eq_div_iff (mul_ne_zero hCm0 hC0) hCm0]
    ring
  rw [hderiv] at hsin
  exact hsin

private lemma entry13_cos_term_hasDerivAt (m k : ℕ) (x : ℝ) :
    HasDerivAt
      (fun y => Real.cos (((k + 1 : ℕ) : ℝ) * y) / (((k + 1 : ℕ) : ℝ) ^ (m + 1)))
      (-(Real.sin (((k + 1 : ℕ) : ℝ) * x) / (((k + 1 : ℕ) : ℝ) ^ m))) x := by
  set C : ℝ := ((k + 1 : ℕ) : ℝ) with hC
  have hCpos : (0 : ℝ) < C := by
    rw [hC]
    have h0 : (0 : ℕ) < k + 1 := by omega
    exact_mod_cast h0
  have hC0 : C ≠ 0 := ne_of_gt hCpos
  have hlin : HasDerivAt (fun y : ℝ => C * y) C x := by
    have h := HasDerivAt.const_mul C (hasDerivAt_id x)
    simpa using h
  have hcos : HasDerivAt (fun y => Real.cos (C * y) / C ^ (m + 1))
      ((-Real.sin (C * x)) * C / C ^ (m + 1)) x :=
    HasDerivAt.div_const hlin.cos (C ^ (m + 1))
  have hpow : C ^ (m + 1) = C ^ m * C := pow_succ C m
  have hCm0 : C ^ m ≠ 0 := pow_ne_zero m hC0
  have hderiv : (-Real.sin (C * x)) * C / C ^ (m + 1)
      = -(Real.sin (C * x) / C ^ m) := by
    rw [← neg_div, hpow, div_eq_div_iff (mul_ne_zero hCm0 hC0) hCm0]
    ring
  rw [hderiv] at hcos
  exact hcos

private lemma entry13eps_eq_one_of_even (m : ℕ) (hm : Even (m + 1)) :
    entry13eps m = 1 := by
  unfold entry13eps
  simp only [hm, ite_true]

private lemma entry13eps_eq_neg_one_of_odd (m : ℕ) (hm : ¬Even (m + 1)) :
    entry13eps m = -1 := by
  unfold entry13eps
  simp only [hm, ite_false]

private lemma entry13_not_even_of_even_succ (m : ℕ) (hm : Even (m + 1)) :
    ¬Even m := by
  obtain ⟨t, ht⟩ := hm
  rintro ⟨s, hs⟩
  omega

private lemma entry13_even_of_not_even_succ (m : ℕ) (hm : ¬Even (m + 1)) :
    Even m := by
  rcases Nat.even_or_odd m with h | h
  · exact h
  · exfalso
    apply hm
    obtain ⟨s, hs⟩ := h
    exact ⟨s + 1, by omega⟩

private lemma entry13_clausenTerm_succ_hasDerivAt (m k : ℕ) (r x : ℝ) :
    HasDerivAt (fun y => r ^ (k + 1) * chapter9ClausenTerm (m + 1) y k)
      (entry13eps m * (r ^ (k + 1) * chapter9ClausenTerm m x k)) x := by
  by_cases hm : Even (m + 1)
  · have hmnot := entry13_not_even_of_even_succ m hm
    have heps := entry13eps_eq_one_of_even m hm
    rw [heps, one_mul]
    have hfun : (fun y => r ^ (k + 1) * chapter9ClausenTerm (m + 1) y k)
        = (fun y => r ^ (k + 1)
          * (Real.sin (((k + 1 : ℕ) : ℝ) * y) / (((k + 1 : ℕ) : ℝ) ^ (m + 1)))) := by
      funext y
      congr 1
      unfold chapter9ClausenTerm
      simp only [hm, ite_true]
    rw [hfun]
    have hbase := entry13_sin_term_hasDerivAt m k x
    have h := HasDerivAt.const_mul (r ^ (k + 1)) hbase
    have hderiv : r ^ (k + 1)
          * (Real.cos (((k + 1 : ℕ) : ℝ) * x) / (((k + 1 : ℕ) : ℝ) ^ m))
        = r ^ (k + 1) * chapter9ClausenTerm m x k := by
      congr 1
      unfold chapter9ClausenTerm
      simp only [hmnot, ite_false]
    rw [hderiv] at h
    exact h
  · have hme := entry13_even_of_not_even_succ m hm
    have heps := entry13eps_eq_neg_one_of_odd m hm
    rw [heps]
    have hfun : (fun y => r ^ (k + 1) * chapter9ClausenTerm (m + 1) y k)
        = (fun y => r ^ (k + 1)
          * (Real.cos (((k + 1 : ℕ) : ℝ) * y) / (((k + 1 : ℕ) : ℝ) ^ (m + 1)))) := by
      funext y
      congr 1
      unfold chapter9ClausenTerm
      simp only [hm, ite_false]
    rw [hfun]
    have hbase := entry13_cos_term_hasDerivAt m k x
    have h := HasDerivAt.const_mul (r ^ (k + 1)) hbase
    have hderiv : r ^ (k + 1)
          * (-(Real.sin (((k + 1 : ℕ) : ℝ) * x) / (((k + 1 : ℕ) : ℝ) ^ m)))
        = -1 * (r ^ (k + 1) * chapter9ClausenTerm m x k) := by
      have hT : chapter9ClausenTerm m x k
          = Real.sin (((k + 1 : ℕ) : ℝ) * x) / (((k + 1 : ℕ) : ℝ) ^ m) := by
        unfold chapter9ClausenTerm
        simp only [hme, ite_true]
      rw [hT]
      ring
    rw [hderiv] at h
    exact h

private lemma entry13_geom_succ_summable {r : ℝ} (hr0 : 0 ≤ r) (hr1 : r < 1) :
    Summable (fun k : ℕ => r ^ (k + 1)) :=
  (summable_nat_add_iff 1).mpr (summable_geometric_of_lt_one hr0 hr1)

private lemma entry13_cm_succ_hasDerivAt (m : ℕ) {r : ℝ} (hr0 : 0 ≤ r)
    (hr1 : r < 1) (x : ℝ) :
    HasDerivAt (fun y => entry13cm (m + 1) r y)
      (entry13eps m * entry13cm m r x) x := by
  have hsum := entry13_geom_succ_summable hr0 hr1
  have hterm : ∀ k (y : ℝ), HasDerivAt
      (fun y => r ^ (k + 1) * chapter9ClausenTerm (m + 1) y k)
      (entry13eps m * (r ^ (k + 1) * chapter9ClausenTerm m y k)) y :=
    fun k y => entry13_clausenTerm_succ_hasDerivAt m k r y
  have heps : ‖entry13eps m‖ = 1 := by
    unfold entry13eps
    split_ifs <;> simp
  have hbound : ∀ k (y : ℝ),
      ‖entry13eps m * (r ^ (k + 1) * chapter9ClausenTerm m y k)‖
        ≤ r ^ (k + 1) := by
    intro k y
    rw [norm_mul, heps, one_mul, norm_mul, Real.norm_eq_abs,
      abs_of_nonneg (pow_nonneg hr0 (k + 1))]
    have hT := entry13_clausenTerm_norm_le_one m y k
    have hnn : (0 : ℝ) ≤ r ^ (k + 1) := pow_nonneg hr0 _
    have hle := mul_le_mul_of_nonneg_left hT hnn
    rwa [mul_one] at hle
  have h0 : Summable
      (fun k : ℕ => r ^ (k + 1) * chapter9ClausenTerm (m + 1) 0 k) := by
    apply Summable.of_norm_bounded hsum
    intro k
    change ‖r ^ (k + 1) * chapter9ClausenTerm (m + 1) 0 k‖ ≤ r ^ (k + 1)
    rw [norm_mul, Real.norm_eq_abs,
      abs_of_nonneg (pow_nonneg hr0 (k + 1))]
    have hT := entry13_clausenTerm_norm_le_one (m + 1) 0 k
    have hnn : (0 : ℝ) ≤ r ^ (k + 1) := pow_nonneg hr0 _
    have hle := mul_le_mul_of_nonneg_left hT hnn
    rwa [mul_one] at hle
  have h := hasDerivAt_tsum (u := fun k : ℕ => r ^ (k + 1))
    (g := fun k y => r ^ (k + 1) * chapter9ClausenTerm (m + 1) y k)
    (g' := fun k y => entry13eps m * (r ^ (k + 1) * chapter9ClausenTerm m y k))
    (y₀ := (0 : ℝ)) hsum hterm hbound h0 x
  rw [tsum_mul_left] at h
  have hfun : (fun z => ∑' k : ℕ,
        r ^ (k + 1) * chapter9ClausenTerm (m + 1) z k)
      = (fun y => entry13cm (m + 1) r y) := rfl
  have hderiv : entry13eps m
        * (∑' k : ℕ, r ^ (k + 1) * chapter9ClausenTerm m x k)
      = entry13eps m * entry13cm m r x := rfl
  rw [hfun, hderiv] at h
  exact h

private lemma entry13_C_eq_cm (m : ℕ) {r : ℝ} (hr0 : 0 ≤ r) (hr1 : r < 1)
    (x : ℝ) :
    entry13C m r x = entry13cm m r x := by
  unfold entry13C
  by_cases hm : m = 1
  · subst hm
    simp only [ite_true]
    exact (entry13_H1_tsum hr0 hr1 x).symm
  · simp only [hm, ite_false]

private lemma entry13_C_one_hasDerivAt {r : ℝ} (hr0 : 0 ≤ r) (hr1 : r < 1)
    (x : ℝ) :
    HasDerivAt (fun y => entry13C 1 r y) (-entry13K r x) x := by
  have hfun : (fun y => entry13C 1 r y) = (fun y => entry13c1closed r y) := by
    funext y
    unfold entry13C
    simp only [ite_true]
  rw [hfun]
  exact entry13c1closed_hasDerivAt hr0 hr1 x

private lemma entry13_C_succ_hasDerivAt (j : ℕ) (hj : 1 ≤ j) {r : ℝ}
    (hr0 : 0 ≤ r) (hr1 : r < 1) (x : ℝ) :
    HasDerivAt (fun y => entry13C (j + 1) r y)
      (entry13eps j * entry13C j r x) x := by
  have hne : j + 1 ≠ 1 := by omega
  have hfun : (fun y => entry13C (j + 1) r y)
      = (fun y => entry13cm (j + 1) r y) := by
    funext y
    unfold entry13C
    simp only [hne, ite_false]
  rw [hfun]
  have h := entry13_cm_succ_hasDerivAt j hr0 hr1 x
  have hC : entry13cm j r x = entry13C j r x :=
    (entry13_C_eq_cm j hr0 hr1 x).symm
  rw [hC] at h
  exact h

/-! ## Helper H3: the exact identity for fixed `r` -/

private lemma entry13_odd_of_even_succ (j : ℕ) (h : Even (j + 1)) : Odd j := by
  obtain ⟨t, ht⟩ := h
  exact ⟨t - 1, by omega⟩

private lemma entry13_consec_even (j : ℕ) : Even ((j - 1) * j) := by
  rcases Nat.even_or_odd j with h | h
  · exact h.mul_left (j - 1)
  · obtain ⟨s, hs⟩ := h
    have h1 : Even (j - 1) := ⟨s, by omega⟩
    exact h1.mul_right j

private lemma entry13_tri_succ (j : ℕ) (hj : 1 ≤ j) :
    j * (j + 1) / 2 = (j - 1) * j / 2 + j := by
  obtain ⟨a, ha⟩ := entry13_consec_even j
  have h1 : j * (j + 1) = (j - 1) * j + 2 * j := by
    have h2 : j - 1 + 2 = j + 1 := by omega
    calc j * (j + 1) = (j + 1) * j := mul_comm _ _
      _ = (j - 1 + 2) * j := by rw [h2]
      _ = (j - 1) * j + 2 * j := by ring
  have hmul : j * (j + 1) = 2 * (a + j) := by
    rw [h1, ha]
    ring
  have hA : j * (j + 1) / 2 = a + j := by
    rw [hmul]
    exact Nat.mul_div_cancel_left (a + j) (by norm_num : (0 : ℕ) < 2)
  have hB : (j - 1) * j / 2 = a := by
    rw [ha, ← two_mul]
    exact Nat.mul_div_cancel_left a (by norm_num : (0 : ℕ) < 2)
  rw [hA, hB]

private lemma entry13s_succ (j : ℕ) (hj : 1 ≤ j) :
    entry13s j = entry13s (j - 1) * (-1 : ℝ) ^ j := by
  have hj1 : j - 1 + 1 = j := Nat.sub_add_cancel hj
  unfold entry13s
  rw [hj1, entry13_tri_succ j hj, pow_add]

private lemma entry13eps_eq (j : ℕ) : entry13eps j = -(-1 : ℝ) ^ j := by
  unfold entry13eps
  by_cases h : Even (j + 1)
  · simp only [h, ite_true]
    have hj : Odd j := entry13_odd_of_even_succ j h
    rw [hj.neg_one_pow, neg_neg]
  · simp only [h, ite_false]
    have hj : Even j := entry13_even_of_not_even_succ j h
    rw [hj.neg_one_pow]

private lemma entry13_sign_cancel (j : ℕ) (hj : 1 ≤ j) :
    entry13s j * entry13eps j = -entry13s (j - 1) := by
  rw [entry13s_succ j hj, entry13eps_eq j]
  have hsq : ((-1 : ℝ) ^ j) * ((-1 : ℝ) ^ j) = 1 := by
    rw [← pow_add]
    have hev : Even (j + j) := ⟨j, rfl⟩
    exact hev.neg_one_pow
  rw [mul_neg, mul_assoc, hsq, mul_one]

/-- Derivative value of `C_{j+1}`: `-K` at `j = 0`, `eps*C_j` otherwise. -/
private def entry13Cp (j : ℕ) (r x : ℝ) : ℝ :=
  if j = 0 then -entry13K r x else entry13eps j * entry13C j r x

private lemma entry13_C_hasDerivAt (j : ℕ) {r : ℝ} (hr0 : 0 ≤ r) (hr1 : r < 1)
    (x : ℝ) :
    HasDerivAt (fun y => entry13C (j + 1) r y) (entry13Cp j r x) x := by
  unfold entry13Cp
  by_cases hj : j = 0
  · subst hj
    simp only [ite_true, zero_add]
    exact entry13_C_one_hasDerivAt hr0 hr1 x
  · simp only [hj, ite_false]
    have hj1 : 1 ≤ j := Nat.one_le_iff_ne_zero.mpr hj
    exact entry13_C_succ_hasDerivAt j hj1 hr0 hr1 x

private lemma entry13_Gterm_hasDerivAt (n j : ℕ) {r : ℝ} (hr0 : 0 ≤ r)
    (hr1 : r < 1) (x : ℝ) :
    HasDerivAt
      (fun y => entry13s j * (n.factorial : ℝ) / ((n - j).factorial : ℝ)
        * y ^ (n - j) * entry13C (j + 1) r y)
      (entry13s j * (n.factorial : ℝ) / ((n - j).factorial : ℝ)
        * (((n - j : ℕ) : ℝ) * x ^ (n - j - 1) * entry13C (j + 1) r x
          + x ^ (n - j) * entry13Cp j r x)) x := by
  have hpow : HasDerivAt (fun y : ℝ => y ^ (n - j))
      (((n - j : ℕ) : ℝ) * x ^ (n - j - 1)) x :=
    hasDerivAt_pow (n - j) x
  have hA : HasDerivAt
      (fun y : ℝ => entry13s j * (n.factorial : ℝ) / ((n - j).factorial : ℝ)
        * y ^ (n - j))
      (entry13s j * (n.factorial : ℝ) / ((n - j).factorial : ℝ)
        * (((n - j : ℕ) : ℝ) * x ^ (n - j - 1))) x :=
    HasDerivAt.const_mul _ hpow
  have hC := entry13_C_hasDerivAt j hr0 hr1 x
  have h : HasDerivAt
      (fun y => (entry13s j * (n.factorial : ℝ) / ((n - j).factorial : ℝ)
        * y ^ (n - j)) * entry13C (j + 1) r y)
      ((entry13s j * (n.factorial : ℝ) / ((n - j).factorial : ℝ)
        * (((n - j : ℕ) : ℝ) * x ^ (n - j - 1))) * entry13C (j + 1) r x
        + (entry13s j * (n.factorial : ℝ) / ((n - j).factorial : ℝ) * x ^ (n - j))
          * entry13Cp j r x) x :=
    HasDerivAt.fun_mul hA hC
  have hderiv : (entry13s j * (n.factorial : ℝ) / ((n - j).factorial : ℝ)
        * (((n - j : ℕ) : ℝ) * x ^ (n - j - 1))) * entry13C (j + 1) r x
        + (entry13s j * (n.factorial : ℝ) / ((n - j).factorial : ℝ) * x ^ (n - j))
          * entry13Cp j r x
      = entry13s j * (n.factorial : ℝ) / ((n - j).factorial : ℝ)
        * (((n - j : ℕ) : ℝ) * x ^ (n - j - 1) * entry13C (j + 1) r x
          + x ^ (n - j) * entry13Cp j r x) := by
    ring
  rw [hderiv] at h
  exact h

private lemma entry13_cancel_pair (n j : ℕ) (hj : j < n) {r : ℝ} (x : ℝ) :
    (entry13s j * (n.factorial : ℝ) / ((n - j).factorial : ℝ)
        * (((n - j : ℕ) : ℝ) * x ^ (n - j - 1) * entry13C (j + 1) r x)
      + entry13s (j + 1) * (n.factorial : ℝ) / ((n - (j + 1)).factorial : ℝ)
        * (x ^ (n - (j + 1)) * entry13Cp (j + 1) r x)) = 0 := by
  have hCp : entry13Cp (j + 1) r x
      = entry13eps (j + 1) * entry13C (j + 1) r x := by
    unfold entry13Cp
    have hne : j + 1 ≠ 0 := by omega
    simp only [hne, ite_false]
  rw [hCp]
  have hnm : n - (j + 1) = n - j - 1 := by omega
  rw [hnm]
  obtain ⟨m, hm⟩ : ∃ m, n - j = m + 1 := ⟨n - j - 1, by omega⟩
  have hfact : (n - j).factorial = (n - j) * (n - j - 1).factorial := by
    rw [hm, Nat.factorial_succ, Nat.add_sub_cancel]
  have hfactR : ((n - j).factorial : ℝ)
      = ((n - j : ℕ) : ℝ) * ((n - j - 1).factorial : ℝ) := by
    exact_mod_cast hfact
  have hnpos : 1 ≤ n - j := by omega
  have hd0 : ((n - j : ℕ) : ℝ) ≠ 0 := by
    have h1 : (1 : ℝ) ≤ ((n - j : ℕ) : ℝ) := by exact_mod_cast hnpos
    have h0 : (0 : ℝ) < ((n - j : ℕ) : ℝ) := by linarith
    exact ne_of_gt h0
  have hg0 : ((n - j - 1).factorial : ℝ) ≠ 0 := by
    have hpos : 0 < ((n - j - 1).factorial : ℝ) := by
      exact_mod_cast Nat.factorial_pos _
    exact ne_of_gt hpos
  have hsign : entry13s (j + 1) * entry13eps (j + 1) = -entry13s j := by
    have h := entry13_sign_cancel (j + 1) (by omega)
    rwa [Nat.add_sub_cancel] at h
  have hfactor : (entry13s j * (n.factorial : ℝ) / ((n - j).factorial : ℝ)
          * (((n - j : ℕ) : ℝ) * x ^ (n - j - 1) * entry13C (j + 1) r x)
        + entry13s (j + 1) * (n.factorial : ℝ) / ((n - j - 1).factorial : ℝ)
          * (x ^ (n - j - 1)
            * (entry13eps (j + 1) * entry13C (j + 1) r x)))
      = x ^ (n - j - 1) * entry13C (j + 1) r x
        * ((entry13s j * (n.factorial : ℝ) / ((n - j).factorial : ℝ))
            * ((n - j : ℕ) : ℝ)
          + (entry13s (j + 1) * (n.factorial : ℝ)
            / ((n - j - 1).factorial : ℝ)) * entry13eps (j + 1)) := by
    ring
  rw [hfactor]
  have hbracket : (entry13s j * (n.factorial : ℝ) / ((n - j).factorial : ℝ))
          * ((n - j : ℕ) : ℝ)
        + (entry13s (j + 1) * (n.factorial : ℝ)
          / ((n - j - 1).factorial : ℝ)) * entry13eps (j + 1)
      = 0 := by
    have h1 : (entry13s j * (n.factorial : ℝ) / ((n - j).factorial : ℝ))
            * ((n - j : ℕ) : ℝ)
        = entry13s j * (n.factorial : ℝ) / ((n - j - 1).factorial : ℝ) := by
      rw [hfactR, div_mul_eq_mul_div,
        div_eq_div_iff (mul_ne_zero hd0 hg0) hg0]
      ring
    rw [h1]
    have h2 : (entry13s (j + 1) * (n.factorial : ℝ)
            / ((n - j - 1).factorial : ℝ)) * entry13eps (j + 1)
        = (entry13s (j + 1) * entry13eps (j + 1)) * (n.factorial : ℝ)
          / ((n - j - 1).factorial : ℝ) := by
      ring
    rw [h2, hsign]
    ring
  rw [hbracket, mul_zero]

private def entry13G (n : ℕ) (r x : ℝ) : ℝ :=
  -∑ j ∈ Finset.range (n + 1),
    entry13s j * (n.factorial : ℝ) / ((n - j).factorial : ℝ)
      * x ^ (n - j) * entry13C (j + 1) r x

private lemma entry13_G_hasDerivAt (n : ℕ) {r : ℝ} (hr0 : 0 ≤ r) (hr1 : r < 1)
    (x : ℝ) :
    HasDerivAt (fun y => entry13G n r y) (x ^ n * entry13K r x) x := by
  have hterm : ∀ j ∈ Finset.range (n + 1), HasDerivAt
      (fun y => entry13s j * (n.factorial : ℝ) / ((n - j).factorial : ℝ)
        * y ^ (n - j) * entry13C (j + 1) r y)
      (entry13s j * (n.factorial : ℝ) / ((n - j).factorial : ℝ)
        * (((n - j : ℕ) : ℝ) * x ^ (n - j - 1) * entry13C (j + 1) r x
          + x ^ (n - j) * entry13Cp j r x)) x :=
    fun j _ => entry13_Gterm_hasDerivAt n j hr0 hr1 x
  have hsum := HasDerivAt.sum hterm
  have hneg := hsum.neg
  have hfun : (-(∑ j ∈ Finset.range (n + 1),
      (fun y => entry13s j * (n.factorial : ℝ) / ((n - j).factorial : ℝ)
        * y ^ (n - j) * entry13C (j + 1) r y)))
      = (fun y => entry13G n r y) := by
    funext y
    unfold entry13G
    simp only [Pi.neg_apply, Finset.sum_apply]
  rw [hfun] at hneg
  have hPn : entry13s n * (n.factorial : ℝ) / ((n - n).factorial : ℝ)
        * (((n - n : ℕ) : ℝ) * x ^ (n - n - 1) * entry13C (n + 1) r x)
      = 0 := by
    have h0 : ((n - n : ℕ) : ℝ) = 0 := by simp
    simp only [h0, zero_mul, mul_zero]
  have hQ0 : entry13s 0 * (n.factorial : ℝ) / ((n - 0).factorial : ℝ)
        * (x ^ (n - 0) * entry13Cp 0 r x)
      = -(x ^ n * entry13K r x) := by
    have hs0 : entry13s 0 = 1 := by
      unfold entry13s
      simp
    have hCp0 : entry13Cp 0 r x = -entry13K r x := by
      unfold entry13Cp
      simp only [ite_true]
    have hfn0 : (n.factorial : ℝ) ≠ 0 := by
      exact_mod_cast Nat.factorial_ne_zero n
    rw [hs0, hCp0, Nat.sub_zero, one_mul, div_self hfn0, one_mul]
    ring
  have hpair : ∀ j ∈ Finset.range n,
      (entry13s j * (n.factorial : ℝ) / ((n - j).factorial : ℝ)
          * (((n - j : ℕ) : ℝ) * x ^ (n - j - 1) * entry13C (j + 1) r x)
        + entry13s (j + 1) * (n.factorial : ℝ) / ((n - (j + 1)).factorial : ℝ)
          * (x ^ (n - (j + 1)) * entry13Cp (j + 1) r x)) = 0 := by
    intro j hj
    have hjn : j < n := Finset.mem_range.mp hj
    exact entry13_cancel_pair n j hjn x
  have hderiv : -(∑ j ∈ Finset.range (n + 1),
        entry13s j * (n.factorial : ℝ) / ((n - j).factorial : ℝ)
          * (((n - j : ℕ) : ℝ) * x ^ (n - j - 1) * entry13C (j + 1) r x
            + x ^ (n - j) * entry13Cp j r x))
      = x ^ n * entry13K r x := by
    simp only [left_distrib]
    rw [Finset.sum_add_distrib]
    have hP : (∑ j ∈ Finset.range (n + 1),
            entry13s j * (n.factorial : ℝ) / ((n - j).factorial : ℝ)
              * (((n - j : ℕ) : ℝ) * x ^ (n - j - 1) * entry13C (j + 1) r x))
          = ∑ j ∈ Finset.range n,
            entry13s j * (n.factorial : ℝ) / ((n - j).factorial : ℝ)
              * (((n - j : ℕ) : ℝ) * x ^ (n - j - 1) * entry13C (j + 1) r x) := by
      rw [Finset.sum_range_succ _ n, hPn, add_zero]
    have hQ : (∑ j ∈ Finset.range (n + 1),
            entry13s j * (n.factorial : ℝ) / ((n - j).factorial : ℝ)
              * (x ^ (n - j) * entry13Cp j r x))
          = (∑ j ∈ Finset.range n,
              entry13s (j + 1) * (n.factorial : ℝ)
                / ((n - (j + 1)).factorial : ℝ)
                * (x ^ (n - (j + 1)) * entry13Cp (j + 1) r x))
            + entry13s 0 * (n.factorial : ℝ) / ((n - 0).factorial : ℝ)
              * (x ^ (n - 0) * entry13Cp 0 r x) :=
      Finset.sum_range_succ' _ n
    rw [hP, hQ, hQ0]
    have hpair0 : (∑ j ∈ Finset.range n,
              entry13s j * (n.factorial : ℝ) / ((n - j).factorial : ℝ)
                * (((n - j : ℕ) : ℝ) * x ^ (n - j - 1) * entry13C (j + 1) r x))
            + (∑ j ∈ Finset.range n,
              entry13s (j + 1) * (n.factorial : ℝ)
                / ((n - (j + 1)).factorial : ℝ)
                * (x ^ (n - (j + 1)) * entry13Cp (j + 1) r x)) = 0 := by
      rw [← Finset.sum_add_distrib]
      trans ∑ _j ∈ Finset.range n, (0 : ℝ)
      · exact Finset.sum_congr rfl hpair
      · exact Finset.sum_const_zero
    linarith [hpair0]
  rw [hderiv] at hneg
  exact hneg

private lemma entry13_G_zero (n : ℕ) (r : ℝ) :
    entry13G n r 0
      = -(entry13s n * (n.factorial : ℝ) * entry13C (n + 1) r 0) := by
  have h0 : (∑ j ∈ Finset.range n,
        entry13s j * (n.factorial : ℝ) / ((n - j).factorial : ℝ)
          * (0 : ℝ) ^ (n - j) * entry13C (j + 1) r 0) = 0 := by
    trans ∑ _j ∈ Finset.range n, (0 : ℝ)
    · apply Finset.sum_congr rfl
      intro j hj
      have hjn : j < n := Finset.mem_range.mp hj
      have hne : n - j ≠ 0 := by omega
      have hpow : (0 : ℝ) ^ (n - j) = 0 := zero_pow hne
      simp only [hpow, mul_zero, zero_mul]
    · exact Finset.sum_const_zero
  unfold entry13G
  rw [Finset.sum_range_succ _ n, h0, zero_add]
  have hnn : n - n = 0 := Nat.sub_self n
  rw [hnn]
  simp only [pow_zero, Nat.factorial_zero, Nat.cast_one, div_one, mul_one]

private lemma entry13K_continuous {r : ℝ} (hr0 : 0 ≤ r) (hr1 : r < 1) :
    Continuous (fun u => entry13K r u) := by
  unfold entry13K entry13D
  apply Continuous.div
  · continuity
  · continuity
  · intro u
    exact entry13D_ne_zero hr0 hr1 u

private lemma entry13_powK_intervalIntegrable (n : ℕ) {r : ℝ} (hr0 : 0 ≤ r)
    (hr1 : r < 1) (x : ℝ) :
    IntervalIntegrable (fun u => u ^ n * entry13K r u) MeasureTheory.volume 0 x :=
  ((continuous_pow n).mul (entry13K_continuous hr0 hr1)).continuousOn.intervalIntegrable

private lemma entry13_H3_identity (n : ℕ) {r : ℝ} (hr0 : 0 ≤ r) (hr1 : r < 1)
    (x : ℝ) :
    (∫ u in (0 : ℝ)..x, u ^ n * entry13K r u)
      = entry13s n * (n.factorial : ℝ) * entry13C (n + 1) r 0
        - ∑ j ∈ Finset.range (n + 1),
          entry13s j * (n.factorial : ℝ) / ((n - j).factorial : ℝ)
            * x ^ (n - j) * entry13C (j + 1) r x := by
  have hderiv : ∀ y ∈ Set.uIcc (0 : ℝ) x,
      HasDerivAt (fun y => entry13G n r y) (y ^ n * entry13K r y) y :=
    fun y _ => entry13_G_hasDerivAt n hr0 hr1 y
  have hint := entry13_powK_intervalIntegrable n hr0 hr1 x
  have hFTC : (∫ u in (0 : ℝ)..x, u ^ n * entry13K r u)
      = entry13G n r x - entry13G n r 0 :=
    intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv hint
  rw [entry13_G_zero] at hFTC
  unfold entry13G at hFTC
  linear_combination hFTC

/-! ## Step 4a: the left-side limit by dominated convergence -/

private lemma entry13_eventually_mem_Ioo :
    ∀ᶠ r in nhdsWithin (1 : ℝ) (Set.Iio 1), r ∈ Set.Ioo (0 : ℝ) 1 := by
  have h1 : ∀ᶠ r in nhdsWithin (1 : ℝ) (Set.Iio 1), r < 1 :=
    self_mem_nhdsWithin
  have h0 : ∀ᶠ r in nhdsWithin (1 : ℝ) (Set.Iio 1), 0 < r :=
    (eventually_gt_nhds (show (0 : ℝ) < 1 by norm_num)).filter_mono
      nhdsWithin_le_nhds
  filter_upwards [h0, h1] with r hr0 hr1
  exact ⟨hr0, hr1⟩

private lemma entry13_abs_le_of_mem_uIcc {x u : ℝ} (hu : u ∈ Set.uIcc 0 x) :
    |u| ≤ |x| := by
  rw [Set.mem_uIcc] at hu
  rcases hu with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · by_cases hxnn : 0 ≤ x
    · calc |u| = u := abs_of_nonneg (by linarith)
        _ ≤ x := h2
        _ = |x| := (abs_of_nonneg hxnn).symm
    · have hxlt : x < 0 := lt_of_not_ge hxnn
      linarith
  · by_cases hxnn : x ≤ 0
    · calc |u| = -u := abs_of_nonpos (by linarith)
        _ ≤ -x := by linarith
        _ = |x| := (abs_of_nonpos hxnn).symm
    · have hxlt : 0 < x := lt_of_not_ge hxnn
      linarith

private lemma entry13_tendsto_D (u : ℝ) :
    Filter.Tendsto (fun r : ℝ => entry13D r u) (nhdsWithin 1 (Set.Iio 1))
      (𝓝 (2 - 2 * Real.cos u)) := by
  have hcont : Continuous (fun r : ℝ => entry13D r u) := by
    unfold entry13D
    continuity
  have h1 : entry13D 1 u = 2 - 2 * Real.cos u := by
    unfold entry13D
    ring
  have h : Filter.Tendsto (fun r : ℝ => entry13D r u)
      (nhdsWithin 1 (Set.Iio 1)) (𝓝 (entry13D 1 u)) :=
    (hcont.tendsto 1).mono_left nhdsWithin_le_nhds
  rwa [h1] at h

private lemma entry13_two_sub_cos_pos {x u : ℝ} (hx : |x| < 2 * Real.pi)
    (hu : u ∈ Set.uIcc 0 x) (hu0 : u ≠ 0) :
    0 < 2 - 2 * Real.cos u := by
  have habs : |u| < 2 * Real.pi :=
    lt_of_le_of_lt (entry13_abs_le_of_mem_uIcc hu) hx
  obtain ⟨hlo, hhi⟩ := abs_lt.mp habs
  have hiff := Real.cos_eq_one_iff_of_lt_of_lt hlo hhi
  have hne : Real.cos u ≠ 1 := by
    intro hcon
    rw [hiff] at hcon
    exact hu0 hcon
  have hle : Real.cos u ≤ 1 := Real.cos_le_one u
  have hlt : Real.cos u < 1 := lt_of_le_of_ne hle hne
  linarith

private lemma entry13_tendsto_K {x u : ℝ} (hx : |x| < 2 * Real.pi)
    (hu : u ∈ Set.uIcc 0 x) (hu0 : u ≠ 0) :
    Filter.Tendsto (fun r : ℝ => entry13K r u) (nhdsWithin 1 (Set.Iio 1))
      (𝓝 (Real.sin u / (2 - 2 * Real.cos u))) := by
  have hD := entry13_tendsto_D u
  have hpos := entry13_two_sub_cos_pos hx hu hu0
  have hne : (2 : ℝ) - 2 * Real.cos u ≠ 0 := ne_of_gt hpos
  have hnum : Filter.Tendsto (fun r : ℝ => r * Real.sin u)
      (nhdsWithin 1 (Set.Iio 1)) (𝓝 (1 * Real.sin u)) := by
    have hc : Continuous (fun _ : ℝ => Real.sin u) := continuous_const
    exact ((continuous_id.mul hc).tendsto 1).mono_left nhdsWithin_le_nhds
  have hdiv : Filter.Tendsto (fun r : ℝ => r * Real.sin u / entry13D r u)
      (nhdsWithin 1 (Set.Iio 1))
      (𝓝 (1 * Real.sin u / (2 - 2 * Real.cos u))) :=
    hnum.div hD hne
  have hfun : (fun r : ℝ => r * Real.sin u / entry13D r u)
      = (fun r => entry13K r u) := by
    funext r
    unfold entry13K
    rfl
  have hval : (1 : ℝ) * Real.sin u / (2 - 2 * Real.cos u)
      = Real.sin u / (2 - 2 * Real.cos u) := by
    rw [one_mul]
  rw [hfun, hval] at hdiv
  exact hdiv

private lemma entry13_dominated (n : ℕ) {r u : ℝ} (hr : r ∈ Set.Ioo (0 : ℝ) 1) :
    ‖u ^ n * entry13K r u‖ ≤ ‖chapter9Entry13Integrand n u‖ := by
  have hr0 : 0 < r := hr.1
  have hr1 : r < 1 := hr.2
  have hDpos : 0 < entry13D r u := entry13D_pos hr0.le hr1 u
  have hDge : 4 * r * Real.sin (u / 2) ^ 2 ≤ entry13D r u := by
    have h1 := entry13D_ge_two_mul r u
    rw [entry13_one_sub_cos] at h1
    have heq : 2 * r * (2 * Real.sin (u / 2) ^ 2)
        = 4 * r * Real.sin (u / 2) ^ 2 := by ring
    rwa [heq] at h1
  by_cases hs : Real.sin (u / 2) = 0
  · have hsin : Real.sin u = 0 := by
      conv_lhs => rw [show u = 2 * (u / 2) from by ring, Real.sin_two_mul]
      rw [hs]
      ring
    have hK : entry13K r u = 0 := by
      unfold entry13K
      rw [hsin, mul_zero, zero_div]
    rw [hK, mul_zero, norm_zero]
    exact norm_nonneg _
  · have habs_pos : (0 : ℝ) < |Real.sin (u / 2)| := abs_pos.mpr hs
    have hsq_pos : (0 : ℝ) < Real.sin (u / 2) ^ 2 := by
      have h1 : (0 : ℝ) < |Real.sin (u / 2)| ^ 2 := pow_pos habs_pos 2
      rwa [sq_abs] at h1
    have h4pos : (0 : ℝ) < 4 * r * Real.sin (u / 2) ^ 2 := by positivity
    have hle : (r * |Real.sin u|) / entry13D r u
        ≤ (r * |Real.sin u|) / (4 * r * Real.sin (u / 2) ^ 2) := by
      have hnn : (0 : ℝ) ≤ r * |Real.sin u| := by positivity
      have hdiv : 1 / entry13D r u ≤ 1 / (4 * r * Real.sin (u / 2) ^ 2) :=
        one_div_le_one_div_of_le h4pos hDge
      calc (r * |Real.sin u|) / entry13D r u
          = (r * |Real.sin u|) * (1 / entry13D r u) := by
            rw [div_eq_mul_one_div]
        _ ≤ (r * |Real.sin u|) * (1 / (4 * r * Real.sin (u / 2) ^ 2)) :=
            mul_le_mul_of_nonneg_left hdiv hnn
        _ = (r * |Real.sin u|) / (4 * r * Real.sin (u / 2) ^ 2) :=
            (div_eq_mul_one_div _ _).symm
    have hcancel : r * |Real.sin u| / (4 * r * Real.sin (u / 2) ^ 2)
        = |Real.sin u| / (4 * Real.sin (u / 2) ^ 2) := by
      have h1 : (4 : ℝ) * r * Real.sin (u / 2) ^ 2 ≠ 0 := ne_of_gt h4pos
      have h2 : (4 : ℝ) * Real.sin (u / 2) ^ 2 ≠ 0 :=
        ne_of_gt (by positivity)
      rw [div_eq_div_iff h1 h2]
      ring
    have hsin2 : |Real.sin u|
        = 2 * |Real.sin (u / 2)| * |Real.cos (u / 2)| := by
      have habs2 : |(2 : ℝ)| = 2 := by norm_num
      conv_lhs => rw [show u = 2 * (u / 2) from by ring, Real.sin_two_mul]
      rw [abs_mul, abs_mul, habs2]
    have hfinal : |Real.sin u| / (4 * Real.sin (u / 2) ^ 2)
        = |Real.cos (u / 2)| / (2 * |Real.sin (u / 2)|) := by
      rw [hsin2, ← sq_abs (Real.sin (u / 2))]
      have hsq2 : (0 : ℝ) < |Real.sin (u / 2)| ^ 2 := pow_pos habs_pos 2
      have h1 : (4 : ℝ) * |Real.sin (u / 2)| ^ 2 ≠ 0 := ne_of_gt (by positivity)
      have h2 : (2 : ℝ) * |Real.sin (u / 2)| ≠ 0 := ne_of_gt (by positivity)
      rw [div_eq_div_iff h1 h2]
      ring
    have e2 : (r * |Real.sin u| / entry13D r u)
        ≤ |Real.cos (u / 2)| / (2 * |Real.sin (u / 2)|) := by
      rw [hcancel] at hle
      exact hle.trans_eq hfinal
    have e1 : |u ^ n * entry13K r u|
        = |u| ^ n * (r * |Real.sin u| / entry13D r u) := by
      unfold entry13K
      rw [abs_mul, abs_pow, abs_div, abs_mul, abs_of_pos hr0, abs_of_pos hDpos]
    have e3 : |chapter9Entry13Integrand n u|
        = |u| ^ n * (|Real.cos (u / 2)| / (2 * |Real.sin (u / 2)|)) := by
      unfold chapter9Entry13Integrand
      have habs2 : |(2 : ℝ)| = 2 := by norm_num
      rw [abs_mul, abs_div, abs_div, abs_pow, habs2]
      ring
    rw [Real.norm_eq_abs, Real.norm_eq_abs, e1, e3]
    exact mul_le_mul_of_nonneg_left e2 (pow_nonneg (abs_nonneg u) n)

private lemma entry13_K_limit_value (n : ℕ) {x u : ℝ} (hx : |x| < 2 * Real.pi)
    (hu : u ∈ Set.uIoc 0 x) (hu0 : u ≠ 0) :
    u ^ n * (Real.sin u / (2 - 2 * Real.cos u))
      = chapter9Entry13Integrand n u := by
  have huIcc : u ∈ Set.uIcc 0 x := Set.uIoc_subset_uIcc hu
  have hs0 : Real.sin (u / 2) ≠ 0 := sin_half_ne_zero_of_mem hx huIcc hu0
  have hsin : Real.sin u = 2 * Real.sin (u / 2) * Real.cos (u / 2) := by
    conv_lhs => rw [show u = 2 * (u / 2) from by ring, Real.sin_two_mul]
  have hcos : 2 - 2 * Real.cos u = 4 * Real.sin (u / 2) ^ 2 := by
    have h := entry13_one_sub_cos u
    linarith
  have hs2 : Real.sin (u / 2) ^ 2 ≠ 0 := pow_ne_zero 2 hs0
  have h1 : (4 : ℝ) * Real.sin (u / 2) ^ 2 ≠ 0 :=
    mul_ne_zero (by norm_num) hs2
  have h2 : (2 : ℝ) * Real.sin (u / 2) ≠ 0 :=
    mul_ne_zero two_ne_zero hs0
  unfold chapter9Entry13Integrand
  rw [hsin, hcos, ← mul_div_assoc, div_mul_div_comm, div_eq_div_iff h1 h2]
  ring

private lemma entry13_tendsto_integral (n : ℕ) (x : ℝ) (hn : 1 ≤ n)
    (hx : |x| < 2 * Real.pi) :
    Filter.Tendsto (fun r : ℝ => ∫ u in (0 : ℝ)..x, u ^ n * entry13K r u)
      (nhdsWithin 1 (Set.Iio 1))
      (𝓝 (∫ u in (0 : ℝ)..x, chapter9Entry13Integrand n u)) := by
  apply intervalIntegral.tendsto_integral_filter_of_dominated_convergence
    (fun u => ‖chapter9Entry13Integrand n u‖)
  · filter_upwards [entry13_eventually_mem_Ioo] with r hr
    have hcont : Continuous (fun u => u ^ n * entry13K r u) :=
      (continuous_pow n).mul (entry13K_continuous hr.1.le hr.2)
    exact hcont.continuousOn.aestronglyMeasurable measurableSet_uIoc
  · filter_upwards [entry13_eventually_mem_Ioo] with r hr
    filter_upwards [MeasureTheory.Measure.ae_ne volume (0 : ℝ)] with u _hu0
    intro _
    exact entry13_dominated n hr
  · exact (entry13_intervalIntegrable n x hn hx).norm
  · filter_upwards [MeasureTheory.Measure.ae_ne volume (0 : ℝ)] with u hu0
    intro hu
    have huIcc : u ∈ Set.uIcc 0 x := Set.uIoc_subset_uIcc hu
    have hK := entry13_tendsto_K hx huIcc hu0
    have hlim : Filter.Tendsto (fun r : ℝ => u ^ n * entry13K r u)
        (nhdsWithin 1 (Set.Iio 1))
        (𝓝 (u ^ n * (Real.sin u / (2 - 2 * Real.cos u)))) :=
      tendsto_const_nhds.mul hK
    rwa [entry13_K_limit_value n hx hu hu0] at hlim

/-! ## Step 4b: limits of the regularized Clausen sums -/

private lemma entry13_cm_tendsto (m : ℕ) (hm : 2 ≤ m) (x : ℝ) :
    Filter.Tendsto (fun r : ℝ => entry13cm m r x)
      (nhdsWithin 1 (Set.Iio 1)) (𝓝 (chapter9Clausen m x)) := by
  have hf : ∀ k : ℕ, ContinuousOn
      (fun r : ℝ => r ^ (k + 1) * chapter9ClausenTerm m x k) (Set.Icc 0 1) :=
    fun k => ((continuous_pow (k + 1)).mul continuous_const).continuousOn
  have hu : Summable (fun k : ℕ => (1 : ℝ) / ((((k + 1 : ℕ)) : ℝ) ^ m)) :=
    chapter9ClausenTerm_shift_summable m hm
  have hfu : ∀ k (r : ℝ), r ∈ Set.Icc 0 1 →
      ‖r ^ (k + 1) * chapter9ClausenTerm m x k‖
        ≤ (1 : ℝ) / ((((k + 1 : ℕ)) : ℝ) ^ m) := by
    intro k r hr
    have hr0 : 0 ≤ r := hr.1
    have hr1 : r ≤ 1 := hr.2
    have hpow : ‖r ^ (k + 1)‖ ≤ 1 := by
      rw [Real.norm_eq_abs, abs_of_nonneg (pow_nonneg hr0 _)]
      exact pow_le_one₀ hr0 hr1
    have hT := chapter9ClausenTerm_norm_bound m x k
    have hnn : (0 : ℝ) ≤ ‖chapter9ClausenTerm m x k‖ := norm_nonneg _
    calc ‖r ^ (k + 1) * chapter9ClausenTerm m x k‖
        = ‖r ^ (k + 1)‖ * ‖chapter9ClausenTerm m x k‖ := norm_mul _ _
      _ ≤ 1 * ‖chapter9ClausenTerm m x k‖ :=
          mul_le_mul_of_nonneg_right hpow hnn
      _ ≤ 1 * ((1 : ℝ) / ((((k + 1 : ℕ)) : ℝ) ^ m)) :=
          mul_le_mul_of_nonneg_left hT (by norm_num)
      _ = (1 : ℝ) / ((((k + 1 : ℕ)) : ℝ) ^ m) := one_mul _
  have h := continuousOn_tsum hf hu hfu
  have hfun : (fun r => ∑' k : ℕ, r ^ (k + 1) * chapter9ClausenTerm m x k)
      = (fun r => entry13cm m r x) := rfl
  rw [hfun] at h
  have hmem : (1 : ℝ) ∈ Set.Icc (0 : ℝ) 1 :=
    Set.mem_Icc.mpr ⟨zero_le_one, le_rfl⟩
  have htend : Filter.Tendsto (fun r : ℝ => entry13cm m r x)
      (nhdsWithin 1 (Set.Icc 0 1)) (𝓝 (entry13cm m 1 x)) :=
    h.continuousWithinAt hmem
  have hval : entry13cm m 1 x = chapter9Clausen m x := by
    unfold entry13cm chapter9Clausen
    have hm0 : ¬m = 0 := by omega
    have hm1 : ¬m = 1 := by omega
    simp only [hm0, hm1, ite_false]
    apply tsum_congr
    intro k
    rw [one_pow, one_mul]
  rw [hval] at htend
  have hIoo_le : nhdsWithin (1 : ℝ) (Set.Ioo 0 1)
      ≤ nhdsWithin (1 : ℝ) (Set.Icc 0 1) :=
    nhdsWithin_mono 1 Set.Ioo_subset_Icc_self
  have htend2 := htend.mono_left hIoo_le
  have hfilter : nhdsWithin (1 : ℝ) (Set.Iio 1)
      = nhdsWithin (1 : ℝ) (Set.Ioo 0 1) := by
    have hmemIoi : (1 : ℝ) ∈ Set.Ioi (0 : ℝ) :=
      Set.mem_Ioi.mpr (show (0 : ℝ) < 1 by norm_num)
    have hinter : Set.Iio (1 : ℝ) ∩ Set.Ioi 0 = Set.Ioo 0 1 ∩ Set.Ioi 0 := by
      ext r
      simp only [Set.mem_inter_iff, Set.mem_Iio, Set.mem_Ioi, Set.mem_Ioo]
      tauto
    exact nhdsWithin_eq_nhdsWithin hmemIoi isOpen_Ioi hinter
  rwa [← hfilter] at htend2

private lemma entry13_C_tendsto (j : ℕ) (hj : 1 ≤ j) (x : ℝ) :
    Filter.Tendsto (fun r : ℝ => entry13C (j + 1) r x)
      (nhdsWithin 1 (Set.Iio 1)) (𝓝 (chapter9Clausen (j + 1) x)) := by
  have hfun : (fun r : ℝ => entry13C (j + 1) r x)
      = (fun r : ℝ => entry13cm (j + 1) r x) := by
    funext r
    unfold entry13C
    have h : j + 1 ≠ 1 := by omega
    simp only [h, ite_false]
  rw [hfun]
  have hm : 2 ≤ j + 1 := by omega
  exact entry13_cm_tendsto (j + 1) hm x

/-! ## Step 4c: limit of the closed-form logarithm -/

private lemma entry13_c1closed_tendsto (x : ℝ) (hx0 : x ≠ 0)
    (hx : |x| < 2 * Real.pi) :
    Filter.Tendsto (fun r : ℝ => entry13c1closed r x)
      (nhdsWithin 1 (Set.Iio 1)) (𝓝 (chapter9Clausen 1 x)) := by
  have hxmem : x ∈ Set.uIcc 0 x := Set.right_mem_uIcc
  have hD := entry13_tendsto_D x
  have hpos : 0 < 2 - 2 * Real.cos x :=
    entry13_two_sub_cos_pos hx hxmem hx0
  have hlog : Filter.Tendsto (fun r : ℝ => Real.log (entry13D r x))
      (nhdsWithin 1 (Set.Iio 1)) (𝓝 (Real.log (2 - 2 * Real.cos x))) :=
    (Real.continuousAt_log (ne_of_gt hpos)).tendsto.comp hD
  have hmul : Filter.Tendsto (fun r : ℝ => -(1 / 2) * Real.log (entry13D r x))
      (nhdsWithin 1 (Set.Iio 1))
      (𝓝 (-(1 / 2) * Real.log (2 - 2 * Real.cos x))) :=
    tendsto_const_nhds.mul hlog
  have hfun : (fun r : ℝ => -(1 / 2) * Real.log (entry13D r x))
      = (fun r => entry13c1closed r x) := by
    funext r
    unfold entry13c1closed
    rfl
  rw [hfun] at hmul
  have hsq : 2 - 2 * Real.cos x = (2 * Real.sin (x / 2)) ^ 2 := by
    have h := entry13_one_sub_cos x
    have h2 : (2 * Real.sin (x / 2)) ^ 2 = 4 * Real.sin (x / 2) ^ 2 := by ring
    linarith
  have hval : -(1 / 2 : ℝ) * Real.log (2 - 2 * Real.cos x)
      = chapter9Clausen 1 x := by
    unfold chapter9Clausen
    have h10 : ¬(1 : ℕ) = 0 := one_ne_zero
    simp only [h10, ite_false, ite_true]
    rw [hsq, Real.log_pow]
    have h2 : ((2 : ℕ) : ℝ) = 2 := by norm_num
    rw [h2, Real.log_abs]
    ring
  rw [hval] at hmul
  exact hmul

/-! ## Step 4d: the constant term -/

private lemma entry13_clausen_zero_of_odd (n : ℕ) (hn : 1 ≤ n) (hodd : Odd n) :
    chapter9Clausen (n + 1) 0 = 0 := by
  have hne0 : n + 1 ≠ 0 := by omega
  have hne1 : n + 1 ≠ 1 := by omega
  have hev : Even (n + 1) := hodd.add_one
  unfold chapter9Clausen
  simp only [hne0, hne1, ite_false]
  have hT : ∀ k : ℕ, chapter9ClausenTerm (n + 1) 0 k = 0 := by
    intro k
    unfold chapter9ClausenTerm
    simp only [hev, ite_true, mul_zero, Real.sin_zero, zero_div]
  trans ∑' _k : ℕ, (0 : ℝ)
  · exact tsum_congr hT
  · exact tsum_zero

private lemma entry13_cos_odd (n : ℕ) (hodd : Odd n) :
    Real.cos ((n : ℝ) * Real.pi / 2) = 0 := by
  obtain ⟨m, hm⟩ := hodd
  have hmR : (n : ℝ) = 2 * (m : ℝ) + 1 := by exact_mod_cast hm
  have harg : (n : ℝ) * Real.pi / 2 = (m : ℝ) * Real.pi + Real.pi / 2 := by
    rw [hmR]
    ring
  rw [harg, Real.cos_add_pi_div_two, Real.sin_nat_mul_pi]
  ring

private lemma entry13_clausen_zero_of_even (n m : ℕ) (hn : 1 ≤ n)
    (hn2 : n = 2 * m) :
    chapter9Clausen (n + 1) 0
      = ∑' k : ℕ, (1 : ℝ) / ((((k + 1 : ℕ))) : ℝ) ^ (n + 1) := by
  have hne0 : n + 1 ≠ 0 := by omega
  have hne1 : n + 1 ≠ 1 := by omega
  have hodd : Odd (n + 1) := ⟨m, by rw [hn2]⟩
  have hneven : ¬Even (n + 1) := Nat.not_even_iff_odd.mpr hodd
  unfold chapter9Clausen
  simp only [hne0, hne1, ite_false]
  apply tsum_congr
  intro k
  unfold chapter9ClausenTerm
  simp only [hneven, ite_false, mul_zero, Real.cos_zero]

private lemma entry13s_even (n m : ℕ) (hn2 : n = 2 * m) :
    entry13s n = (-1 : ℝ) ^ m := by
  have hexp : n * (n + 1) / 2 = m * (2 * m + 1) := by
    have hmul : n * (n + 1) = 2 * (m * (2 * m + 1)) := by
      rw [hn2]
      ring
    rw [hmul]
    exact Nat.mul_div_cancel_left (m * (2 * m + 1)) (by norm_num : (0 : ℕ) < 2)
  have hpow : (-1 : ℝ) ^ (m * (2 * m + 1)) = (-1 : ℝ) ^ m := by
    have heq : m * (2 * m + 1) = m + 2 * (m * m) := by ring
    rw [heq, pow_add]
    have h1 : (-1 : ℝ) ^ (2 * (m * m)) = 1 := by
      rw [pow_mul, neg_one_sq, one_pow]
    rw [h1, mul_one]
  unfold entry13s
  rw [hexp]
  exact hpow

private lemma entry13_cos_even (n m : ℕ) (hn2 : n = 2 * m) :
    Real.cos ((n : ℝ) * Real.pi / 2) = (-1 : ℝ) ^ m := by
  have hnR : (n : ℝ) = 2 * (m : ℝ) := by exact_mod_cast hn2
  have harg : (n : ℝ) * Real.pi / 2 = (m : ℝ) * Real.pi := by
    rw [hnR]
    ring
  rw [harg, Real.cos_nat_mul_pi]

private lemma entry13_zeta_re (n : ℕ) (hn : 1 ≤ n) :
    (∑' k : ℕ, (1 : ℝ) / (((k + 1 : ℕ) : ℝ) ^ (n + 1)))
      = (riemannZeta (((n + 1 : ℕ)) : ℂ)).re := by
  have hs : (1 : ℝ) < ((((n + 1 : ℕ)) : ℂ)).re := by
    rw [← Complex.ofReal_natCast, Complex.ofReal_re]
    have h : (1 : ℕ) < n + 1 := by omega
    exact_mod_cast h
  have hz := zeta_eq_tsum_one_div_nat_add_one_cpow
    (s := (((n + 1 : ℕ)) : ℂ)) hs
  have hsumC : Summable
      (fun k : ℕ => (1 : ℂ) / ((k : ℂ) + 1) ^ (((n + 1 : ℕ)) : ℂ)) := by
    have hbase : Summable
        (fun k : ℕ => (1 : ℂ) / (k : ℂ) ^ (((n + 1 : ℕ)) : ℂ)) :=
      Complex.summable_one_div_nat_cpow.mpr hs
    have hshift := (summable_nat_add_iff 1).mpr hbase
    have hfun : (fun k : ℕ => (1 : ℂ) / ((k : ℂ) + 1) ^ (((n + 1 : ℕ)) : ℂ))
        = (fun k : ℕ => (1 : ℂ) / (((k + 1 : ℕ)) : ℂ) ^ (((n + 1 : ℕ)) : ℂ)) := by
      funext k
      simp only [Nat.cast_add_one]
    rw [hfun]
    exact hshift
  have hre := Complex.re_tsum hsumC
  rw [← hz] at hre
  have hterm : ∀ k : ℕ, ((1 : ℂ) / ((k : ℂ) + 1) ^ (((n + 1 : ℕ)) : ℂ)).re
      = (1 : ℝ) / (((k + 1 : ℕ)) : ℝ) ^ (n + 1) := by
    intro k
    rw [← Nat.cast_add_one, Complex.cpow_natCast, ← Nat.cast_pow,
      ← Complex.ofReal_natCast, ← Complex.ofReal_one, ← Complex.ofReal_div,
      Complex.ofReal_re, Nat.cast_pow]
  rw [tsum_congr hterm] at hre
  exact hre.symm

private lemma entry13_const_term (n : ℕ) (hn : 1 ≤ n) :
    entry13s n * chapter9Clausen (n + 1) 0
      = Real.cos ((n : ℝ) * Real.pi / 2)
        * (riemannZeta ((((n + 1 : ℕ))) : ℂ)).re := by
  rcases Nat.even_or_odd n with hev | hodd
  · obtain ⟨m, hm⟩ := hev
    have hn2 : n = 2 * m := by omega
    have hCl := entry13_clausen_zero_of_even n m hn hn2
    have hzeta := entry13_zeta_re n hn
    have hs := entry13s_even n m hn2
    have hc := entry13_cos_even n m hn2
    rw [hCl, hzeta, hs, hc]
  · have hCl0 := entry13_clausen_zero_of_odd n hn hodd
    have hc0 := entry13_cos_odd n hodd
    rw [hCl0, hc0, mul_zero, zero_mul]

/-! ## Conjunct 2: Dirichlet plus Abel -/

private lemma entry13_exp_pow (x : ℝ) (m : ℕ) :
    Complex.exp ((x : ℂ) * Complex.I) ^ m
      = Complex.exp (((((m : ℝ) * x : ℝ)) : ℂ) * Complex.I) := by
  have harg : (m : ℂ) * ((x : ℂ) * Complex.I)
      = (((((m : ℝ) * x : ℝ))) : ℂ) * Complex.I := by
    rw [Complex.ofReal_mul, Complex.ofReal_natCast]
    ring
  rw [← Complex.exp_nat_mul, harg]

private lemma entry13_exp_pow_re (x : ℝ) (m : ℕ) :
    (Complex.exp ((x : ℂ) * Complex.I) ^ m).re
      = Real.cos ((m : ℝ) * x) := by
  rw [entry13_exp_pow, Complex.exp_ofReal_mul_I_re]

private lemma entry13_geom_bound (x : ℝ) (hx0 : x ≠ 0)
    (hx : |x| < 2 * Real.pi) :
    ∃ b : ℝ, ∀ n : ℕ, ‖∑ i ∈ Finset.range n,
      Real.cos (((((i + 1 : ℕ))) : ℝ) * x)‖ ≤ b := by
  have hw1 : Complex.exp ((x : ℂ) * Complex.I) ≠ 1 := by
    intro hcon
    have hre : (Complex.exp ((x : ℂ) * Complex.I)).re = (1 : ℂ).re := by
      rw [hcon]
    rw [Complex.exp_ofReal_mul_I_re, Complex.one_re] at hre
    obtain ⟨hlo, hhi⟩ := abs_lt.mp hx
    have hiff := Real.cos_eq_one_iff_of_lt_of_lt hlo hhi
    rw [hiff] at hre
    exact hx0 hre
  have hw10 : (1 : ℂ) - Complex.exp ((x : ℂ) * Complex.I) ≠ 0 := by
    intro hcon
    apply hw1
    have h := sub_eq_zero.mp hcon
    exact h.symm
  have hc : (0 : ℝ) < ‖(1 : ℂ) - Complex.exp ((x : ℂ) * Complex.I)‖ :=
    norm_pos_iff.mpr hw10
  have hw1norm : ‖Complex.exp ((x : ℂ) * Complex.I)‖ = 1 :=
    Complex.norm_exp_ofReal_mul_I x
  refine ⟨2 / ‖(1 : ℂ) - Complex.exp ((x : ℂ) * Complex.I)‖, fun n => ?_⟩
  have hRe : (∑ i ∈ Finset.range n, Real.cos (((((i + 1 : ℕ))) : ℝ) * x))
      = (∑ i ∈ Finset.range n,
        Complex.exp ((x : ℂ) * Complex.I) ^ (i + 1)).re := by
    rw [Complex.re_sum]
    apply Finset.sum_congr rfl
    intro i _
    rw [entry13_exp_pow_re]
  have hsum : (∑ i ∈ Finset.range n,
        Complex.exp ((x : ℂ) * Complex.I) ^ (i + 1))
      = Complex.exp ((x : ℂ) * Complex.I)
        * ((Complex.exp ((x : ℂ) * Complex.I) ^ n - 1)
          / (Complex.exp ((x : ℂ) * Complex.I) - 1)) := by
    have h1 : (∑ i ∈ Finset.range n,
          Complex.exp ((x : ℂ) * Complex.I) ^ (i + 1))
        = (∑ i ∈ Finset.range n, Complex.exp ((x : ℂ) * Complex.I) ^ i)
          * Complex.exp ((x : ℂ) * Complex.I) := by
      rw [Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro i _
      exact pow_succ _ _
    rw [h1, geom_sum_eq hw1]
    ring
  have hwn : ‖Complex.exp ((x : ℂ) * Complex.I) ^ n‖ = 1 := by
    rw [norm_pow, hw1norm, one_pow]
  have h2 : ‖Complex.exp ((x : ℂ) * Complex.I) ^ n - 1‖ ≤ 2 := by
    have h := norm_sub_le (Complex.exp ((x : ℂ) * Complex.I) ^ n) 1
    rw [hwn, norm_one] at h
    have h11 : (1 : ℝ) + 1 = 2 := by norm_num
    rwa [h11] at h
  have hboundC : ‖∑ i ∈ Finset.range n,
        Complex.exp ((x : ℂ) * Complex.I) ^ (i + 1)‖
      ≤ 2 / ‖(1 : ℂ) - Complex.exp ((x : ℂ) * Complex.I)‖ := by
    rw [hsum, norm_mul, hw1norm, one_mul, norm_div]
    have hrev : ‖Complex.exp ((x : ℂ) * Complex.I) - 1‖
        = ‖(1 : ℂ) - Complex.exp ((x : ℂ) * Complex.I)‖ :=
      norm_sub_rev _ _
    rw [hrev, div_eq_mul_inv, div_eq_mul_inv]
    exact mul_le_mul_of_nonneg_right h2 (inv_nonneg.mpr hc.le)
  rw [Real.norm_eq_abs, hRe]
  exact le_trans (Complex.abs_re_le_norm _) hboundC

private lemma entry13_dirichlet_limit (x : ℝ) (hx0 : x ≠ 0)
    (hx : |x| < 2 * Real.pi) :
    ∃ l : ℝ, Filter.Tendsto
      (fun N : ℕ => ∑ k ∈ Finset.range N,
        Real.cos (((k + 1 : ℕ) : ℝ) * x) / ((k + 1 : ℕ) : ℝ))
      atTop (𝓝 l) := by
  have hanti : Antitone (fun k : ℕ => (1 : ℝ) / ((((k + 1 : ℕ))) : ℝ)) := by
    intro a b hab
    apply one_div_le_one_div_of_le
    · have h0 : (0 : ℕ) < a + 1 := by omega
      exact_mod_cast h0
    · exact_mod_cast Nat.add_le_add_right hab 1
  have hzero : Filter.Tendsto (fun k : ℕ => (1 : ℝ) / ((((k + 1 : ℕ))) : ℝ))
      atTop (𝓝 0) := by
    have h : Filter.Tendsto (fun n : ℕ => (1 : ℝ) / ((n : ℝ))) atTop (𝓝 0) :=
      tendsto_one_div_atTop_nhds_zero_nat
    have h2 : Filter.Tendsto
        (fun k : ℕ => (fun n : ℕ => (1 : ℝ) / ((n : ℝ))) (k + 1))
        atTop (𝓝 0) :=
      (tendsto_add_atTop_iff_nat 1).mpr h
    exact h2
  obtain ⟨b, hb⟩ := entry13_geom_bound x hx0 hx
  have hdir := Antitone.cauchySeq_series_mul_of_tendsto_zero_of_bounded
    (f := fun k : ℕ => (1 : ℝ) / ((((k + 1 : ℕ))) : ℝ))
    (z := fun k : ℕ => Real.cos (((k + 1 : ℕ) : ℝ) * x))
    hanti hzero hb
  obtain ⟨l, hl⟩ := cauchySeq_tendsto_of_complete hdir
  refine ⟨l, ?_⟩
  have hsmul : ∀ k : ℕ, ((1 : ℝ) / ((((k + 1 : ℕ))) : ℝ))
        • Real.cos (((k + 1 : ℕ) : ℝ) * x)
      = Real.cos (((k + 1 : ℕ) : ℝ) * x) / ((k + 1 : ℕ) : ℝ) := by
    intro k
    rw [smul_eq_mul]
    ring
  have h2 := hl
  simp only [hsmul] at h2
  exact h2

private lemma entry13_conjunct2 (x : ℝ) (hx0 : x ≠ 0)
    (hx : |x| < 2 * Real.pi) :
    Filter.Tendsto
      (fun N : ℕ => ∑ k ∈ Finset.range N,
        Real.cos (((k + 1 : ℕ) : ℝ) * x) / ((k + 1 : ℕ) : ℝ))
      atTop (𝓝 (chapter9Clausen 1 x)) := by
  obtain ⟨l, hl⟩ := entry13_dirichlet_limit x hx0 hx
  have hTS : ∀ n : ℕ, (∑ i ∈ Finset.range (n + 1),
        Real.cos (((i : ℕ) : ℝ) * x) / ((i : ℕ) : ℝ))
      = ∑ k ∈ Finset.range n,
        Real.cos (((k + 1 : ℕ) : ℝ) * x) / ((k + 1 : ℕ) : ℝ) := by
    intro n
    rw [Finset.sum_range_succ']
    have hf0 : Real.cos (((0 : ℕ) : ℝ) * x) / ((0 : ℕ) : ℝ) = 0 := by simp
    rw [hf0, add_zero]
  have hTshift : Filter.Tendsto
      (fun n : ℕ => ∑ i ∈ Finset.range (n + 1),
        Real.cos (((i : ℕ) : ℝ) * x) / ((i : ℕ) : ℝ))
      atTop (𝓝 l) := by
    have hfun : (fun n : ℕ => ∑ i ∈ Finset.range (n + 1),
          Real.cos (((i : ℕ) : ℝ) * x) / ((i : ℕ) : ℝ))
        = (fun N : ℕ => ∑ k ∈ Finset.range N,
          Real.cos (((k + 1 : ℕ) : ℝ) * x) / ((k + 1 : ℕ) : ℝ)) :=
      funext hTS
    rw [hfun]
    exact hl
  have hT : Filter.Tendsto
      (fun n : ℕ => ∑ i ∈ Finset.range n,
        Real.cos (((i : ℕ) : ℝ) * x) / ((i : ℕ) : ℝ))
      atTop (𝓝 l) :=
    (tendsto_add_atTop_iff_nat 1).mp hTshift
  have habel := Real.tendsto_tsum_powerSeries_nhdsWithin_lt
    (f := fun n : ℕ => Real.cos (((n : ℕ) : ℝ) * x) / ((n : ℕ) : ℝ)) hT
  have hid : ∀ r : ℝ, 0 ≤ r → r < 1 →
      (∑' n : ℕ, (Real.cos (((n : ℕ) : ℝ) * x) / ((n : ℕ) : ℝ)) * r ^ n)
        = entry13c1closed r x := by
    intro r hr0 hr1
    have hH1 := (entry13_H1_unshifted hr0 hr1 x).tsum_eq
    have hterm : ∀ n : ℕ, (Real.cos (((n : ℕ) : ℝ) * x) / ((n : ℕ) : ℝ)) * r ^ n
        = r ^ n * Real.cos ((n : ℝ) * x) / (n : ℝ) := by
      intro n
      ring
    rw [tsum_congr hterm]
    exact hH1
  have hc1l : Filter.Tendsto (fun r : ℝ => entry13c1closed r x)
      (nhdsWithin 1 (Set.Iio 1)) (𝓝 l) := by
    have heq : (fun r : ℝ => ∑' n : ℕ,
            (Real.cos (((n : ℕ) : ℝ) * x) / ((n : ℕ) : ℝ)) * r ^ n)
          =ᶠ[nhdsWithin 1 (Set.Iio 1)] (fun r : ℝ => entry13c1closed r x) := by
      filter_upwards [entry13_eventually_mem_Ioo] with r hr
      exact hid r hr.1.le hr.2
    exact Filter.Tendsto.congr' heq habel
  have hc1Cl := entry13_c1closed_tendsto x hx0 hx
  have hl_eq : l = chapter9Clausen 1 x := tendsto_nhds_unique hc1l hc1Cl
  rw [hl_eq] at hl
  exact hl

/-- Source: Bruce C. Berndt, Ramanujan's Notebooks, Part I, Chapter 9.

Proves `Wanted` entry `ramanujan_part1_ch9_entry13_bernoulligen`.
-/
theorem ramanujan_part1_ch9_entry13_bernoulligen (n : ℕ) (x : ℝ)
    (hn : 1 ≤ n) (hx0 : x ≠ 0) (hx : |x| < 2 * Real.pi) :
    IntervalIntegrable (chapter9Entry13Integrand n) volume 0 x ∧
      Tendsto
        (fun N : ℕ => ∑ k ∈ range N,
          Real.cos (((k + 1 : ℕ) : ℝ) * x) / ((k + 1 : ℕ) : ℝ))
        atTop (𝓝 (chapter9Clausen 1 x)) ∧
      (∀ m : ℕ, 2 ≤ m → m ≤ n + 1 →
        Summable (chapter9ClausenTerm m x)) ∧
      (∫ u in (0 : ℝ)..x, chapter9Entry13Integrand n u) =
        Real.cos (n * Real.pi / 2) * n.factorial *
            (riemannZeta ((n + 1 : ℕ) : ℂ)).re -
          ∑ j ∈ range (n + 1),
            (-1 : ℝ) ^ (j * (j + 1) / 2) *
              (n.factorial : ℝ) / ((n - j).factorial : ℝ) *
              x ^ (n - j) * chapter9Clausen (j + 1) x := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · exact entry13_intervalIntegrable n x hn hx
  · exact entry13_conjunct2 x hx0 hx
  · intro m hm2 _hmn
    exact chapter9ClausenTerm_summable_of_two_le m x hm2
  · have hL := entry13_tendsto_integral n x hn hx
    have hC0 : Filter.Tendsto (fun r : ℝ => entry13C (n + 1) r 0)
        (nhdsWithin 1 (Set.Iio 1)) (𝓝 (chapter9Clausen (n + 1) 0)) :=
      entry13_C_tendsto n hn 0
    have hconst : Filter.Tendsto
        (fun r : ℝ => entry13s n * (n.factorial : ℝ) * entry13C (n + 1) r 0)
        (nhdsWithin 1 (Set.Iio 1))
        (𝓝 (entry13s n * (n.factorial : ℝ) * chapter9Clausen (n + 1) 0)) :=
      tendsto_const_nhds.mul hC0
    have hterm : ∀ j ∈ Finset.range (n + 1), Filter.Tendsto
        (fun r : ℝ => entry13s j * (n.factorial : ℝ) / ((n - j).factorial : ℝ)
          * x ^ (n - j) * entry13C (j + 1) r x)
        (nhdsWithin 1 (Set.Iio 1))
        (𝓝 (entry13s j * (n.factorial : ℝ) / ((n - j).factorial : ℝ)
          * x ^ (n - j) * chapter9Clausen (j + 1) x)) := by
      intro j hj
      by_cases hj0 : j = 0
      · subst hj0
        have hC1 : Filter.Tendsto (fun r : ℝ => entry13C (0 + 1) r x)
            (nhdsWithin 1 (Set.Iio 1)) (𝓝 (chapter9Clausen (0 + 1) x)) := by
          have hfun : (fun r : ℝ => entry13C (0 + 1) r x)
              = (fun r : ℝ => entry13c1closed r x) := by
            funext r
            unfold entry13C
            simp
          have hCl : Filter.Tendsto (fun r : ℝ => entry13c1closed r x)
              (nhdsWithin 1 (Set.Iio 1)) (𝓝 (chapter9Clausen 1 x)) :=
            entry13_c1closed_tendsto x hx0 hx
          rw [hfun]
          simpa using hCl
        exact tendsto_const_nhds.mul hC1
      · have hj1 : 1 ≤ j := Nat.one_le_iff_ne_zero.mpr hj0
        have hC := entry13_C_tendsto j hj1 x
        exact tendsto_const_nhds.mul hC
    have hsum : Filter.Tendsto
        (fun r : ℝ => ∑ j ∈ Finset.range (n + 1),
          entry13s j * (n.factorial : ℝ) / ((n - j).factorial : ℝ)
            * x ^ (n - j) * entry13C (j + 1) r x)
        (nhdsWithin 1 (Set.Iio 1))
        (𝓝 (∑ j ∈ Finset.range (n + 1),
          entry13s j * (n.factorial : ℝ) / ((n - j).factorial : ℝ)
            * x ^ (n - j) * chapter9Clausen (j + 1) x)) :=
      tendsto_finsetSum _ hterm
    have hR : Filter.Tendsto
        (fun r : ℝ => entry13s n * (n.factorial : ℝ) * entry13C (n + 1) r 0
          - ∑ j ∈ Finset.range (n + 1),
            entry13s j * (n.factorial : ℝ) / ((n - j).factorial : ℝ)
              * x ^ (n - j) * entry13C (j + 1) r x)
        (nhdsWithin 1 (Set.Iio 1))
        (𝓝 (entry13s n * (n.factorial : ℝ) * chapter9Clausen (n + 1) 0
          - ∑ j ∈ Finset.range (n + 1),
            entry13s j * (n.factorial : ℝ) / ((n - j).factorial : ℝ)
              * x ^ (n - j) * chapter9Clausen (j + 1) x)) :=
      hconst.sub hsum
    have heq : (fun r : ℝ => ∫ u in (0 : ℝ)..x, u ^ n * entry13K r u)
        =ᶠ[nhdsWithin 1 (Set.Iio 1)]
        (fun r : ℝ => entry13s n * (n.factorial : ℝ) * entry13C (n + 1) r 0
          - ∑ j ∈ Finset.range (n + 1),
            entry13s j * (n.factorial : ℝ) / ((n - j).factorial : ℝ)
              * x ^ (n - j) * entry13C (j + 1) r x) := by
      filter_upwards [entry13_eventually_mem_Ioo] with r hr
      exact entry13_H3_identity n hr.1.le hr.2 x
    have hR' : Filter.Tendsto
        (fun r : ℝ => entry13s n * (n.factorial : ℝ) * entry13C (n + 1) r 0
          - ∑ j ∈ Finset.range (n + 1),
            entry13s j * (n.factorial : ℝ) / ((n - j).factorial : ℝ)
              * x ^ (n - j) * entry13C (j + 1) r x)
        (nhdsWithin 1 (Set.Iio 1))
        (𝓝 (∫ u in (0 : ℝ)..x, chapter9Entry13Integrand n u)) :=
      Filter.Tendsto.congr' heq hL
    have hEq : (∫ u in (0 : ℝ)..x, chapter9Entry13Integrand n u)
        = entry13s n * (n.factorial : ℝ) * chapter9Clausen (n + 1) 0
          - ∑ j ∈ Finset.range (n + 1),
            entry13s j * (n.factorial : ℝ) / ((n - j).factorial : ℝ)
              * x ^ (n - j) * chapter9Clausen (j + 1) x :=
      tendsto_nhds_unique hR' hR
    have hct := entry13_const_term n hn
    have hconstEq : entry13s n * (n.factorial : ℝ) * chapter9Clausen (n + 1) 0
        = Real.cos (n * Real.pi / 2) * n.factorial *
          (riemannZeta ((n + 1 : ℕ) : ℂ)).re := by
      have hfac : ((n.factorial : ℕ) : ℝ) = (n.factorial : ℝ) := rfl
      linear_combination (n.factorial : ℝ) * hct
    have hsumEq : (∑ j ∈ Finset.range (n + 1),
            entry13s j * (n.factorial : ℝ) / ((n - j).factorial : ℝ)
              * x ^ (n - j) * chapter9Clausen (j + 1) x)
        = ∑ j ∈ Finset.range (n + 1),
            (-1 : ℝ) ^ (j * (j + 1) / 2) *
              (n.factorial : ℝ) / ((n - j).factorial : ℝ) *
              x ^ (n - j) * chapter9Clausen (j + 1) x := by
      apply Finset.sum_congr rfl
      intro j _
      rfl
    rw [hEq, hconstEq, hsumEq]

end
end Entry13Bernoulligen
end MathlibExt.Analysis.Ramanujan.Part1Ch9
end
