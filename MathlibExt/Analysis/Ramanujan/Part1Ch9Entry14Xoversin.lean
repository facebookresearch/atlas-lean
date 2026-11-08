/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import Mathlib.Analysis.PSeriesComplex

public import MathlibExt.Analysis.Ramanujan.Part1Ch9Entry13Bernoulligen

@[expose] public section

section
/-!
# Ramanujan's Notebooks, Part I, Chapter 9

Statements of entries from B. C. Berndt, *Ramanujan's Notebooks, Part I*
(Springer, 1985), with proofs.
-/

namespace MathlibExt.Analysis.Ramanujan.Part1Ch9

namespace Entry14Xoversin

open scoped Nat Real BigOperators Interval Polynomial ContDiff
open Asymptotics Filter Finset Complex Topology MeasureTheory
open MathlibExt.Analysis.Ramanujan.Part1Ch9.Entry13Bernoulligen

noncomputable section

def chapter9ChiAtOne (m : ℕ) : ℝ :=
  ∑' k : ℕ, 1 / (((2 * k + 1 : ℕ) : ℝ) ^ m)

def chapter9Entry14Integrand (n : ℕ) (u : ℝ) : ℝ :=
  u ^ n / 2 / Real.sin u

def chapter9OddClausenTerm (m : ℕ) (x : ℝ) (k : ℕ) : ℝ :=
  let odd : ℕ := 2 * k + 1
  if Even m then
    Real.sin ((odd : ℝ) * x) / ((odd : ℝ) ^ m)
  else
    Real.cos ((odd : ℝ) * x) / ((odd : ℝ) ^ m)

def chapter9OddClausen (m : ℕ) (x : ℝ) : ℝ :=
  if m = 0 then 0
  else if m = 1 then -(1 / 2 : ℝ) * Real.log |Real.tan (x / 2)|
  else ∑' k : ℕ, chapter9OddClausenTerm m x k

/-- Norm bound for the odd Clausen summand. -/
theorem chapter9OddClausenTerm_norm_bound (m : ℕ) (x : ℝ) (k : ℕ) :
    ‖chapter9OddClausenTerm m x k‖ ≤ 1 / (((2 * k + 1 : ℕ) : ℝ) ^ m) := by
  have hpos : (0 : ℝ) < (((2 * k + 1 : ℕ) : ℝ) ^ m) := by positivity
  unfold chapter9OddClausenTerm
  split_ifs
  · rw [Real.norm_eq_abs, abs_div, abs_of_pos hpos]
    exact div_le_div_of_nonneg_right (Real.abs_sin_le_one _) (le_of_lt hpos)
  · rw [Real.norm_eq_abs, abs_div, abs_of_pos hpos]
    exact div_le_div_of_nonneg_right (Real.abs_cos_le_one _) (le_of_lt hpos)

private theorem helper_chi_summable (n : ℕ) (hn : 1 ≤ n) :
    Summable (fun k : ℕ => 1 / (((2 * k + 1 : ℕ) : ℝ) ^ (n + 1))) := by
  have hbase : Summable (fun n' : ℕ => 1 / ((n' : ℝ) ^ (n + 1))) :=
    Real.summable_one_div_nat_pow.mpr (by omega)
  have hinj : Function.Injective (fun k : ℕ => 2 * k + 1) := by
    intro a b h
    simp only at h
    omega
  simpa [Function.comp_def] using hbase.comp_injective hinj

/-- The odd Clausen series is summable for `2 ≤ m`. -/
theorem chapter9OddClausenTerm_summable_of_two_le (m : ℕ) (x : ℝ) (hm : 2 ≤ m) :
    Summable (chapter9OddClausenTerm m x) := by
  have hbase : Summable (fun k : ℕ => 1 / (((2 * k + 1 : ℕ) : ℝ) ^ m)) := by
    have hfull : Summable (fun n' : ℕ => 1 / ((n' : ℝ) ^ m)) :=
      Real.summable_one_div_nat_pow.mpr (by omega)
    have hinj : Function.Injective (fun k : ℕ => 2 * k + 1) := by
      intro a b h
      simp only at h
      omega
    simpa [Function.comp_def] using hfull.comp_injective hinj
  exact Summable.of_norm_bounded hbase (chapter9OddClausenTerm_norm_bound m x)

/-- `chapter9OddClausen` at `m = 0` vanishes. -/
theorem chapter9OddClausen_zero (x : ℝ) : chapter9OddClausen 0 x = 0 := by
  rfl

/-- `chapter9OddClausen` at `m = 1` is the log-tangent closed form. -/
theorem chapter9OddClausen_one (x : ℝ) :
    chapter9OddClausen 1 x = -(1 / 2 : ℝ) * Real.log |Real.tan (x / 2)| := by
  rfl

/-- `chapter9OddClausen` for `2 ≤ m` is the odd Clausen series. -/
theorem chapter9OddClausen_of_two_le (m : ℕ) (x : ℝ) (hm : 2 ≤ m) :
    chapter9OddClausen m x = ∑' k : ℕ, chapter9OddClausenTerm m x k := by
  unfold chapter9OddClausen
  simp only [show m ≠ 0 by omega, show m ≠ 1 by omega, ↓reduceIte]

private lemma sin_ne_zero_of_mem_Ioo (u : ℝ) (hu : |u| < Real.pi)
    (hu0 : u ≠ 0) : Real.sin u ≠ 0 := by
  by_cases hpos : 0 < u
  · have hlt : u < Real.pi := by
      have h1 : |u| = u := abs_of_pos hpos
      linarith
    have hsin : 0 < Real.sin u :=
      Real.sin_pos_of_pos_of_lt_pi hpos hlt
    exact ne_of_gt hsin
  · have hneg : u < 0 := lt_of_le_of_ne (le_of_not_gt hpos) hu0
    have hv0 : (0 : ℝ) < -u := by linarith
    have hvpi : -u < Real.pi := by
      have h1 : |u| = -u := abs_of_neg hneg
      linarith
    have hsinv : 0 < Real.sin (-u) :=
      Real.sin_pos_of_pos_of_lt_pi hv0 hvpi
    have hsin : Real.sin u < 0 := by
      have hneg2 : Real.sin (-u) = -Real.sin u := Real.sin_neg u
      linarith
    exact ne_of_lt hsin

private lemma continuousAt_sin_div (u : ℝ) (hu : u ≠ 0) :
    ContinuousAt (fun v : ℝ => Real.sin v / v) u := by
  apply ContinuousAt.div Real.continuous_sin.continuousAt continuous_id.continuousAt
  exact hu

private lemma tendsto_sin_div_punctured :
    Tendsto (fun u : ℝ => Real.sin u / u) (𝓝[≠] (0 : ℝ)) (𝓝 1) := by
  have hderiv : HasDerivAt Real.sin (Real.cos 0) 0 := Real.hasDerivAt_sin 0
  have hcos0 : Real.cos (0 : ℝ) = 1 := Real.cos_zero
  rw [hcos0] at hderiv
  have hslope := hderiv.tendsto_slope
  have hEq : (slope Real.sin 0) =ᶠ[𝓝[≠] (0 : ℝ)]
      (fun u => Real.sin u / u) := by
    filter_upwards [self_mem_nhdsWithin] with u hu
    simp only [slope, vsub_eq_sub, Real.sin_zero, sub_zero] at hu ⊢
    rw [smul_eq_mul, div_eq_mul_inv, mul_comm]
  have h2 := hslope.congr' hEq
  simpa using h2

private lemma continuousAt_sin_div_ext :
    ContinuousAt (fun u : ℝ => if u = 0 then (1 : ℝ) else Real.sin u / u) 0 := by
  rw [ContinuousAt]
  have hval : (if (0 : ℝ) = 0 then (1 : ℝ) else Real.sin 0 / 0) = 1 := by simp
  rw [hval]
  rw [Metric.tendsto_nhds]
  intro ε hε
  have hlim2 : ∀ᶠ u in 𝓝[≠] (0 : ℝ), dist (Real.sin u / u) 1 < ε := by
    have hlim := tendsto_sin_div_punctured
    rw [Metric.tendsto_nhds] at hlim
    exact hlim ε hε
  rw [eventually_nhdsWithin_iff] at hlim2
  filter_upwards [hlim2] with u hu
  by_cases hu0 : u = 0
  · subst hu0
    simp only [↓reduceIte, dist_self]
    exact hε
  · simp only [hu0, ↓reduceIte]
    exact hu hu0

private lemma continuous_sin_div_ext :
    Continuous (fun u : ℝ => if u = 0 then (1 : ℝ) else Real.sin u / u) := by
  rw [continuous_iff_continuousAt]
  intro u
  by_cases hu0 : u = 0
  · subst hu0
    exact continuousAt_sin_div_ext
  · have hcont : ContinuousAt (fun v : ℝ => Real.sin v / v) u :=
      continuousAt_sin_div u hu0
    have heq : (fun v : ℝ => if v = 0 then (1 : ℝ) else Real.sin v / v)
        =ᶠ[𝓝 u] (fun v : ℝ => Real.sin v / v) := by
      filter_upwards [eventually_ne_nhds hu0] with v hv
      simp only [hv, ↓reduceIte]
    exact hcont.congr heq.symm

private lemma sin_div_ext_ne_zero (u : ℝ) (hu : u ∈ Set.Ioo (-Real.pi) Real.pi) :
    (if u = 0 then (1 : ℝ) else Real.sin u / u) ≠ 0 := by
  by_cases hu0 : u = 0
  · simp only [hu0, ↓reduceIte]
    norm_num
  · simp only [hu0, ↓reduceIte]
    have habs : |u| < Real.pi := by
      simp only [Set.mem_Ioo] at hu
      rw [abs_lt]
      constructor <;> linarith
    have hsin : Real.sin u ≠ 0 := sin_ne_zero_of_mem_Ioo u habs hu0
    exact div_ne_zero hsin hu0

private lemma uIcc_subset_Ioo_of_abs_lt (x : ℝ) (hx : |x| < Real.pi) :
    Set.uIcc (0 : ℝ) x ⊆ Set.Ioo (-Real.pi) Real.pi := by
  intro u hu
  simp only [Set.mem_uIcc] at hu
  simp only [Set.mem_Ioo]
  rcases hu with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · have habs : |u| ≤ |x| := by
      rw [abs_of_nonneg h1]
      calc u ≤ x := h2
        _ ≤ |x| := le_abs_self x
    have h1' : (0 : ℝ) ≤ u := h1
    constructor <;> linarith [abs_lt.mp hx]
  · have habs : |u| ≤ |x| := by
      have hneg : u ≤ 0 := h2
      rw [abs_of_nonpos hneg]
      have hxneg : x ≤ 0 := le_trans h1 h2
      rw [abs_of_nonpos hxneg]
      linarith
    constructor <;> linarith [abs_lt.mp hx]

private lemma continuousOn_inv_sin_div_ext :
    ContinuousOn
      (fun u : ℝ => ((if u = 0 then (1 : ℝ) else Real.sin u / u))⁻¹ / 2)
      (Set.Ioo (-Real.pi) Real.pi) := by
  have hcont : ContinuousOn
      (fun u : ℝ => if u = 0 then (1 : ℝ) else Real.sin u / u)
      (Set.Ioo (-Real.pi) Real.pi) :=
    continuous_sin_div_ext.continuousOn
  have hne : ∀ u ∈ Set.Ioo (-Real.pi) Real.pi,
      (if u = 0 then (1 : ℝ) else Real.sin u / u) ≠ 0 :=
    fun u hu => sin_div_ext_ne_zero u hu
  have hinv : ContinuousOn
      (fun u : ℝ => ((if u = 0 then (1 : ℝ) else Real.sin u / u))⁻¹)
      (Set.Ioo (-Real.pi) Real.pi) := hcont.inv₀ hne
  exact hinv.div_const 2

private lemma integrand_eq_continuous_ext (n : ℕ) (hn : 1 ≤ n) (u : ℝ)
    (hu0 : u ≠ 0) :
    chapter9Entry14Integrand n u =
      u ^ (n - 1) *
        (((if u = 0 then (1 : ℝ) else Real.sin u / u))⁻¹ / 2) := by
  have hn1 : n = (n - 1) + 1 := by omega
  have hpow : u ^ n = u ^ (n - 1) * u := by
    conv_lhs => rw [hn1]
    rw [pow_succ]
  simp only [chapter9Entry14Integrand, hu0, ↓reduceIte, inv_div]
  rw [hpow]
  simp only [div_eq_mul_inv]
  ring

private lemma helper_integrand_integrable (n : ℕ) (x : ℝ) (hn : 1 ≤ n)
    (hx : |x| < Real.pi) :
    IntervalIntegrable (chapter9Entry14Integrand n) volume 0 x := by
  have hsub : Set.uIcc (0 : ℝ) x ⊆ Set.Ioo (-Real.pi) Real.pi :=
    uIcc_subset_Ioo_of_abs_lt x hx
  have hpow_cont : ContinuousOn (fun u : ℝ => u ^ (n - 1))
      (Set.Ioo (-Real.pi) Real.pi) :=
    (continuous_id.pow (n - 1)).continuousOn
  have hinv_cont := continuousOn_inv_sin_div_ext
  have hg_cont : ContinuousOn
      (fun u : ℝ => u ^ (n - 1) *
        (((if u = 0 then (1 : ℝ) else Real.sin u / u))⁻¹ / 2))
      (Set.Ioo (-Real.pi) Real.pi) := hpow_cont.mul hinv_cont
  have hg_uIcc : ContinuousOn
      (fun u : ℝ => u ^ (n - 1) *
        (((if u = 0 then (1 : ℝ) else Real.sin u / u))⁻¹ / 2))
      (Set.uIcc (0 : ℝ) x) := hg_cont.mono hsub
  have hg_int : IntervalIntegrable
      (fun u : ℝ => u ^ (n - 1) *
        (((if u = 0 then (1 : ℝ) else Real.sin u / u))⁻¹ / 2))
      volume 0 x := hg_uIcc.intervalIntegrable
  have hae : (fun u : ℝ => u ^ (n - 1) *
        (((if u = 0 then (1 : ℝ) else Real.sin u / u))⁻¹ / 2))
      =ᵐ[volume.restrict (Set.uIoc (0 : ℝ) x)]
        (chapter9Entry14Integrand n) := by
    filter_upwards [Measure.ae_ne (volume.restrict (Set.uIoc 0 x)) 0] with u hu0
    exact (integrand_eq_continuous_ext n hn u hu0).symm
  exact IntervalIntegrable.congr_ae hg_int hae

private lemma xs_sum_range_even_odd {α : Type*} [AddCommMonoid α]
    (f : ℕ → α) (N : ℕ) :
    ∑ k ∈ range (2 * N), f k =
      (∑ k ∈ range N, f (2 * k)) + ∑ k ∈ range N, f (2 * k + 1) := by
  induction N with
  | zero => simp
  | succ N ih =>
      rw [show 2 * (N + 1) = (2 * N + 1) + 1 by omega]
      rw [sum_range_succ, sum_range_succ, sum_range_succ, sum_range_succ, ih]
      ac_rfl

private lemma xs_odd_clausen_term_eq (m : ℕ) (x : ℝ) (k : ℕ) :
    chapter9OddClausenTerm m x k = chapter9ClausenTerm m x (2 * k) := by
  unfold chapter9OddClausenTerm chapter9ClausenTerm
  rfl

private lemma xs_even_clausen_term_eq (m : ℕ) (x : ℝ) (k : ℕ) :
    chapter9ClausenTerm m x (2 * k + 1) =
      (1 / (2 : ℝ) ^ m) * chapter9ClausenTerm m (2 * x) k := by
  have harg : (((2 * k + 1 + 1 : ℕ) : ℝ) * x) =
      (((k + 1 : ℕ) : ℝ) * (2 * x)) := by
    push_cast
    ring
  have hden : (((2 * k + 1 + 1 : ℕ) : ℝ) ^ m) =
      (2 : ℝ) ^ m * (((k + 1 : ℕ) : ℝ) ^ m) := by
    rw [show ((2 * k + 1 + 1 : ℕ) : ℝ) = 2 * ((k + 1 : ℕ) : ℝ) by
      push_cast
      ring]
    rw [mul_pow]
  unfold chapter9ClausenTerm
  split_ifs <;> rw [harg, hden] <;> ring

/-- The odd Clausen function is the odd-frequency part of `chapter9Clausen` for `2 ≤ m`. -/
theorem chapter9OddClausen_eq_clausen_sub_of_two_le (m : ℕ) (x : ℝ) (hm : 2 ≤ m) :
    chapter9OddClausen m x = chapter9Clausen m x -
      (1 / (2 : ℝ) ^ m) * chapter9Clausen m (2 * x) := by
  have hfull := chapter9ClausenTerm_summable_of_two_le m x hm
  have hinj_even : Function.Injective (fun k : ℕ => 2 * k) := by
    intro a b hab
    exact Nat.mul_left_cancel (by omega) hab
  have hinj_odd : Function.Injective (fun k : ℕ => 2 * k + 1) := by
    intro a b hab
    exact hinj_even (Nat.add_right_cancel hab)
  have heven : Summable (fun k : ℕ => chapter9ClausenTerm m x (2 * k)) := by
    simpa [Function.comp_def] using hfull.comp_injective hinj_even
  have hodd : Summable (fun k : ℕ => chapter9ClausenTerm m x (2 * k + 1)) := by
    simpa [Function.comp_def] using hfull.comp_injective hinj_odd
  have hsplit := tsum_even_add_odd heven hodd
  have hodd_tsum : (∑' k : ℕ, chapter9ClausenTerm m x (2 * k)) =
      chapter9OddClausen m x := by
    calc
      (∑' k : ℕ, chapter9ClausenTerm m x (2 * k)) =
          ∑' k : ℕ, chapter9OddClausenTerm m x k :=
        tsum_congr (fun k => (xs_odd_clausen_term_eq m x k).symm)
      _ = chapter9OddClausen m x := by
        unfold chapter9OddClausen
        simp only [show m ≠ 0 by omega, show m ≠ 1 by omega, ↓reduceIte]
  have heven_tsum : (∑' k : ℕ, chapter9ClausenTerm m x (2 * k + 1)) =
      (1 / (2 : ℝ) ^ m) * chapter9Clausen m (2 * x) := by
    calc
      (∑' k : ℕ, chapter9ClausenTerm m x (2 * k + 1)) =
          ∑' k : ℕ, (1 / (2 : ℝ) ^ m) * chapter9ClausenTerm m (2 * x) k :=
        tsum_congr (xs_even_clausen_term_eq m x)
      _ = (1 / (2 : ℝ) ^ m) *
          (∑' k : ℕ, chapter9ClausenTerm m (2 * x) k) := tsum_mul_left
      _ = (1 / (2 : ℝ) ^ m) * chapter9Clausen m (2 * x) := by
        rw [chapter9Clausen_of_two_le m (2 * x) hm]
  rw [hodd_tsum, heven_tsum, ← chapter9Clausen_of_two_le m x hm] at hsplit
  linarith

private lemma xs_odd_clausen_one_eq (x : ℝ) (hx0 : x ≠ 0)
    (hx : |x| < Real.pi) :
    chapter9OddClausen 1 x = chapter9Clausen 1 x -
      (1 / (2 : ℝ) ^ (1 : ℕ)) * chapter9Clausen 1 (2 * x) := by
  have hxhalf : |x / 2| < Real.pi / 2 := by
    rw [abs_div, abs_of_pos (by norm_num : (0 : ℝ) < 2)]
    exact div_lt_div_of_pos_right hx (by norm_num)
  have hxhalfpi : |x / 2| < Real.pi := by
    have hpi : 0 < Real.pi := Real.pi_pos
    linarith
  have hxhalf0 : x / 2 ≠ 0 := div_ne_zero hx0 (by norm_num)
  have hsin : Real.sin (x / 2) ≠ 0 :=
    sin_ne_zero_of_mem_Ioo (x / 2) hxhalfpi hxhalf0
  have hcospos : 0 < Real.cos (x / 2) := by
    apply Real.cos_pos_of_mem_Ioo
    simpa only [Set.mem_Ioo] using (abs_lt.mp hxhalf)
  have hcos : Real.cos (x / 2) ≠ 0 := ne_of_gt hcospos
  have hA : |2 * Real.sin (x / 2)| ≠ 0 :=
    abs_ne_zero.mpr (mul_ne_zero (by norm_num) hsin)
  have hC : |2 * Real.cos (x / 2)| ≠ 0 :=
    abs_ne_zero.mpr (mul_ne_zero (by norm_num) hcos)
  have hprod : |2 * Real.sin x| =
      |2 * Real.sin (x / 2)| * |2 * Real.cos (x / 2)| := by
    have hs : Real.sin x = 2 * Real.sin (x / 2) * Real.cos (x / 2) := by
      conv_lhs => rw [show x = 2 * (x / 2) by ring, Real.sin_two_mul]
    simp only [hs, abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 2)]
    ring
  have htan : |Real.tan (x / 2)| =
      |2 * Real.sin (x / 2)| / |2 * Real.cos (x / 2)| := by
    rw [Real.tan_eq_sin_div_cos, abs_div, abs_mul, abs_mul]
    norm_num
    field_simp
  unfold chapter9OddClausen chapter9Clausen
  simp only [one_ne_zero, ↓reduceIte, pow_one]
  rw [show 2 * x / 2 = x by ring]
  rw [htan, Real.log_div hA hC, hprod, Real.log_mul hA hC]
  ring

/-- The odd Clausen function is the odd-frequency part of `chapter9Clausen` on `(-π, π)`. -/
theorem chapter9OddClausen_eq_clausen_sub (m : ℕ) (x : ℝ) (hm : 1 ≤ m)
    (hx0 : x ≠ 0) (hx : |x| < Real.pi) :
    chapter9OddClausen m x = chapter9Clausen m x -
      (1 / (2 : ℝ) ^ m) * chapter9Clausen m (2 * x) := by
  by_cases hm1 : m = 1
  · subst m
    exact xs_odd_clausen_one_eq x hx0 hx
  · exact chapter9OddClausen_eq_clausen_sub_of_two_le m x (by omega)

private lemma xs_odd_partial_sum_eq (x : ℝ) (N : ℕ) :
    (∑ k ∈ range N,
        Real.cos (((2 * k + 1 : ℕ) : ℝ) * x) / ((2 * k + 1 : ℕ) : ℝ)) =
      (∑ k ∈ range (2 * N),
        Real.cos (((k + 1 : ℕ) : ℝ) * x) / ((k + 1 : ℕ) : ℝ)) -
      (1 / 2 : ℝ) * ∑ k ∈ range N,
        Real.cos (((k + 1 : ℕ) : ℝ) * (2 * x)) / ((k + 1 : ℕ) : ℝ) := by
  have hsplit := xs_sum_range_even_odd (chapter9ClausenTerm 1 x) N
  have hodd : (∑ k ∈ range N, chapter9ClausenTerm 1 x (2 * k)) =
      ∑ k ∈ range N, chapter9OddClausenTerm 1 x k := by
    apply Finset.sum_congr rfl
    intro k _
    exact (xs_odd_clausen_term_eq 1 x k).symm
  have heven : (∑ k ∈ range N, chapter9ClausenTerm 1 x (2 * k + 1)) =
      (1 / 2 : ℝ) * ∑ k ∈ range N, chapter9ClausenTerm 1 (2 * x) k := by
    calc
      (∑ k ∈ range N, chapter9ClausenTerm 1 x (2 * k + 1)) =
          ∑ k ∈ range N, (1 / 2 : ℝ) * chapter9ClausenTerm 1 (2 * x) k := by
        apply Finset.sum_congr rfl
        intro k _
        simpa using xs_even_clausen_term_eq 1 x k
      _ = (1 / 2 : ℝ) * ∑ k ∈ range N, chapter9ClausenTerm 1 (2 * x) k := by
        rw [Finset.mul_sum]
  rw [hodd, heven] at hsplit
  have hrel : (∑ k ∈ range N, chapter9OddClausenTerm 1 x k) =
      (∑ k ∈ range (2 * N), chapter9ClausenTerm 1 x k) -
        (1 / 2 : ℝ) * ∑ k ∈ range N, chapter9ClausenTerm 1 (2 * x) k := by
    linarith [hsplit]
  simpa [chapter9OddClausenTerm, chapter9ClausenTerm] using hrel

private lemma xs_cos_series_tendsto (x : ℝ) (hx0 : x ≠ 0)
    (hx : |x| < Real.pi) :
    Tendsto
      (fun N : ℕ => ∑ k ∈ range N,
        Real.cos (((2 * k + 1 : ℕ) : ℝ) * x) / ((2 * k + 1 : ℕ) : ℝ))
      atTop (𝓝 (chapter9OddClausen 1 x)) := by
  have hx_two_pi : |x| < 2 * Real.pi := by
    nlinarith [Real.pi_pos]
  have h2x0 : 2 * x ≠ 0 := mul_ne_zero (by norm_num) hx0
  have h2x_two_pi : |2 * x| < 2 * Real.pi := by
    rw [abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 2)]
    nlinarith
  have hentry_x := ramanujan_part1_ch9_entry13_bernoulligen
    1 x (by norm_num) hx0 hx_two_pi
  have hentry_2x := ramanujan_part1_ch9_entry13_bernoulligen
    1 (2 * x) (by norm_num) h2x0 h2x_two_pi
  have hdouble : Tendsto (fun N : ℕ => 2 * N) atTop atTop := by
    rw [Filter.tendsto_atTop]
    intro b
    filter_upwards [eventually_ge_atTop b] with N hN
    omega
  have hfirst : Tendsto
      (fun N : ℕ => ∑ k ∈ range (2 * N),
        Real.cos (((k + 1 : ℕ) : ℝ) * x) / ((k + 1 : ℕ) : ℝ))
      atTop (𝓝 (chapter9Clausen 1 x)) := by
    have hcomp := hentry_x.2.1.comp hdouble
    change Tendsto
      (fun N : ℕ => ∑ k ∈ range (2 * N),
        Real.cos (((k + 1 : ℕ) : ℝ) * x) / ((k + 1 : ℕ) : ℝ))
      atTop (𝓝 (chapter9Clausen 1 x)) at hcomp
    exact hcomp
  have hsecond : Tendsto
      (fun N : ℕ => (1 / 2 : ℝ) * ∑ k ∈ range N,
        Real.cos (((k + 1 : ℕ) : ℝ) * (2 * x)) / ((k + 1 : ℕ) : ℝ))
      atTop (𝓝 ((1 / 2 : ℝ) * chapter9Clausen 1 (2 * x))) :=
    tendsto_const_nhds.mul hentry_2x.2.1
  have hdiff := hfirst.sub hsecond
  have hcl := xs_odd_clausen_one_eq x hx0 hx
  norm_num at hcl
  rw [← hcl] at hdiff
  exact hdiff.congr' (Eventually.of_forall fun N => (xs_odd_partial_sum_eq x N).symm)

private lemma xs_zeta_re (m : ℕ) (hm : 2 ≤ m) :
    (∑' k : ℕ, (1 : ℝ) / (((k + 1 : ℕ) : ℝ) ^ m)) =
      (riemannZeta (m : ℂ)).re := by
  have hs : (1 : ℝ) < ((m : ℂ)).re := by
    rw [← Complex.ofReal_natCast, Complex.ofReal_re]
    exact_mod_cast (show 1 < m by omega)
  have hz := zeta_eq_tsum_one_div_nat_add_one_cpow (s := (m : ℂ)) hs
  have hsumC : Summable
      (fun k : ℕ => (1 : ℂ) / (k + 1) ^ (m : ℂ)) := by
    have hbase : Summable (fun k : ℕ => (1 : ℂ) / (k : ℂ) ^ (m : ℂ)) :=
      Complex.summable_one_div_nat_cpow.mpr hs
    have hshift := (summable_nat_add_iff 1).mpr hbase
    have hfun : (fun k : ℕ => (1 : ℂ) / (k + 1) ^ (m : ℂ)) =
        (fun k : ℕ => (1 : ℂ) / ((k + 1 : ℕ) : ℂ) ^ (m : ℂ)) := by
      funext k
      simp only [Nat.cast_add_one]
    rw [hfun]
    exact hshift
  have hre := Complex.re_tsum hsumC
  rw [← hz] at hre
  have hterm : ∀ k : ℕ, ((1 : ℂ) / (k + 1) ^ (m : ℂ)).re =
      (1 : ℝ) / (((k + 1 : ℕ) : ℝ) ^ m) := by
    intro k
    rw [← Nat.cast_add_one, Complex.cpow_natCast, ← Nat.cast_pow,
      ← Complex.ofReal_natCast, ← Complex.ofReal_one, ← Complex.ofReal_div,
      Complex.ofReal_re, Nat.cast_pow]
  rw [tsum_congr hterm] at hre
  exact hre.symm

/-- The odd-denominator zeta sum is the Dirichlet chi value at an integer `m ≥ 2`. -/
theorem chapter9ChiAtOne_eq_zeta (m : ℕ) (hm : 2 ≤ m) :
    chapter9ChiAtOne m =
      (1 - 1 / (2 : ℝ) ^ m) * (riemannZeta (m : ℂ)).re := by
  let f : ℕ → ℝ := fun k => 1 / (((k + 1 : ℕ) : ℝ) ^ m)
  have hbase : Summable (fun k : ℕ => 1 / ((k : ℝ) ^ m)) :=
    Real.summable_one_div_nat_pow.mpr (by omega)
  have hfull : Summable f := by
    exact (summable_nat_add_iff 1).mpr hbase
  have heven : Summable (fun k : ℕ => f (2 * k)) := by
    exact hfull.comp_injective (by
      intro a b hab
      exact Nat.mul_left_cancel (by omega) hab)
  have hodd : Summable (fun k : ℕ => f (2 * k + 1)) := by
    exact hfull.comp_injective (by
      intro a b hab
      exact Nat.add_right_cancel hab |> Nat.mul_left_cancel (by omega))
  have hsplit := tsum_even_add_odd heven hodd
  have heven_tsum : (∑' k : ℕ, f (2 * k)) = chapter9ChiAtOne m := by
    unfold f chapter9ChiAtOne
    rfl
  have hodd_term : ∀ k : ℕ, f (2 * k + 1) =
      (1 / (2 : ℝ) ^ m) * f k := by
    intro k
    have hden : (((2 * k + 1 + 1 : ℕ) : ℝ) ^ m) =
        (2 : ℝ) ^ m * (((k + 1 : ℕ) : ℝ) ^ m) := by
      rw [show ((2 * k + 1 + 1 : ℕ) : ℝ) = 2 * ((k + 1 : ℕ) : ℝ) by
        push_cast
        ring]
      rw [mul_pow]
    unfold f
    rw [hden]
    ring
  have hodd_tsum : (∑' k : ℕ, f (2 * k + 1)) =
      (1 / (2 : ℝ) ^ m) * ∑' k : ℕ, f k := by
    calc
      (∑' k : ℕ, f (2 * k + 1)) =
          ∑' k : ℕ, (1 / (2 : ℝ) ^ m) * f k := tsum_congr hodd_term
      _ = (1 / (2 : ℝ) ^ m) * ∑' k : ℕ, f k := tsum_mul_left
  rw [heven_tsum, hodd_tsum] at hsplit
  have hzeta : (∑' k : ℕ, f k) = (riemannZeta (m : ℂ)).re := by
    exact xs_zeta_re m hm
  rw [hzeta] at hsplit
  linarith

private lemma xs_integrand_eq_entry13 (n : ℕ) (u : ℝ) (hu0 : u ≠ 0)
    (hu : |u| < Real.pi) :
    chapter9Entry14Integrand n u = chapter9Entry13Integrand n u -
      (1 / (2 : ℝ) ^ n) * chapter9Entry13Integrand n (2 * u) := by
  have hsin : Real.sin u ≠ 0 := sin_ne_zero_of_mem_Ioo u hu hu0
  have huhalf : |u / 2| < Real.pi := by
    rw [abs_div, abs_of_pos (by norm_num : (0 : ℝ) < 2)]
    nlinarith [Real.pi_pos]
  have huhalf0 : u / 2 ≠ 0 := div_ne_zero hu0 (by norm_num)
  have hsinh : Real.sin (u / 2) ≠ 0 :=
    sin_ne_zero_of_mem_Ioo (u / 2) huhalf huhalf0
  have hpow : (2 * u) ^ n = (2 : ℝ) ^ n * u ^ n := mul_pow 2 u n
  have hhalf : 2 * u / 2 = u := by ring
  have htrig := Real.sin_sub u (u / 2)
  rw [show u - u / 2 = u / 2 by ring] at htrig
  have hscaled : (1 / (2 : ℝ) ^ n) * chapter9Entry13Integrand n (2 * u) =
      u ^ n / 2 * (Real.cos u / Real.sin u) := by
    unfold chapter9Entry13Integrand
    rw [hpow, hhalf]
    field_simp
  have hcot : 1 / Real.sin u = Real.cos (u / 2) / Real.sin (u / 2) -
      Real.cos u / Real.sin u := by
    field_simp
    linear_combination htrig
  unfold chapter9Entry14Integrand
  rw [hscaled]
  unfold chapter9Entry13Integrand
  calc
    u ^ n / 2 / Real.sin u = u ^ n / 2 * (1 / Real.sin u) := by ring
    _ = u ^ n / 2 * (Real.cos (u / 2) / Real.sin (u / 2) -
        Real.cos u / Real.sin u) := by rw [hcot]
    _ = u ^ n / 2 * (Real.cos (u / 2) / Real.sin (u / 2)) -
        u ^ n / 2 * (Real.cos u / Real.sin u) := by ring

private lemma xs_integral_reduce (n : ℕ) (x : ℝ) (hx : |x| < Real.pi)
    (hIx : IntervalIntegrable (chapter9Entry13Integrand n) volume 0 x)
    (hI2x : IntervalIntegrable (chapter9Entry13Integrand n) volume 0 (2 * x)) :
    (∫ u in (0 : ℝ)..x, chapter9Entry14Integrand n u) =
      (∫ u in (0 : ℝ)..x, chapter9Entry13Integrand n u) -
      (1 / (2 : ℝ) ^ (n + 1)) *
        ∫ u in (0 : ℝ)..(2 * x), chapter9Entry13Integrand n u := by
  have hsub := uIcc_subset_Ioo_of_abs_lt x hx
  have hcongr : (∫ u in (0 : ℝ)..x, chapter9Entry14Integrand n u) =
      ∫ u in (0 : ℝ)..x, chapter9Entry13Integrand n u -
        (1 / (2 : ℝ) ^ n) * chapter9Entry13Integrand n (2 * u) := by
    apply intervalIntegral.integral_congr_ae
    filter_upwards [MeasureTheory.Measure.ae_ne volume 0] with u hu0
    intro hu
    have huIoo := hsub (Set.uIoc_subset_uIcc hu)
    apply xs_integrand_eq_entry13 n u hu0
    exact abs_lt.mpr huIoo
  have hcomp : IntervalIntegrable
      (fun u : ℝ => chapter9Entry13Integrand n (2 * u)) volume 0 x := by
    have h := hI2x.comp_mul_left (c := (2 : ℝ))
    have hzero : (0 : ℝ) / 2 = 0 := by norm_num
    have hxdiv : 2 * x / 2 = x := by ring_nf
    rw [hzero, hxdiv] at h
    exact h
  have hscaled : IntervalIntegrable
      (fun u : ℝ => (1 / (2 : ℝ) ^ n) * chapter9Entry13Integrand n (2 * u))
      volume 0 x := hcomp.const_mul _
  have hchange := intervalIntegral.integral_comp_mul_left
    (f := chapter9Entry13Integrand n) (a := 0) (b := x) (c := (2 : ℝ)) (by norm_num)
  rw [hcongr, intervalIntegral.integral_sub hIx hscaled,
    intervalIntegral.integral_const_mul, hchange]
  simp only [smul_eq_mul]
  rw [pow_succ]
  ring_nf

private lemma xs_scale_pow (n j : ℕ) (x : ℝ) (hj : j ≤ n) :
    (1 / (2 : ℝ) ^ (n + 1)) * (2 * x) ^ (n - j) =
      (1 / (2 : ℝ) ^ (j + 1)) * x ^ (n - j) := by
  have hexp : n + 1 = (n - j) + (j + 1) := by omega
  rw [mul_pow, hexp, pow_add]
  field_simp

private lemma xs_sum_reduce (n : ℕ) (x : ℝ) (hx0 : x ≠ 0)
    (hx : |x| < Real.pi) :
    (∑ j ∈ range (n + 1),
        (-1 : ℝ) ^ (j * (j + 1) / 2) *
          (n.factorial : ℝ) / ((n - j).factorial : ℝ) *
          x ^ (n - j) * chapter9Clausen (j + 1) x) -
      (1 / (2 : ℝ) ^ (n + 1)) *
        ∑ j ∈ range (n + 1),
          (-1 : ℝ) ^ (j * (j + 1) / 2) *
            (n.factorial : ℝ) / ((n - j).factorial : ℝ) *
            (2 * x) ^ (n - j) * chapter9Clausen (j + 1) (2 * x) =
      ∑ j ∈ range (n + 1),
        (-1 : ℝ) ^ (j * (j + 1) / 2) *
          (n.factorial : ℝ) / ((n - j).factorial : ℝ) *
          x ^ (n - j) * chapter9OddClausen (j + 1) x := by
  rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro j hj
  have hjle : j ≤ n := by
    simp only [Finset.mem_range] at hj
    omega
  have hscale := xs_scale_pow n j x hjle
  have hcl := chapter9OddClausen_eq_clausen_sub (j + 1) x (by omega) hx0 hx
  calc
    (-1 : ℝ) ^ (j * (j + 1) / 2) * (n.factorial : ℝ) /
          ((n - j).factorial : ℝ) * x ^ (n - j) * chapter9Clausen (j + 1) x -
        (1 / (2 : ℝ) ^ (n + 1)) *
          ((-1 : ℝ) ^ (j * (j + 1) / 2) * (n.factorial : ℝ) /
            ((n - j).factorial : ℝ) * (2 * x) ^ (n - j) *
              chapter9Clausen (j + 1) (2 * x)) =
      ((-1 : ℝ) ^ (j * (j + 1) / 2) * (n.factorial : ℝ) /
          ((n - j).factorial : ℝ)) *
        (x ^ (n - j) * chapter9Clausen (j + 1) x -
          (1 / (2 : ℝ) ^ (n + 1)) * (2 * x) ^ (n - j) *
            chapter9Clausen (j + 1) (2 * x)) := by ring
    _ = ((-1 : ℝ) ^ (j * (j + 1) / 2) * (n.factorial : ℝ) /
          ((n - j).factorial : ℝ)) *
        (x ^ (n - j) * chapter9Clausen (j + 1) x -
          (1 / (2 : ℝ) ^ (j + 1)) * x ^ (n - j) *
            chapter9Clausen (j + 1) (2 * x)) := by rw [hscale]
    _ = ((-1 : ℝ) ^ (j * (j + 1) / 2) * (n.factorial : ℝ) /
          ((n - j).factorial : ℝ)) * x ^ (n - j) *
        (chapter9Clausen (j + 1) x -
          (1 / (2 : ℝ) ^ (j + 1)) * chapter9Clausen (j + 1) (2 * x)) := by ring
    _ = (-1 : ℝ) ^ (j * (j + 1) / 2) * (n.factorial : ℝ) /
          ((n - j).factorial : ℝ) * x ^ (n - j) *
            chapter9OddClausen (j + 1) x := by rw [← hcl]

private lemma xs_integral_formula (n : ℕ) (x : ℝ) (hn : 1 ≤ n)
    (hx0 : x ≠ 0) (hx : |x| < Real.pi) :
    (∫ u in (0 : ℝ)..x, chapter9Entry14Integrand n u) =
      Real.cos (n * Real.pi / 2) * n.factorial * chapter9ChiAtOne (n + 1) -
        ∑ j ∈ range (n + 1),
          (-1 : ℝ) ^ (j * (j + 1) / 2) *
            (n.factorial : ℝ) / ((n - j).factorial : ℝ) *
            x ^ (n - j) * chapter9OddClausen (j + 1) x := by
  have hx_two_pi : |x| < 2 * Real.pi := by
    nlinarith [Real.pi_pos]
  have h2x0 : 2 * x ≠ 0 := mul_ne_zero (by norm_num) hx0
  have h2x_two_pi : |2 * x| < 2 * Real.pi := by
    rw [abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 2)]
    nlinarith
  have hentry_x := ramanujan_part1_ch9_entry13_bernoulligen
    n x hn hx0 hx_two_pi
  have hentry_2x := ramanujan_part1_ch9_entry13_bernoulligen
    n (2 * x) hn h2x0 h2x_two_pi
  have hreduce := xs_integral_reduce n x hx hentry_x.1 hentry_2x.1
  rw [hentry_x.2.2.2, hentry_2x.2.2.2] at hreduce
  let scale : ℝ := 1 / (2 : ℝ) ^ (n + 1)
  let c : ℝ := Real.cos (n * Real.pi / 2) * n.factorial
  let z : ℝ := (riemannZeta ((n + 1 : ℕ) : ℂ)).re
  let sx : ℝ := ∑ j ∈ range (n + 1),
    (-1 : ℝ) ^ (j * (j + 1) / 2) * (n.factorial : ℝ) /
      ((n - j).factorial : ℝ) * x ^ (n - j) * chapter9Clausen (j + 1) x
  let s2x : ℝ := ∑ j ∈ range (n + 1),
    (-1 : ℝ) ^ (j * (j + 1) / 2) * (n.factorial : ℝ) /
      ((n - j).factorial : ℝ) * (2 * x) ^ (n - j) *
        chapter9Clausen (j + 1) (2 * x)
  let so : ℝ := ∑ j ∈ range (n + 1),
    (-1 : ℝ) ^ (j * (j + 1) / 2) * (n.factorial : ℝ) /
      ((n - j).factorial : ℝ) * x ^ (n - j) * chapter9OddClausen (j + 1) x
  have hreduce' : (∫ u in (0 : ℝ)..x, chapter9Entry14Integrand n u) =
      (c * z - sx) - scale * (c * z - s2x) := by
    simpa [scale, c, z, sx, s2x] using hreduce
  have hchi : chapter9ChiAtOne (n + 1) = (1 - scale) * z := by
    simpa [scale, z] using chapter9ChiAtOne_eq_zeta (n + 1) (by omega)
  have hsum : sx - scale * s2x = so := by
    simpa [scale, sx, s2x, so] using xs_sum_reduce n x hx0 hx
  calc
    (∫ u in (0 : ℝ)..x, chapter9Entry14Integrand n u) =
        (c * z - sx) - scale * (c * z - s2x) := hreduce'
    _ = c * ((1 - scale) * z) - (sx - scale * s2x) := by ring
    _ = c * chapter9ChiAtOne (n + 1) - so := by rw [← hchi, hsum]
    _ = Real.cos (n * Real.pi / 2) * n.factorial * chapter9ChiAtOne (n + 1) -
        ∑ j ∈ range (n + 1),
          (-1 : ℝ) ^ (j * (j + 1) / 2) *
            (n.factorial : ℝ) / ((n - j).factorial : ℝ) *
            x ^ (n - j) * chapter9OddClausen (j + 1) x := by
      rfl

/-- Source: Bruce C. Berndt, Ramanujan's Notebooks, Part I, Chapter 9.

Proves `Wanted` entry `ramanujan_part1_ch9_entry14_xoversin`.

Proof: Subtracts a scaled Entry 13 identity at `2x` from the identity at `x`, then
splits the zeta and Clausen series into even and odd frequencies, following Berndt
and Lewin, *Polylogarithms and Associated Functions*, Chapter 4.
-/
theorem ramanujan_part1_ch9_entry14_xoversin (n : ℕ) (x : ℝ)
    (hn : 1 ≤ n) (hx0 : x ≠ 0) (hx : |x| < Real.pi) :
    IntervalIntegrable (chapter9Entry14Integrand n) volume 0 x ∧
      Summable (fun k : ℕ =>
        1 / (((2 * k + 1 : ℕ) : ℝ) ^ (n + 1))) ∧
      Tendsto
        (fun N : ℕ => ∑ k ∈ range N,
          Real.cos (((2 * k + 1 : ℕ) : ℝ) * x) /
            ((2 * k + 1 : ℕ) : ℝ))
        atTop (𝓝 (chapter9OddClausen 1 x)) ∧
      (∀ m : ℕ, 2 ≤ m → m ≤ n + 1 →
        Summable (chapter9OddClausenTerm m x)) ∧
      (∫ u in (0 : ℝ)..x, chapter9Entry14Integrand n u) =
        Real.cos (n * Real.pi / 2) * n.factorial *
            chapter9ChiAtOne (n + 1) -
          ∑ j ∈ range (n + 1),
            (-1 : ℝ) ^ (j * (j + 1) / 2) *
              (n.factorial : ℝ) / ((n - j).factorial : ℝ) *
              x ^ (n - j) * chapter9OddClausen (j + 1) x := by
  refine ⟨helper_integrand_integrable n x hn hx, helper_chi_summable n hn,
    xs_cos_series_tendsto x hx0 hx, ?_, xs_integral_formula n x hn hx0 hx⟩
  intro m hm _
  exact chapter9OddClausenTerm_summable_of_two_le m x hm

end
end Entry14Xoversin
end MathlibExt.Analysis.Ramanujan.Part1Ch9
end
