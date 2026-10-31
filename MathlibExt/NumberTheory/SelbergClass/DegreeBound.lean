/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.NumberTheory.SelbergClass.Basic
import Mathlib.Analysis.Complex.PhragmenLindelof
import Mathlib.Analysis.SpecialFunctions.Gamma.Beta
import Mathlib.Analysis.Normed.Module.Connected
import Mathlib.Analysis.SpecialFunctions.Complex.LogDeriv
import MathlibExt.Analysis.SpecialFunctions.Gamma.Vertical
import MathlibExt.Analysis.Complex.RectangleResidue

/-!
# No functions of degree between `0` and `1` in the Selberg class

A theorem of Selberg (with the proof of Conrey and Ghosh): a member of the Selberg class whose
functional equation has positive degree has degree at least `1`.

Write `F` for the continuation of `L(a, s)`. The Mellin–Barnes integral
`∑ a n e^{-n x} = (1/2π) ∫ F(2 + it) Γ(2 + it) x^{-2-it} dt` is shifted to the left across the
poles of `Γ` at `0, -1, -2, …`, using the functional equation and Stirling's formula to bound
`F(s) Γ(s)` on the lines `Re s = -N - 1/2`. When the degree `d` is less than `1` the error terms
decay faster than any geometric sequence, so `∑ a n e^{-n x} = R(log x) + ∑ c_n x^n` with `R` and
the power series entire. Hence `z ↦ ∑ a n e^{-n z}` continues to a `2πi`-periodic function
holomorphic on the upper half-plane, and its coefficients decay like `a n = O(e^{-n})`. Then
`L(a, s)` is bounded on every vertical line, while by Stirling's formula the functional equation
of positive degree makes `F(1 - σ + it)` grow like `|t|^{d(σ - 1/2)}`: a contradiction.

## Main statements

* `SelbergClass.one_le_degree_of_pos`: if `0 < deg D` then `1 ≤ deg D`.
-/

open ArithmeticFunction SelbergClass

@[expose] public section

namespace SelbergClass


open Complex Filter Topology MeasureTheory in
/-- Shifting a vertical line integral across a strip: the difference of the two line
integrals is the boundary integral of the box `[a, b] × [-1, 1]`. -/
private lemma sub_integral_vertical_eq_box (h : ℂ → ℂ) (a b : ℝ) (hab : a ≤ b)
    (hd : ∀ s : ℂ, a ≤ s.re → s.re ≤ b → 1 ≤ |s.im| → DifferentiableAt ℂ h s)
    (hia : Integrable (fun t : ℝ => h (a + t * I)))
    (hib : Integrable (fun t : ℝ => h (b + t * I)))
    (hdec : ∀ ε > (0 : ℝ), ∃ T₀, ∀ s : ℂ, a ≤ s.re → s.re ≤ b → T₀ ≤ |s.im| → ‖h s‖ ≤ ε) :
    I * ((∫ t : ℝ, h (b + t * I)) - ∫ t : ℝ, h (a + t * I)) =
      (∫ x : ℝ in a..b, h (x + (-1 : ℝ) * I)) - (∫ x : ℝ in a..b, h (x + (1 : ℝ) * I)) +
        I * (∫ y : ℝ in (-1 : ℝ)..1, h (b + y * I)) - I * ∫ y : ℝ in (-1 : ℝ)..1, h (a + y * I) :=
            by
  set box := (∫ x : ℝ in a..b, h (x + (-1 : ℝ) * I)) - (∫ x : ℝ in a..b, h (x + (1 : ℝ) * I)) +
        I * (∫ y : ℝ in (-1 : ℝ)..1, h (b + y * I)) - I * ∫ y : ℝ in (-1 : ℝ)..1, h (a + y * I)
    with hbox
  have key : ∀ T : ℝ, 1 ≤ T →
      I * ((∫ y : ℝ in (-T)..T, h (b + y * I)) - ∫ y : ℝ in (-T)..T, h (a + y * I)) =
        box + ((∫ x : ℝ in a..b, h (x + T * I)) - ∫ x : ℝ in a..b, h (x + (-T) * I)) := by
    intro T hT
    have H1 := Complex.integral_boundary_rect_eq_zero_of_differentiableOn h ⟨a, 1⟩ ⟨b, T⟩ (by
      intro z hz
      simp only [Complex.mem_reProdIm, Set.uIcc_of_le hab, Set.uIcc_of_le hT, Set.mem_Icc] at hz
      exact (hd z hz.1.1 hz.1.2 (by rw [abs_of_nonneg (by linarith)]; exact
          hz.2.1)).differentiableWithinAt)
    have H2 := Complex.integral_boundary_rect_eq_zero_of_differentiableOn h ⟨a, -T⟩ ⟨b, -1⟩ (by
      intro z hz
      simp only [Complex.mem_reProdIm, Set.uIcc_of_le hab,
        Set.uIcc_of_le (show -T ≤ -1 by linarith), Set.mem_Icc] at hz
      exact (hd z hz.1.1 hz.1.2
        (by rw [abs_of_nonpos (by linarith)]; linarith)).differentiableWithinAt)
    simp only [smul_eq_mul] at H1 H2
    have hIa : ∀ u v : ℝ, IntervalIntegrable (fun y : ℝ => h (a + y * I)) volume u v :=
      fun u v => hia.intervalIntegrable
    have hIb : ∀ u v : ℝ, IntervalIntegrable (fun y : ℝ => h (b + y * I)) volume u v :=
      fun u v => hib.intervalIntegrable
    have sa : (∫ y : ℝ in (-T)..T, h (a + y * I)) = (∫ y : ℝ in (-T)..(-1), h (a + y * I)) +
        (∫ y : ℝ in (-1 : ℝ)..1, h (a + y * I)) + ∫ y : ℝ in (1 : ℝ)..T, h (a + y * I) := by
      rw [intervalIntegral.integral_add_adjacent_intervals (hIa _ _) (hIa _ _),
        intervalIntegral.integral_add_adjacent_intervals (hIa _ _) (hIa _ _)]
    have sb : (∫ y : ℝ in (-T)..T, h (b + y * I)) = (∫ y : ℝ in (-T)..(-1), h (b + y * I)) +
        (∫ y : ℝ in (-1 : ℝ)..1, h (b + y * I)) + ∫ y : ℝ in (1 : ℝ)..T, h (b + y * I) := by
      rw [intervalIntegral.integral_add_adjacent_intervals (hIb _ _) (hIb _ _),
        intervalIntegral.integral_add_adjacent_intervals (hIb _ _) (hIb _ _)]
    rw [sa, sb, hbox]
    push_cast at H1 H2 ⊢
    linear_combination H1 + H2
  -- limits
  have hL : Tendsto (fun T : ℝ =>
      I * ((∫ y : ℝ in (-T)..T, h (b + y * I)) - ∫ y : ℝ in (-T)..T, h (a + y * I))) atTop
      (𝓝 (I * ((∫ t : ℝ, h (b + t * I)) - ∫ t : ℝ, h (a + t * I)))) := by
    have h1 := intervalIntegral_tendsto_integral hib tendsto_neg_atTop_atBot tendsto_id
    have h2 := intervalIntegral_tendsto_integral hia tendsto_neg_atTop_atBot tendsto_id
    exact (h1.sub h2).const_mul I
  have hR : Tendsto (fun T : ℝ =>
      box + ((∫ x : ℝ in a..b, h (x + T * I)) - ∫ x : ℝ in a..b, h (x + (-T) * I))) atTop
      (𝓝 box) := by
    have hz : Tendsto (fun T : ℝ =>
        (∫ x : ℝ in a..b, h (x + T * I)) - ∫ x : ℝ in a..b, h (x + (-T) * I)) atTop (𝓝 0) := by
      rw [Metric.tendsto_atTop]
      intro ε hε
      obtain ⟨T₀, hT₀⟩ := hdec (ε / (2 * (b - a + 1))) (by
        have : 0 < b - a + 1 := by linarith
        positivity)
      refine ⟨max T₀ 1, fun T hT => ?_⟩
      have hT1 : T₀ ≤ T := le_trans (le_max_left _ _) hT
      have hbd : ∀ c : ℝ, T₀ ≤ |c| → ‖∫ x : ℝ in a..b, h (x + c * I)‖ ≤
          ε / (2 * (b - a + 1)) * |b - a| := by
        intro c hc
        apply intervalIntegral.norm_integral_le_of_norm_le_const
        intro x hx
        rw [Set.uIoc_of_le hab] at hx
        apply hT₀
        · simp; linarith [hx.1]
        · simp; linarith [hx.2]
        · simpa using hc
      rw [dist_zero_right]
      have e1 := hbd T (by rw [abs_of_nonneg (by linarith [le_max_right T₀ 1])]; exact hT1)
      have e2 := hbd (-T) (by rw [abs_neg, abs_of_nonneg (by linarith [le_max_right T₀ 1])]; exact
          hT1)
      have hab' : |b - a| = b - a := abs_of_nonneg (by linarith)
      rw [hab'] at e1 e2
      push_cast at e2
      calc _ ≤ _ := norm_sub_le _ _
        _ ≤ ε / (2 * (b - a + 1)) * (b - a) + ε / (2 * (b - a + 1)) * (b - a) := add_le_add e1 e2
        _ < ε := by
          have : 0 < b - a + 1 := by linarith
          rw [← mul_two, div_mul_eq_mul_div, div_mul_eq_mul_div, div_lt_iff₀ (by positivity)]
          nlinarith
    simpa using (tendsto_const_nhds (x := box)).add hz
  have hR' : Tendsto (fun T : ℝ =>
      I * ((∫ y : ℝ in (-T)..T, h (b + y * I)) - ∫ y : ℝ in (-T)..T, h (a + y * I))) atTop
      (𝓝 box) := by
    refine hR.congr' ?_
    filter_upwards [eventually_ge_atTop 1] with T hT
    exact (key T hT).symm
  exact tendsto_nhds_unique hL hR'

open Complex Filter Topology MeasureTheory in
/-- Phragmén–Lindelöf on a closed vertical strip, for a function of finite order. -/
private lemma bounded_strip_of_finite_order (φ : ℂ → ℂ) (a b : ℝ) (hab : a < b)
    (hd : ∀ s : ℂ, a ≤ s.re → s.re ≤ b → DifferentiableAt ℂ φ s)
    (k C R : ℝ) (hk : 0 ≤ k)
    (hg : ∀ s : ℂ, a ≤ s.re → s.re ≤ b → R ≤ ‖s‖ → ‖φ s‖ ≤ C * Real.exp (‖s‖ ^ k))
    (M : ℝ) (hM : ∀ s : ℂ, (s.re = a ∨ s.re = b) → ‖φ s‖ ≤ M) :
    ∀ s : ℂ, a ≤ s.re → s.re ≤ b → ‖φ s‖ ≤ M := by
  set A : ℝ := |a| + |b| with hA
  have hA0 : 0 ≤ A := by positivity
  set c : ℝ := Real.pi / (2 * (b - a)) with hc
  have hba : 0 < b - a := by linarith
  have hc0 : 0 < c := by positivity
  have hcl : c < Real.pi / (b - a) := by
    rw [hc, div_lt_div_iff₀ (by positivity) hba]
    nlinarith [Real.pi_pos]
  have hlim : ∀ᶠ y : ℝ in atTop, (y + A) ^ k ≤ Real.exp (c * y) := by
    have h1 := (tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero k c hc0).comp
      (tendsto_atTop_add_const_right atTop A tendsto_id)
    have h2 := h1.eventually (gt_mem_nhds (show (0 : ℝ) < Real.exp (-c * A) by positivity))
    filter_upwards [h2] with y hy
    simp only [Function.comp_apply, id] at hy
    have e : Real.exp (-c * (y + A)) = Real.exp (-c * A) * Real.exp (-(c * y)) := by
      rw [← Real.exp_add]; ring_nf
    rw [e] at hy
    have hy' : (y + A) ^ k * Real.exp (-(c * y)) < 1 := by
      have := Real.exp_pos (-c * A)
      nlinarith [Real.exp_pos (-(c * y))]
    calc (y + A) ^ k = (y + A) ^ k * Real.exp (-(c * y)) * Real.exp (c * y) := by
          rw [mul_assoc, ← Real.exp_add]; simp
      _ ≤ 1 * Real.exp (c * y) := by gcongr
      _ = Real.exp (c * y) := one_mul _
  rw [eventually_atTop] at hlim
  obtain ⟨Y0, hY0⟩ := hlim
  have hgrowth : ∃ c' < Real.pi / (b - a), ∃ B, φ =O[comap (_root_.abs ∘ Complex.im) atTop ⊓
      Filter.principal (Complex.re ⁻¹' Set.Ioo a b)]
      fun z => Real.exp (B * Real.exp (c' * |z.im|)) := by
    refine ⟨c, hcl, 1, ?_⟩
    refine Asymptotics.IsBigO.of_bound |C| ?_
    rw [Filter.eventually_inf_principal, Filter.eventually_comap, Filter.eventually_atTop]
    refine ⟨max (max Y0 R) 0, fun y hy z hz hzs => ?_⟩
    simp only [Function.comp_apply] at hz
    simp only [Set.mem_preimage, Set.mem_Ioo] at hzs
    have hyY : Y0 ≤ y := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hy
    have hyR : R ≤ y := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hy
    have hy0 : 0 ≤ y := le_trans (le_max_right _ _) hy
    have hnz : ‖z‖ ≤ y + A := by
      calc ‖z‖ ≤ |z.re| + |z.im| := Complex.norm_le_abs_re_add_abs_im z
        _ ≤ A + y := by
          rw [hz]; gcongr
          rw [hA, abs_le]
          constructor
          · have := neg_abs_le a; have := abs_nonneg b; linarith
          · have := le_abs_self b; have := abs_nonneg a; linarith
        _ = y + A := by ring
    have hRz : R ≤ ‖z‖ := hyR.trans (hz ▸ Complex.abs_im_le_norm z)
    have hφ := hg z hzs.1.le hzs.2.le hRz
    calc ‖φ z‖ ≤ C * Real.exp (‖z‖ ^ k) := hφ
      _ ≤ |C| * Real.exp (‖z‖ ^ k) := by gcongr; exact le_abs_self C
      _ ≤ |C| * ‖Real.exp (1 * Real.exp (c * |z.im|))‖ := by
          gcongr
          rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
          apply Real.exp_le_exp.2
          rw [hz, one_mul]
          calc ‖z‖ ^ k ≤ (y + A) ^ k := Real.rpow_le_rpow (norm_nonneg _) hnz hk
            _ ≤ Real.exp (c * y) := hY0 y hyY
  have hdc : DiffContOnCl ℂ φ (Complex.re ⁻¹' Set.Ioo a b) := by
    apply DifferentiableOn.diffContOnCl
    have hcl : closure (Complex.re ⁻¹' Set.Ioo a b) ⊆ Complex.re ⁻¹' Set.Icc a b :=
      closure_minimal (Set.preimage_mono Set.Ioo_subset_Icc_self)
        (isClosed_Icc.preimage Complex.continuous_re)
    intro z hz
    have hz' := hcl hz
    simp only [Set.mem_preimage, Set.mem_Icc] at hz'
    exact (hd z hz'.1 hz'.2).differentiableWithinAt
  intro s h1 h2
  exact PhragmenLindelof.vertical_strip hdc hgrowth (fun z hz => hM z (Or.inl hz))
    (fun z hz => hM z (Or.inr hz)) h1 h2

open Complex Filter Topology MeasureTheory in
/-- `Γ(s + n) = Γ(s) ∏_{k < n} (s + k)` away from the poles. -/
private lemma Gamma_add_nat_eq_prod_mul (s : ℂ) (hs : ∀ k : ℕ, s ≠ -k) (n : ℕ) :
    Complex.Gamma (s + n) = Complex.Gamma s * ∏ k ∈ Finset.range n, (s + k) := by
  induction n with
  | zero => simp
  | succ n ih =>
    have hne : s + n ≠ 0 := by
      intro h; apply hs n; linear_combination h
    rw [Finset.prod_range_succ, show s + ((n + 1 : ℕ) : ℂ) = (s + n) + 1 by push_cast; ring,
      Complex.Gamma_add_one _ hne, ih]
    ring

open Complex Filter Topology MeasureTheory in
/-- `‖sin z‖ ≤ e^{|Im z|}`. -/
private lemma norm_sin_le_exp_abs_im (z : ℂ) : ‖Complex.sin z‖ ≤ Real.exp |z.im| := by
  rw [Complex.sin]
  have h1 : ‖Complex.exp (-z * I)‖ = Real.exp z.im := by
    rw [Complex.norm_exp]; simp
  have h2 : ‖Complex.exp (z * I)‖ = Real.exp (-z.im) := by
    rw [Complex.norm_exp]; simp
  rw [norm_div, norm_mul, Complex.norm_I, mul_one, Complex.norm_two]
  calc ‖Complex.exp (-z * I) - Complex.exp (z * I)‖ / 2
      ≤ (‖Complex.exp (-z * I)‖ + ‖Complex.exp (z * I)‖) / 2 := by gcongr; exact norm_sub_le _ _
    _ = (Real.exp z.im + Real.exp (-z.im)) / 2 := by rw [h1, h2]
    _ ≤ (Real.exp |z.im| + Real.exp |z.im|) / 2 := by
        gcongr
        · exact le_abs_self _
        · exact neg_le_abs _
    _ = Real.exp |z.im| := by ring

open Complex Filter Topology MeasureTheory in
/-- `‖1/Γ(w)‖ ≤ Γ(1 - Re w) e^{π |Im w|} / π` when `Re w < 1`. -/
private lemma norm_inv_Gamma_le (w : ℂ) (hw : 0 < 1 - w.re) :
    ‖(Complex.Gamma w)⁻¹‖ ≤ Real.Gamma (1 - w.re) * Real.exp (Real.pi * |w.im|) / Real.pi := by
  have hpos : 0 ≤ Real.Gamma (1 - w.re) * Real.exp (Real.pi * |w.im|) / Real.pi := by
    have := Real.Gamma_pos_of_pos hw
    positivity
  by_cases h0 : Complex.Gamma w = 0
  · rw [h0, inv_zero, norm_zero]; exact hpos
  have h1 : Complex.Gamma (1 - w) ≠ 0 := Complex.Gamma_ne_zero_of_re_pos (by simpa using hw)
  have href := Complex.Gamma_mul_Gamma_one_sub w
  have hsin : Complex.sin (Real.pi * w) ≠ 0 := by
    intro hs
    rw [hs, div_zero] at href
    exact mul_ne_zero h0 h1 href
  have e : (Complex.Gamma w)⁻¹ = Complex.Gamma (1 - w) * Complex.sin (Real.pi * w) / Real.pi := by
    rw [mul_comm] at href
    have := congrArg (fun x => x * Complex.sin (Real.pi * w)) href
    rw [div_mul_cancel₀ _ hsin] at this
    have hpi : (Real.pi : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
    rw [eq_div_iff hpi, inv_mul_eq_iff_eq_mul₀ h0]
    linear_combination -this
  rw [e, norm_div, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos Real.pi_pos]
  have hG := Complex.norm_Gamma_le_Gamma_re (s := 1 - w) (by simpa using hw)
  have hS := norm_sin_le_exp_abs_im (Real.pi * w)
  have him : ((Real.pi : ℂ) * w).im = Real.pi * w.im := by simp
  rw [him, abs_mul, abs_of_pos Real.pi_pos] at hS
  have hre : (1 - w).re = 1 - w.re := by simp
  rw [hre] at hG
  gcongr

open Complex Filter Topology MeasureTheory in
/-- `‖Γ(1/2 + it)‖ ≤ √(2π) e^{-π|t|/2}`. -/
private lemma norm_Gamma_half_add_mul_I_le (t : ℝ) :
    ‖Complex.Gamma (1 / 2 + t * I)‖ ≤ Real.sqrt (2 * Real.pi) * Real.exp (-(Real.pi * |t|) / 2) :=
        by
  set z : ℂ := 1 / 2 + t * I with hz
  have hc : 1 - z = (starRingEnd ℂ) z := by
    apply Complex.ext <;> (simp [hz]; try norm_num)
  have href := Complex.Gamma_mul_Gamma_one_sub z
  rw [hc, Complex.Gamma_conj, Complex.mul_conj, Complex.normSq_eq_norm_sq] at href
  have hs : Complex.sin (Real.pi * z) = Real.cosh (Real.pi * t) := by
    rw [hz, mul_add, Complex.sin_add, show (Real.pi : ℂ) * (1 / 2) = (Real.pi / 2 : ℝ) by
      push_cast; ring]
    rw [show (Real.pi : ℂ) * (t * I) = ((Real.pi * t : ℝ) : ℂ) * I by push_cast; ring,
      Complex.sin_mul_I, Complex.cos_mul_I]
    rw [← Complex.ofReal_sin, ← Complex.ofReal_cos, Real.sin_pi_div_two, Real.cos_pi_div_two]
    push_cast; ring
  rw [hs] at href
  have hcosh : Real.exp (Real.pi * |t|) / 2 ≤ Real.cosh (Real.pi * t) := by
    rw [Real.cosh_eq]
    rcases le_or_gt 0 t with ht | ht
    · rw [abs_of_nonneg ht]; have := Real.exp_pos (-(Real.pi * t)); linarith
    · rw [abs_of_neg ht]
      have := Real.exp_pos (Real.pi * t)
      have e : Real.pi * -t = -(Real.pi * t) := by ring
      rw [e]; linarith
  have hcpos : 0 < Real.cosh (Real.pi * t) := Real.cosh_pos _
  have hsq : ‖Complex.Gamma z‖ ^ 2 = Real.pi / Real.cosh (Real.pi * t) := by
    have := congrArg Complex.re href
    simp only [Complex.ofReal_re] at this
    rw [this, ← Complex.ofReal_div, Complex.ofReal_re]
  have hle : ‖Complex.Gamma z‖ ^ 2 ≤
      (Real.sqrt (2 * Real.pi) * Real.exp (-(Real.pi * |t|) / 2)) ^ 2 := by
    rw [hsq, mul_pow, Real.sq_sqrt (by positivity), ← Real.exp_nat_mul]
    rw [div_le_iff₀ hcpos]
    have e : ((2 : ℕ) : ℝ) * (-(Real.pi * |t|) / 2) = -(Real.pi * |t|) := by push_cast; ring
    rw [e]
    have hE : Real.exp (-(Real.pi * |t|)) * Real.exp (Real.pi * |t|) = 1 := by
      rw [← Real.exp_add]; simp
    have hm := mul_le_mul_of_nonneg_left hcosh
      (show 0 ≤ 2 * Real.pi * Real.exp (-(Real.pi * |t|)) by positivity)
    have : 2 * Real.pi * Real.exp (-(Real.pi * |t|)) * (Real.exp (Real.pi * |t|) / 2) = Real.pi :=
        by
      rw [show 2 * Real.pi * Real.exp (-(Real.pi * |t|)) * (Real.exp (Real.pi * |t|) / 2) =
        Real.pi * (Real.exp (-(Real.pi * |t|)) * Real.exp (Real.pi * |t|)) by ring, hE, mul_one]
    linarith
  exact (pow_le_pow_iff_left₀ (norm_nonneg _) (by positivity) two_ne_zero).1 hle

open Complex Filter Topology MeasureTheory in
/-- On the line `Re s = -N - 1/2`: `‖Γ(s)‖ ∏_{j ≤ N} (j + 1/2) ≤ √(2π) e^{-π|t|/2}`. -/
private lemma norm_Gamma_neg_half_line_mul_prod_le (N : ℕ) (t : ℝ) :
    ‖Complex.Gamma (-(N : ℂ) - 1 / 2 + t * I)‖ * ∏ j ∈ Finset.range (N + 1), ((j : ℝ) + 1 / 2) ≤
      Real.sqrt (2 * Real.pi) * Real.exp (-(Real.pi * |t|) / 2) := by
  set s : ℂ := -(N : ℂ) - 1 / 2 + t * I with hs
  have hpole : ∀ k : ℕ, s ≠ -k := by
    intro k h
    have := congrArg Complex.re h
    simp only [hs, one_div, add_re, sub_re, neg_re, natCast_re, inv_re, re_ofNat, normSq_ofNat,
        div_self_mul_self', mul_re, ofReal_re, I_re, mul_zero, ofReal_im, I_im, mul_one, sub_self,
        add_zero] at this
    have h2 : (2 * (k : ℝ)) = 2 * N + 1 := by linarith
    have h3 : (2 * k : ℕ) = 2 * N + 1 := by exact_mod_cast h2
    omega
  have e := Gamma_add_nat_eq_prod_mul s hpole (N + 1)
  have hsN : s + ((N + 1 : ℕ) : ℂ) = 1 / 2 + t * I := by rw [hs]; push_cast; ring
  rw [hsN] at e
  have hb := norm_Gamma_half_add_mul_I_le t
  rw [e, norm_mul, norm_prod] at hb
  refine le_trans ?_ hb
  have hrefl : ∏ j ∈ Finset.range (N + 1), ((j : ℝ) + 1 / 2) =
      ∏ k ∈ Finset.range (N + 1), (((N - k : ℕ) : ℝ) + 1 / 2) := by
    rw [← Finset.prod_range_reflect (fun j : ℕ => ((j : ℝ) + 1 / 2)) (N + 1)]
    apply Finset.prod_congr rfl
    intro k hk
    congr 2
  rw [hrefl]
  gcongr with k hk
  have hk' : k ≤ N := Nat.lt_succ_iff.1 (Finset.mem_range.1 hk)
  refine le_trans ?_ (Complex.abs_re_le_norm _)
  have : (s + k).re = -(((N - k : ℕ) : ℝ) + 1 / 2) := by
    simp [hs, Nat.cast_sub hk']; ring
  rw [this, abs_neg, abs_of_pos (by positivity)]

open Complex Filter Topology MeasureTheory in
/-- The bound for `F(s) Γ(s)` on the line `Re s = -N - 1/2`, from the functional equation. -/
private lemma norm_mul_Gamma_line_le (F : ℂ → ℂ) (D : FunctionalEquation F) (K : ℝ)
    (hfe : ∀ s : ℂ, s.re < 1 → s ≠ 0 → F s = (D.Q : ℂ) ^ (-s) *
      (∏ i, (Complex.Gamma (D.α i * s + D.r i))⁻¹) *
      (D.w * starRingEnd ℂ ((D.Q : ℂ) ^ (1 - starRingEnd ℂ s) *
        (∏ i, Complex.Gamma (D.α i * (1 - starRingEnd ℂ s) + D.r i)) *
          F (1 - starRingEnd ℂ s))))
    (hK : ∀ s : ℂ, 3 / 2 ≤ s.re → ‖F s‖ ≤ K)
    (N : ℕ) (hN : ∀ i, (D.r i).re ≤ D.α i * N) (t : ℝ) :
    ‖F (-(N : ℂ) - 1 / 2 + t * I) * Complex.Gamma (-(N : ℂ) - 1 / 2 + t * I)‖ ≤
      K * D.Q ^ (2 * N + 2) * (∏ i, (Real.Gamma (D.α i * (N + 3 / 2) + (D.r i).re) *
        Real.Gamma (1 + D.α i * (N + 1 / 2) - (D.r i).re) *
          Real.exp (Real.pi * |(D.r i).im|) / Real.pi)) *
        (Real.sqrt (2 * Real.pi) / ∏ j ∈ Finset.range (N + 1), ((j : ℝ) + 1 / 2)) *
        Real.exp (-(Real.pi * (1 - D.degree) / 2) * |t|) := by
  set s : ℂ := -(N : ℂ) - 1 / 2 + t * I with hs
  have hsre : s.re = -(N : ℝ) - 1 / 2 := by simp [hs]
  have hsim : s.im = t := by simp [hs]
  have hs1 : s.re < 1 := by rw [hsre]; have := Nat.cast_nonneg (α := ℝ) N; linarith
  have hs0 : s ≠ 0 := by
    intro h; have := congrArg Complex.re h; rw [hsre] at this; simp at this
    have := Nat.cast_nonneg (α := ℝ) N; linarith
  set u : ℂ := 1 - starRingEnd ℂ s with hu
  have hure : u.re = (N : ℝ) + 3 / 2 := by simp [hu, hsre]; ring
  have huim : u.im = t := by simp [hu, hsim]
  have hQ := D.Q_pos
  have hK0 : 0 ≤ K := le_trans (norm_nonneg _)
    (hK u (by rw [hure]; have := Nat.cast_nonneg (α := ℝ) N; linarith))
  have e := hfe s hs1 hs0
  rw [← hu] at e
  -- per-factor bound
  set g : Fin D.d → ℝ := fun i => Real.Gamma (D.α i * (N + 3 / 2) + (D.r i).re) *
        Real.Gamma (1 + D.α i * (N + 1 / 2) - (D.r i).re) *
          Real.exp (Real.pi * |(D.r i).im|) / Real.pi with hg
  have hfac : ∀ i, ‖(Complex.Gamma (D.α i * s + D.r i))⁻¹‖ *
      ‖Complex.Gamma (D.α i * u + D.r i)‖ ≤ g i * Real.exp (Real.pi * D.α i * |t|) := by
    intro i
    have hα := D.α_pos i
    have hρ := D.r_re_nonneg i
    have h1re : (D.α i * s + D.r i : ℂ).re = -(D.α i * (N + 1 / 2)) + (D.r i).re := by
      simp [hsre]; ring
    have h1im : (D.α i * s + D.r i : ℂ).im = D.α i * t + (D.r i).im := by
      simp [hsim]
    have h2re : (D.α i * u + D.r i : ℂ).re = D.α i * (N + 3 / 2) + (D.r i).re := by
      simp [hure]
    have hpos1 : 0 < 1 - (D.α i * s + D.r i : ℂ).re := by
      rw [h1re]; have := hN i; nlinarith
    have hA := norm_inv_Gamma_le _ hpos1
    rw [h1re, h1im] at hA
    have hB := Complex.norm_Gamma_le_Gamma_re (s := D.α i * u + D.r i) (by
      rw [h2re]; have := Nat.cast_nonneg (α := ℝ) N; positivity)
    rw [h2re] at hB
    have hexp : Real.exp (Real.pi * |D.α i * t + (D.r i).im|) ≤
        Real.exp (Real.pi * D.α i * |t|) * Real.exp (Real.pi * |(D.r i).im|) := by
      rw [← Real.exp_add]
      apply Real.exp_le_exp.2
      have := abs_add_le (D.α i * t) (D.r i).im
      rw [abs_mul, abs_of_pos hα] at this
      nlinarith [Real.pi_pos]
    have hG1 : 0 ≤ Real.Gamma (1 - (-(D.α i * (N + 1 / 2)) + (D.r i).re)) :=
      Real.Gamma_nonneg_of_nonneg (by have := hN i; nlinarith)
    have hG2 : 0 ≤ Real.Gamma (D.α i * (N + 3 / 2) + (D.r i).re) :=
      Real.Gamma_nonneg_of_nonneg (by have := Nat.cast_nonneg (α := ℝ) N; positivity)
    calc ‖(Complex.Gamma (D.α i * s + D.r i))⁻¹‖ * ‖Complex.Gamma (D.α i * u + D.r i)‖
        ≤ (Real.Gamma (1 - (-(D.α i * (N + 1 / 2)) + (D.r i).re)) *
            Real.exp (Real.pi * |D.α i * t + (D.r i).im|) / Real.pi) *
          Real.Gamma (D.α i * (N + 3 / 2) + (D.r i).re) :=
          mul_le_mul hA hB (norm_nonneg _) (by positivity)
      _ ≤ (Real.Gamma (1 - (-(D.α i * (N + 1 / 2)) + (D.r i).re)) *
            (Real.exp (Real.pi * D.α i * |t|) * Real.exp (Real.pi * |(D.r i).im|)) / Real.pi) *
          Real.Gamma (D.α i * (N + 3 / 2) + (D.r i).re) := by gcongr
      _ = g i * Real.exp (Real.pi * D.α i * |t|) := by
          simp only [hg]
          rw [show 1 - (-(D.α i * (N + 1 / 2)) + (D.r i).re) =
            1 + D.α i * (N + 1 / 2) - (D.r i).re by ring]
          ring
  have hprod : (∏ i, ‖(Complex.Gamma (D.α i * s + D.r i))⁻¹‖) *
      (∏ i, ‖Complex.Gamma (D.α i * u + D.r i)‖) ≤
      (∏ i, g i) * Real.exp (Real.pi * (∑ i, D.α i) * |t|) := by
    rw [← Finset.prod_mul_distrib]
    calc ∏ i, ‖(Complex.Gamma (D.α i * s + D.r i))⁻¹‖ * ‖Complex.Gamma (D.α i * u + D.r i)‖
        ≤ ∏ i, (g i * Real.exp (Real.pi * D.α i * |t|)) :=
          Finset.prod_le_prod₀ (fun i _ => by positivity) (fun i _ => hfac i)
      _ = (∏ i, g i) * Real.exp (Real.pi * (∑ i, D.α i) * |t|) := by
          rw [Finset.prod_mul_distrib, ← Real.exp_sum, Finset.mul_sum, Finset.sum_mul]
  -- norms of the powers of `Q`
  have hQs : ‖(D.Q : ℂ) ^ (-s)‖ = D.Q ^ ((N : ℝ) + 1 / 2) := by
    rw [Complex.norm_cpow_eq_rpow_re_of_pos hQ]; congr 1; simp [hsre]; ring
  have hQu : ‖(D.Q : ℂ) ^ u‖ = D.Q ^ ((N : ℝ) + 3 / 2) := by
    rw [Complex.norm_cpow_eq_rpow_re_of_pos hQ, hure]
  have hQQ : D.Q ^ ((N : ℝ) + 1 / 2) * D.Q ^ ((N : ℝ) + 3 / 2) = D.Q ^ (2 * N + 2) := by
    rw [← Real.rpow_add hQ, show (N : ℝ) + 1 / 2 + ((N : ℝ) + 3 / 2) = ((2 * N + 2 : ℕ) : ℝ) by
      push_cast; ring, Real.rpow_natCast]
  have hFs : ‖F s‖ = D.Q ^ (2 * N + 2) * ((∏ i, ‖(Complex.Gamma (D.α i * s + D.r i))⁻¹‖) *
      (∏ i, ‖Complex.Gamma (D.α i * u + D.r i)‖)) * ‖F u‖ := by
    rw [e]
    simp only [norm_mul, norm_prod, Complex.norm_conj, D.norm_w, one_mul, hQs, hQu]
    rw [← hQQ]; ring
  have hFu := hK u (by rw [hure]; have := Nat.cast_nonneg (α := ℝ) N; linarith)
  have hGs := norm_Gamma_neg_half_line_mul_prod_le N t
  have hD : ∏ j ∈ Finset.range (N + 1), ((j : ℝ) + 1 / 2) > 0 :=
    Finset.prod_pos (fun j _ => by positivity)
  have hGs' : ‖Complex.Gamma s‖ ≤ (Real.sqrt (2 * Real.pi) / ∏ j ∈ Finset.range (N + 1),
      ((j : ℝ) + 1 / 2)) * Real.exp (-(Real.pi * |t|) / 2) := by
    rw [div_mul_eq_mul_div, le_div_iff₀ hD, mul_comm (Real.sqrt _)]
    linarith
  have hdeg : D.degree = 2 * ∑ i, D.α i := rfl
  have hexp : Real.exp (Real.pi * (∑ i, D.α i) * |t|) * Real.exp (-(Real.pi * |t|) / 2) =
      Real.exp (-(Real.pi * (1 - D.degree) / 2) * |t|) := by
    rw [← Real.exp_add, hdeg]; congr 1; ring
  have hg0 : 0 ≤ ∏ i, g i := Finset.prod_nonneg (fun i _ => by
    simp only [hg]
    have hα := D.α_pos i
    have hρ := D.r_re_nonneg i
    have := hN i
    have : 0 ≤ Real.Gamma (D.α i * (N + 3 / 2) + (D.r i).re) :=
      Real.Gamma_nonneg_of_nonneg (by have := Nat.cast_nonneg (α := ℝ) N; positivity)
    have : 0 ≤ Real.Gamma (1 + D.α i * (N + 1 / 2) - (D.r i).re) :=
      Real.Gamma_nonneg_of_nonneg (by nlinarith)
    have := Real.pi_pos
    positivity)
  rw [norm_mul, hFs]
  calc D.Q ^ (2 * N + 2) * ((∏ i, ‖(Complex.Gamma (D.α i * s + D.r i))⁻¹‖) *
      (∏ i, ‖Complex.Gamma (D.α i * u + D.r i)‖)) * ‖F u‖ * ‖Complex.Gamma s‖
      ≤ D.Q ^ (2 * N + 2) * ((∏ i, g i) * Real.exp (Real.pi * (∑ i, D.α i) * |t|)) * K *
          ((Real.sqrt (2 * Real.pi) / ∏ j ∈ Finset.range (N + 1), ((j : ℝ) + 1 / 2)) *
            Real.exp (-(Real.pi * |t|) / 2)) := by
        gcongr
    _ = _ := by
        rw [← hexp]; simp only [hg]; ring

open Complex Filter Topology MeasureTheory in
/-- `Γ(y + a) ≤ Γ(y) y^a` for `y > 0`, `0 < a < 1` (log-convexity). -/
private lemma Real_Gamma_add_le (y a : ℝ) (hy : 0 < y) (ha0 : 0 < a) (ha1 : a < 1) :
    Real.Gamma (y + a) ≤ Real.Gamma y * y ^ a := by
  have h := Real.Gamma_mul_add_mul_le_rpow_Gamma_mul_rpow_Gamma (s := y) (t := y + 1)
    (a := 1 - a) (b := a) hy (by linarith) (by linarith) ha0 (by ring)
  rw [show (1 - a) * y + a * (y + 1) = y + a by ring, Real.Gamma_add_one hy.ne'] at h
  have hG := Real.Gamma_pos_of_pos hy
  rw [Real.mul_rpow hy.le hG.le] at h
  calc Real.Gamma (y + a) ≤ Real.Gamma y ^ (1 - a) * (y ^ a * Real.Gamma y ^ a) := h
    _ = Real.Gamma y * y ^ a := by
        rw [mul_left_comm, ← Real.rpow_add hG]; simp; ring

open Complex Filter Topology MeasureTheory in
/-- A nonnegative sequence that eventually halves at each step tends to `0`. -/
private lemma tendsto_zero_of_eventually_halving (u : ℕ → ℝ) (N1 : ℕ) (hu : ∀ N ≥ N1, 0 ≤ u N)
    (h : ∀ N ≥ N1, u (N + 1) ≤ u N / 2) : Tendsto u atTop (𝓝 0) := by
  have hk : ∀ k : ℕ, u (N1 + k) ≤ u N1 * (1 / 2) ^ k := by
    intro k
    induction k with
    | zero => simp
    | succ k ih =>
      calc u (N1 + (k + 1)) = u (N1 + k + 1) := by rw [add_assoc]
        _ ≤ u (N1 + k) / 2 := h _ (by omega)
        _ ≤ u N1 * (1 / 2) ^ k / 2 := by gcongr
        _ = u N1 * (1 / 2) ^ (k + 1) := by ring
  have hlim : Tendsto (fun N : ℕ => u N1 * (1 / 2) ^ (N - N1)) atTop (𝓝 0) := by
    have h1 : Tendsto (fun N : ℕ => (1 / 2 : ℝ) ^ (N - N1)) atTop (𝓝 0) :=
      (tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num) (by norm_num)).comp
        (tendsto_sub_atTop_nat N1)
    simpa using h1.const_mul (u N1)
  refine squeeze_zero' ?_ ?_ hlim
  · filter_upwards [eventually_ge_atTop N1] with N hN using hu N hN
  filter_upwards [eventually_ge_atTop N1] with N hN
  have := hk (N - N1)
  rwa [Nat.add_sub_cancel' hN] at this

open Complex Filter Topology MeasureTheory in
/-- The constants of the line bound decay faster than any geometric sequence. -/
private lemma tendsto_line_bound_const_mul_pow {F : ℂ → ℂ} (D : FunctionalEquation F) (K : ℝ) (hK0 :
    0 ≤ K)
    (hdeg : D.degree < 1) (N0 : ℕ) (hN0 : ∀ i, (D.r i).re ≤ D.α i * N0) (ρ : ℝ) (hρ : 0 < ρ) :
    Tendsto (fun N : ℕ => K * D.Q ^ (2 * N + 2) * (∏ i, (Real.Gamma (D.α i * (N + 3 / 2) + (D.r
        i).re) *
        Real.Gamma (1 + D.α i * (N + 1 / 2) - (D.r i).re) *
          Real.exp (Real.pi * |(D.r i).im|) / Real.pi)) *
        (Real.sqrt (2 * Real.pi) / ∏ j ∈ Finset.range (N + 1), ((j : ℝ) + 1 / 2)) * ρ ^ N)
      atTop (𝓝 0) := by
  set g : Fin D.d → ℕ → ℝ := fun i N => Real.Gamma (D.α i * (N + 3 / 2) + (D.r i).re) *
        Real.Gamma (1 + D.α i * (N + 1 / 2) - (D.r i).re) *
          Real.exp (Real.pi * |(D.r i).im|) / Real.pi with hg
  set Dn : ℕ → ℝ := fun N => ∏ j ∈ Finset.range (N + 1), ((j : ℝ) + 1 / 2) with hDn
  set d : ℝ := D.degree with hd
  have hdsum : d = 2 * ∑ i, D.α i := rfl
  have hQ := D.Q_pos
  have hα1 : ∀ i, D.α i < 1 := by
    intro i
    have := Finset.single_le_sum (fun j _ => (D.α_pos j).le) (Finset.mem_univ i)
    linarith
  set C : ℝ := 3 / 2 + ∑ i, |(D.r i).re| + 1 with hC
  have hC1 : 1 ≤ C := by
    have : 0 ≤ ∑ i, |(D.r i).re| := Finset.sum_nonneg (fun i _ => abs_nonneg _)
    linarith
  have hNC : ∀ N : ℕ, 0 < (N : ℝ) + C := fun N => by positivity
  have hgnn : ∀ i, ∀ N ≥ N0, 0 ≤ g i N := by
    intro i N hN
    have hα := D.α_pos i
    have hρ0 := D.r_re_nonneg i
    have h1 : (N0 : ℝ) ≤ N := by exact_mod_cast hN
    have := hN0 i
    simp only [hg]
    have : 0 ≤ Real.Gamma (D.α i * (N + 3 / 2) + (D.r i).re) :=
      Real.Gamma_nonneg_of_nonneg (by positivity)
    have : 0 ≤ Real.Gamma (1 + D.α i * (N + 1 / 2) - (D.r i).re) :=
      Real.Gamma_nonneg_of_nonneg (by nlinarith)
    have := Real.pi_pos
    positivity
  have hgstep : ∀ i, ∀ N ≥ N0, g i (N + 1) ≤ g i N * ((N : ℝ) + C) ^ (2 * D.α i) := by
    intro i N hN
    have hα := D.α_pos i
    have hρ0 := D.r_re_nonneg i
    have h1 : (N0 : ℝ) ≤ N := by exact_mod_cast hN
    have h0 := hN0 i
    set y1 : ℝ := D.α i * (N + 3 / 2) + (D.r i).re with hy1
    set y2 : ℝ := 1 + D.α i * (N + 1 / 2) - (D.r i).re with hy2
    have hy1p : 0 < y1 := by positivity
    have hy2p : 0 < y2 := by nlinarith
    have hy1C : y1 ≤ N + C := by
      have : (D.r i).re ≤ ∑ j, |(D.r j).re| :=
        (le_abs_self _).trans (Finset.single_le_sum (f := fun j => |(D.r j).re|)
          (fun j _ => abs_nonneg _) (Finset.mem_univ i))
      have : D.α i * (N + 3 / 2) ≤ N + 3 / 2 := by
        have : (0 : ℝ) ≤ N + 3 / 2 := by positivity
        nlinarith [hα1 i]
      linarith
    have hy2C : y2 ≤ N + C := by
      have : D.α i * (N + 1 / 2) ≤ N + 1 / 2 := by
        have : (0 : ℝ) ≤ N + 1 / 2 := by positivity
        nlinarith [hα1 i]
      have : 0 ≤ ∑ j, |(D.r j).re| := Finset.sum_nonneg (fun j _ => abs_nonneg _)
      linarith
    have e1 : D.α i * (((N + 1 : ℕ) : ℝ) + 3 / 2) + (D.r i).re = y1 + D.α i := by
      rw [hy1]; push_cast; ring
    have e2 : 1 + D.α i * (((N + 1 : ℕ) : ℝ) + 1 / 2) - (D.r i).re = y2 + D.α i := by
      rw [hy2]; push_cast; ring
    have G1 := Real_Gamma_add_le y1 (D.α i) hy1p hα (hα1 i)
    have G2 := Real_Gamma_add_le y2 (D.α i) hy2p hα (hα1 i)
    have P1 : y1 ^ D.α i ≤ ((N : ℝ) + C) ^ D.α i := Real.rpow_le_rpow hy1p.le hy1C hα.le
    have P2 : y2 ^ D.α i ≤ ((N : ℝ) + C) ^ D.α i := Real.rpow_le_rpow hy2p.le hy2C hα.le
    have Γ1 := Real.Gamma_pos_of_pos hy1p
    have Γ2 := Real.Gamma_pos_of_pos hy2p
    simp only [hg]
    rw [e1, e2]
    rw [show (2 * D.α i) = D.α i + D.α i by ring, Real.rpow_add (hNC N)]
    have hE : 0 ≤ Real.exp (Real.pi * |(D.r i).im|) / Real.pi := by
      have := Real.pi_pos; positivity
    calc Real.Gamma (y1 + D.α i) * Real.Gamma (y2 + D.α i) *
          Real.exp (Real.pi * |(D.r i).im|) / Real.pi
        = Real.Gamma (y1 + D.α i) * Real.Gamma (y2 + D.α i) *
          (Real.exp (Real.pi * |(D.r i).im|) / Real.pi) := by ring
      _ ≤ (Real.Gamma y1 * ((N : ℝ) + C) ^ D.α i) * (Real.Gamma y2 * ((N : ℝ) + C) ^ D.α i) *
          (Real.exp (Real.pi * |(D.r i).im|) / Real.pi) := by
          gcongr
          · exact G1.trans (by gcongr)
          · exact G2.trans (by gcongr)
      _ = _ := by ring
  have hP : ∀ N ≥ N0, (∏ i, g i (N + 1)) ≤ (∏ i, g i N) * ((N : ℝ) + C) ^ d := by
    intro N hN
    calc (∏ i, g i (N + 1)) ≤ ∏ i, (g i N * ((N : ℝ) + C) ^ (2 * D.α i)) :=
          Finset.prod_le_prod₀ (fun i _ => hgnn i (N + 1) (by omega)) (fun i _ => hgstep i N hN)
      _ = (∏ i, g i N) * ((N : ℝ) + C) ^ d := by
          rw [Finset.prod_mul_distrib, ← Real.rpow_sum_of_pos (hNC N), hdsum, Finset.mul_sum]
  have hDn : ∀ N, Dn (N + 1) = Dn N * ((N : ℝ) + 3 / 2) := by
    intro N
    simp only [hDn]
    rw [Finset.prod_range_succ]
    push_cast; ring
  have hDpos : ∀ N, 0 < Dn N := fun N => Finset.prod_pos (fun j _ => by positivity)
  set u : ℕ → ℝ := fun N => K * D.Q ^ (2 * N + 2) * (∏ i, g i N) *
    (Real.sqrt (2 * Real.pi) / Dn N) * ρ ^ N with hu
  have hunn : ∀ N ≥ N0, 0 ≤ u N := by
    intro N hN
    have := Finset.prod_nonneg (fun i (_ : i ∈ Finset.univ) => hgnn i N hN)
    have := hDpos N
    simp only [hu]; positivity
  have hstep : ∀ N ≥ N0, u (N + 1) ≤ u N * (ρ * D.Q ^ 2 * (((N : ℝ) + C) ^ d / (N + 3 / 2))) := by
    intro N hN
    have hPN := hP N hN
    have hD1 := hDn N
    have hDN := hDpos N
    have hN32 : (0 : ℝ) < N + 3 / 2 := by positivity
    simp only [hu]
    rw [hD1, show 2 * (N + 1) + 2 = (2 * N + 2) + 2 by ring, pow_add, pow_succ ρ]
    have hpos : 0 ≤ K * D.Q ^ (2 * N + 2) * D.Q ^ 2 * Real.sqrt (2 * Real.pi) * ρ ^ N * ρ := by
      positivity
    calc K * (D.Q ^ (2 * N + 2) * D.Q ^ 2) * (∏ i, g i (N + 1)) *
          (Real.sqrt (2 * Real.pi) / (Dn N * ((N : ℝ) + 3 / 2))) * (ρ ^ N * ρ)
        = (K * D.Q ^ (2 * N + 2) * D.Q ^ 2 * Real.sqrt (2 * Real.pi) * ρ ^ N * ρ) *
            (∏ i, g i (N + 1)) / (Dn N * ((N : ℝ) + 3 / 2)) := by ring
      _ ≤ (K * D.Q ^ (2 * N + 2) * D.Q ^ 2 * Real.sqrt (2 * Real.pi) * ρ ^ N * ρ) *
            ((∏ i, g i N) * ((N : ℝ) + C) ^ d) / (Dn N * ((N : ℝ) + 3 / 2)) := by
          gcongr
      _ = _ := by field_simp
  -- the ratio tends to zero
  have hratio : ∀ᶠ N : ℕ in atTop, ρ * D.Q ^ 2 * (((N : ℝ) + C) ^ d / (N + 3 / 2)) ≤ 1 / 2 := by
    have hlim : Tendsto (fun N : ℕ => ((N : ℝ) + C) ^ (-(1 - d))) atTop (𝓝 0) :=
      (tendsto_rpow_neg_atTop (by linarith)).comp
        (tendsto_atTop_add_const_right atTop C tendsto_natCast_atTop_atTop)
    have hc : 0 < 1 / (2 * (ρ * D.Q ^ 2 * C)) := by positivity
    filter_upwards [hlim.eventually (gt_mem_nhds hc)] with N hN
    have hNC' := hNC N
    have h32 : (0 : ℝ) < N + 3 / 2 := by positivity
    have e : ((N : ℝ) + C) ^ d = ((N : ℝ) + C) ^ (-(1 - d)) * ((N : ℝ) + C) := by
      rw [← Real.rpow_add_one hNC'.ne']; ring_nf
    have hle : ((N : ℝ) + C) ≤ C * (N + 3 / 2) := by nlinarith
    have hpow0 : 0 ≤ ((N : ℝ) + C) ^ (-(1 - d)) := by positivity
    rw [e]
    calc ρ * D.Q ^ 2 * (((N : ℝ) + C) ^ (-(1 - d)) * ((N : ℝ) + C) / (N + 3 / 2))
        ≤ ρ * D.Q ^ 2 * (((N : ℝ) + C) ^ (-(1 - d)) * (C * (N + 3 / 2)) / (N + 3 / 2)) := by
          gcongr
      _ = ρ * D.Q ^ 2 * C * ((N : ℝ) + C) ^ (-(1 - d)) := by field_simp
      _ ≤ ρ * D.Q ^ 2 * C * (1 / (2 * (ρ * D.Q ^ 2 * C))) := by gcongr
      _ = 1 / 2 := by field_simp
  rw [eventually_atTop] at hratio
  obtain ⟨N1, hN1⟩ := hratio
  have hlim := tendsto_zero_of_eventually_halving u (max N0 N1) (fun N hN => hunn N (le_trans
      (le_max_left _ _) hN))
    (fun N hN => by
      have h1 := hstep N (le_trans (le_max_left _ _) hN)
      have h2 := hN1 N (le_trans (le_max_right _ _) hN)
      have h3 := hunn N (le_trans (le_max_left _ _) hN)
      calc u (N + 1) ≤ u N * (ρ * D.Q ^ 2 * (((N : ℝ) + C) ^ d / (N + 3 / 2))) := h1
        _ ≤ u N * (1 / 2) := by gcongr
        _ = u N / 2 := by ring)
  exact hlim

open Complex Filter Topology MeasureTheory in
/-- `Γ` is bounded on a compact interval of positive reals. -/
private lemma exists_Real_Gamma_le_on_Icc (a b : ℝ) (ha : 0 < a) :
    ∃ M, ∀ x : ℝ, a ≤ x → x ≤ b → Real.Gamma x ≤ M := by
  have hc : ContinuousOn Real.Gamma (Set.Icc a b) := by
    intro x hx
    apply (Real.differentiableAt_Gamma _).continuousAt.continuousWithinAt
    intro m hm
    have := hx.1
    have : (0 : ℝ) ≤ m := Nat.cast_nonneg m
    linarith
  obtain ⟨M, hM⟩ := isCompact_Icc.exists_bound_of_continuousOn hc
  exact ⟨M, fun x h1 h2 => (le_abs_self _).trans (hM x ⟨h1, h2⟩)⟩

open Complex Filter Topology MeasureTheory in
/-- Decay of `F(s) Γ(s)` in a vertical strip `-n - 1/2 ≤ Re s ≤ b`, from Phragmén–Lindelöf
applied to `G(s) Γ(s + n + 1) / (s + n + 2)^m`, bounded on the two edges. -/
private lemma norm_mul_Gamma_strip_le (F G : ℂ → ℂ) (m : ℕ) (hGd : Differentiable ℂ G)
    (hGF : ∀ s, s ≠ 1 → G s = (s - 1) ^ m * F s)
    (k C R : ℝ) (hk : 0 ≤ k) (hGg : ∀ s : ℂ, R ≤ ‖s‖ → ‖G s‖ ≤ C * Real.exp (‖s‖ ^ k))
    (n : ℕ) (b : ℝ) (hab : -(n : ℝ) - 1 / 2 < b) (_hb2 : b ≤ 2) (B : ℝ)
    (hedge : ∀ s : ℂ, (s.re = -(n : ℝ) - 1 / 2 ∨ s.re = b) →
      ‖G s * Complex.Gamma (s + (n + 1 : ℕ)) / (s + (n + 2 : ℕ)) ^ m‖ ≤ B) :
    ∃ M, ∀ s : ℂ, -(n : ℝ) - 1 / 2 ≤ s.re → s.re ≤ b → 1 ≤ |s.im| →
      ‖F s * Complex.Gamma s‖ ≤ M / |s.im| := by
  set φ : ℂ → ℂ := fun s => G s * Complex.Gamma (s + (n + 1 : ℕ)) / (s + (n + 2 : ℕ)) ^ m
    with hφ
  have hre1 : ∀ s : ℂ, -(n : ℝ) - 1 / 2 ≤ s.re → 1 / 2 ≤ (s + (n + 1 : ℕ)).re := by
    intro s hs; simp; linarith
  have hre2 : ∀ s : ℂ, -(n : ℝ) - 1 / 2 ≤ s.re → 3 / 2 ≤ ‖s + (n + 2 : ℕ)‖ := by
    intro s hs
    refine le_trans ?_ (Complex.abs_re_le_norm _)
    rw [abs_of_nonneg (by simp; linarith)]
    simp; linarith
  have hφd : ∀ s : ℂ, -(n : ℝ) - 1 / 2 ≤ s.re → s.re ≤ b → DifferentiableAt ℂ φ s := by
    intro s h1 _
    have hG1 : DifferentiableAt ℂ (fun s : ℂ => Complex.Gamma (s + (n + 1 : ℕ))) s := by
      apply DifferentiableAt.comp
      · apply Complex.differentiableAt_Gamma
        intro j hj
        have := congrArg Complex.re hj
        have h2 := hre1 s h1
        rw [this] at h2
        simp at h2
        have : (0 : ℝ) ≤ j := Nat.cast_nonneg j
        linarith
      · exact differentiableAt_id.add_const _
    have hne : (s + (n + 2 : ℕ)) ^ m ≠ 0 := by
      apply pow_ne_zero
      intro h0
      have := hre2 s h1
      rw [h0, norm_zero] at this
      linarith
    exact ((hGd s).mul hG1).div ((differentiableAt_id.add_const _).pow m) hne
  obtain ⟨Γm, hΓm⟩ := exists_Real_Gamma_le_on_Icc (1 / 2) (b + n + 1) (by norm_num)
  have hφg : ∀ s : ℂ, -(n : ℝ) - 1 / 2 ≤ s.re → s.re ≤ b → R ≤ ‖s‖ →
      ‖φ s‖ ≤ (C * Γm) * Real.exp (‖s‖ ^ k) := by
    intro s h1 h2 h3
    have hG := hGg s h3
    have hΓ := Complex.norm_Gamma_le_Gamma_re (s := s + (n + 1 : ℕ)) (by linarith [hre1 s h1])
    have hΓ' : Real.Gamma (s + (n + 1 : ℕ)).re ≤ Γm := by
      apply hΓm _ (hre1 s h1)
      simp; linarith
    have hden : 1 ≤ ‖(s + (n + 2 : ℕ)) ^ m‖ := by
      rw [norm_pow]; exact one_le_pow₀ (by linarith [hre2 s h1])
    simp only [hφ, norm_div, norm_mul]
    rw [div_le_iff₀ (by linarith)]
    calc ‖G s‖ * ‖Complex.Gamma (s + (n + 1 : ℕ))‖
        ≤ (C * Real.exp (‖s‖ ^ k)) * Γm := by
          apply mul_le_mul hG (hΓ.trans hΓ') (norm_nonneg _)
          exact (norm_nonneg _).trans hG
      _ = (C * Γm) * Real.exp (‖s‖ ^ k) * 1 := by ring
      _ ≤ (C * Γm) * Real.exp (‖s‖ ^ k) * ‖(s + (n + 2 : ℕ)) ^ m‖ := by
          apply mul_le_mul_of_nonneg_left hden
          have := (norm_nonneg (G s)).trans hG
          have hC0 : 0 ≤ C := by
            by_contra hC; push Not at hC
            have : C * Real.exp (‖s‖ ^ k) < 0 := mul_neg_of_neg_of_pos hC (Real.exp_pos _)
            linarith
          have : 0 ≤ Γm := le_trans (Real.Gamma_pos_of_pos (by norm_num : (0 : ℝ) < 1 / 2)).le
            (hΓm (1 / 2) le_rfl (by have := Nat.cast_nonneg (α := ℝ) n; linarith))
          positivity
  have hPL := bounded_strip_of_finite_order φ _ b hab hφd k (C * Γm) R hk hφg B hedge
  have hB0 : 0 ≤ B := le_trans (norm_nonneg _) (hedge (b : ℂ) (Or.inr (by simp)))
  refine ⟨B * ((n : ℝ) + 4) ^ m, fun s h1 h2 h3 => ?_⟩
  have hs1 : s ≠ 1 := by
    intro h; rw [h] at h3; simp at h3; linarith
  have hpole : ∀ j : ℕ, s ≠ -j := by
    intro j h; rw [h] at h3; simp at h3; linarith
  have hGs := hGF s hs1
  have hΓs := Gamma_add_nat_eq_prod_mul s hpole (n + 1)
  have hφs := hPL s h1 h2
  have ht0 : 0 < |s.im| := by linarith
  -- norms
  have hn1 : 1 ≤ ‖s - 1‖ := by
    refine le_trans h3 ?_
    have := Complex.abs_im_le_norm (s - 1)
    simpa using this
  have hnum : ‖s + (n + 2 : ℕ)‖ ≤ ((n : ℝ) + 4) * ‖s - 1‖ := by
    calc ‖s + (n + 2 : ℕ)‖ = ‖(s - 1) + ((n + 3 : ℕ) : ℂ)‖ := by push_cast; ring_nf
      _ ≤ ‖s - 1‖ + ‖((n + 3 : ℕ) : ℂ)‖ := norm_add_le _ _
      _ = ‖s - 1‖ + ((n : ℝ) + 3) := by rw [Complex.norm_natCast]; push_cast; ring
      _ ≤ ((n : ℝ) + 4) * ‖s - 1‖ := by nlinarith
  have hprod : |s.im| ≤ ‖∏ j ∈ Finset.range (n + 1), (s + j)‖ := by
    rw [norm_prod]
    have hk1 : ∀ j ∈ Finset.range (n + 1), 1 ≤ ‖s + j‖ := by
      intro j _
      refine le_trans h3 ?_
      have := Complex.abs_im_le_norm (s + j)
      simpa using this
    calc |s.im| ≤ ‖s + ((0 : ℕ) : ℂ)‖ := by
          have := Complex.abs_im_le_norm (s + ((0 : ℕ) : ℂ)); simpa using this
      _ ≤ ∏ j ∈ Finset.range (n + 1), ‖s + j‖ := by
          rw [Finset.prod_range_succ']
          have : 1 ≤ ∏ j ∈ Finset.range n, ‖s + ((j + 1 : ℕ) : ℂ)‖ := by
            calc (1 : ℝ) = ∏ j ∈ Finset.range n, (1 : ℝ) := by simp
              _ ≤ _ := Finset.prod_le_prod₀ (fun _ _ => zero_le_one)
                (fun j hj => hk1 (j + 1) (by simp at hj ⊢; omega))
          calc ‖s + ((0 : ℕ) : ℂ)‖ = 1 * ‖s + ((0 : ℕ) : ℂ)‖ := (one_mul _).symm
            _ ≤ _ := by gcongr
  have hden0 : (s - 1) ^ m * ∏ j ∈ Finset.range (n + 1), (s + j) ≠ 0 := by
    apply mul_ne_zero (pow_ne_zero _ (sub_ne_zero.2 hs1))
    rw [Finset.prod_ne_zero_iff]
    intro j _ h0
    exact hpole j (by linear_combination h0)
  have hnum0 : (s + (n + 2 : ℕ)) ^ m ≠ 0 := by
    apply pow_ne_zero
    intro h0
    have := hre2 s h1
    rw [h0, norm_zero] at this
    linarith
  have key : F s * Complex.Gamma s = φ s * (s + (n + 2 : ℕ)) ^ m /
      ((s - 1) ^ m * ∏ j ∈ Finset.range (n + 1), (s + j)) := by
    rw [eq_div_iff hden0]
    simp only [hφ]
    rw [div_mul_cancel₀ _ hnum0, hGs, hΓs]
    ring
  rw [key, norm_div, norm_mul, norm_mul, norm_pow, norm_pow, div_le_div_iff₀ (by
    apply mul_pos (pow_pos (by linarith) _) (by linarith)) ht0]
  have hpow : ‖s + (n + 2 : ℕ)‖ ^ m ≤ ((n : ℝ) + 4) ^ m * ‖s - 1‖ ^ m := by
    rw [← mul_pow]; exact pow_le_pow_left₀ (norm_nonneg _) hnum m
  calc ‖φ s‖ * ‖s + (n + 2 : ℕ)‖ ^ m * |s.im|
      ≤ B * (((n : ℝ) + 4) ^ m * ‖s - 1‖ ^ m) * ‖∏ j ∈ Finset.range (n + 1), (s + j)‖ := by
        gcongr
    _ = B * ((n : ℝ) + 4) ^ m * (‖s - 1‖ ^ m * ‖∏ j ∈ Finset.range (n + 1), (s + j)‖) := by ring

open Complex Filter Topology MeasureTheory in
/-- `(B + |t|)^j e^{-c|t|}` is bounded. -/
private lemma add_abs_pow_mul_exp_neg_le (B c t : ℝ) (hB : 0 ≤ B) (hc : 0 < c) (j : ℕ) :
    (B + |t|) ^ j * Real.exp (-c * |t|) ≤ j.factorial / c ^ j * Real.exp (c * B) := by
  have h := Real.pow_div_factorial_le_exp (x := c * (B + |t|)) (by positivity) j
  have hj : (0 : ℝ) < j.factorial := by exact_mod_cast Nat.factorial_pos j
  rw [div_le_iff₀ hj, mul_pow] at h
  have hcj : 0 < c ^ j := pow_pos hc j
  rw [div_mul_eq_mul_div, le_div_iff₀ hcj]
  have e : Real.exp (c * (B + |t|)) = Real.exp (c * B) * Real.exp (c * |t|) := by
    rw [← Real.exp_add]; ring_nf
  rw [e] at h
  have hE : Real.exp (-c * |t|) * Real.exp (c * |t|) = 1 := by
    rw [← Real.exp_add]; simp
  calc (B + |t|) ^ j * Real.exp (-c * |t|) * c ^ j
      = (c ^ j * (B + |t|) ^ j) * Real.exp (-c * |t|) := by ring
    _ ≤ (Real.exp (c * B) * Real.exp (c * |t|) * j.factorial) * Real.exp (-c * |t|) := by
        gcongr
    _ = j.factorial * Real.exp (c * B) * (Real.exp (-c * |t|) * Real.exp (c * |t|)) := by ring
    _ = j.factorial * Real.exp (c * B) := by rw [hE, mul_one]

open Complex Filter Topology MeasureTheory in
/-- The edge bound on a line `Re s = -N - 1/2`, from an exponentially decaying bound for
`F(s) Γ(s)` there. -/
private lemma norm_edge_line_le (F G : ℂ → ℂ) (m : ℕ) (hGF : ∀ s, s ≠ 1 → G s = (s - 1) ^ m * F s)
    (n N : ℕ) (hNn : N ≤ n) (A c : ℝ) (hc : 0 < c)
    (hline : ∀ t : ℝ, ‖F (-(N : ℂ) - 1 / 2 + t * I) * Complex.Gamma (-(N : ℂ) - 1 / 2 + t * I)‖ ≤
      A * Real.exp (-c * |t|)) :
    ∃ B, ∀ s : ℂ, s.re = -(N : ℝ) - 1 / 2 →
      ‖G s * Complex.Gamma (s + (n + 1 : ℕ)) / (s + (n + 2 : ℕ)) ^ m‖ ≤ B := by
  have hA : 0 ≤ A := by
    have := hline 0
    simp only [abs_zero, mul_zero, Real.exp_zero, mul_one] at this
    exact (norm_nonneg _).trans this
  refine ⟨((n : ℝ) + 4) ^ m * (A * ((n + 1).factorial / c ^ (n + 1) *
    Real.exp (c * ((n : ℝ) + 1)))), fun s hs => ?_⟩
  set t := s.im with ht
  have hse : s = -(N : ℂ) - 1 / 2 + t * I := by
    apply Complex.ext <;> simp [hs, ht]
  have hs1 : s ≠ 1 := by
    intro h; rw [h] at hs; simp at hs; have := Nat.cast_nonneg (α := ℝ) N; linarith
  have hpole : ∀ k : ℕ, s ≠ -k := by
    intro k h
    have := congrArg Complex.re h
    rw [hs] at this
    simp only [one_div, neg_re, natCast_re] at this
    have h2 : (2 * (k : ℝ)) = 2 * N + 1 := by linarith
    have h3 : (2 * k : ℕ) = 2 * N + 1 := by exact_mod_cast h2
    omega
  have hGs := hGF s hs1
  have hΓs := Gamma_add_nat_eq_prod_mul s hpole (n + 1)
  have hNn' : (N : ℝ) ≤ n := by exact_mod_cast hNn
  have hden : 3 / 2 ≤ ‖s + (n + 2 : ℕ)‖ := by
    refine le_trans ?_ (Complex.abs_re_le_norm _)
    have : (s + (n + 2 : ℕ)).re = (n : ℝ) - N + 3 / 2 := by simp [hs]; ring
    rw [this, abs_of_nonneg (by linarith)]
    linarith
  have hnum : ‖s - 1‖ ≤ ((n : ℝ) + 4) * ‖s + (n + 2 : ℕ)‖ := by
    calc ‖s - 1‖ = ‖(s + (n + 2 : ℕ)) - ((n + 3 : ℕ) : ℂ)‖ := by push_cast; ring_nf
      _ ≤ ‖s + (n + 2 : ℕ)‖ + ‖((n + 3 : ℕ) : ℂ)‖ := norm_sub_le _ _
      _ = ‖s + (n + 2 : ℕ)‖ + ((n : ℝ) + 3) := by rw [Complex.norm_natCast]; push_cast; ring
      _ ≤ ((n : ℝ) + 4) * ‖s + (n + 2 : ℕ)‖ := by nlinarith
  have hprod : ‖∏ k ∈ Finset.range (n + 1), (s + k)‖ ≤ ((n : ℝ) + 1 + |t|) ^ (n + 1) := by
    rw [norm_prod]
    calc ∏ k ∈ Finset.range (n + 1), ‖s + k‖ ≤ ∏ k ∈ Finset.range (n + 1), ((n : ℝ) + 1 + |t|) :=
          Finset.prod_le_prod₀ (fun _ _ => norm_nonneg _) (fun k hk => by
            have hk' : (k : ℝ) ≤ n := by
              have := Finset.mem_range.1 hk; exact_mod_cast Nat.lt_succ_iff.1 this
            refine (Complex.norm_le_abs_re_add_abs_im _).trans ?_
            have h1 : (s + k).re = (k : ℝ) - N - 1 / 2 := by simp [hs]; ring
            have h2 : (s + k).im = t := by simp [ht]
            rw [h1, h2]
            gcongr
            rw [abs_le]; constructor <;> linarith [Nat.cast_nonneg (α := ℝ) k, Nat.cast_nonneg (α :=
                ℝ) N])
      _ = _ := by simp
  have hl := hline t
  rw [← hse] at hl
  have hpe := add_abs_pow_mul_exp_neg_le ((n : ℝ) + 1) c t (by positivity) hc (n + 1)
  have hnum0 : (s + (n + 2 : ℕ)) ^ m ≠ 0 := by
    apply pow_ne_zero; intro h0; rw [h0, norm_zero] at hden; linarith
  have e : G s * Complex.Gamma (s + (n + 1 : ℕ)) / (s + (n + 2 : ℕ)) ^ m =
      ((s - 1) / (s + (n + 2 : ℕ))) ^ m * (F s * Complex.Gamma s) *
        ∏ k ∈ Finset.range (n + 1), (s + k) := by
    rw [hGs, hΓs, div_pow]; field_simp
  rw [e, norm_mul, norm_mul, norm_pow, norm_div]
  have hq : ‖s - 1‖ / ‖s + (n + 2 : ℕ)‖ ≤ (n : ℝ) + 4 := by
    rw [div_le_iff₀ (by linarith)]; exact hnum
  calc (‖s - 1‖ / ‖s + (n + 2 : ℕ)‖) ^ m * ‖F s * Complex.Gamma s‖ *
        ‖∏ k ∈ Finset.range (n + 1), (s + k)‖
      ≤ ((n : ℝ) + 4) ^ m * (A * Real.exp (-c * |t|)) * ((n : ℝ) + 1 + |t|) ^ (n + 1) := by
        gcongr
    _ = ((n : ℝ) + 4) ^ m * (A * (((n : ℝ) + 1 + |t|) ^ (n + 1) * Real.exp (-c * |t|))) := by ring
    _ ≤ _ := by gcongr

open Complex Filter Topology MeasureTheory in
/-- The edge bound on the line `Re s = 2`. -/
private lemma norm_edge_line_two_le (F G : ℂ → ℂ) (m : ℕ) (hGF : ∀ s, s ≠ 1 → G s = (s - 1) ^ m * F
    s)
    (K : ℝ) (hK : ∀ s : ℂ, 3 / 2 ≤ s.re → ‖F s‖ ≤ K) (n : ℕ) :
    ∀ s : ℂ, s.re = 2 →
      ‖G s * Complex.Gamma (s + (n + 1 : ℕ)) / (s + (n + 2 : ℕ)) ^ m‖ ≤
        K * Real.Gamma ((n : ℝ) + 3) := by
  intro s hs
  have hs1 : s ≠ 1 := by intro h; rw [h] at hs; norm_num at hs
  have hFs := hK s (by rw [hs]; norm_num)
  have hK0 : 0 ≤ K := (norm_nonneg _).trans hFs
  have hre : (s + (n + 1 : ℕ)).re = (n : ℝ) + 3 := by simp [hs]; ring
  have hΓ := Complex.norm_Gamma_le_Gamma_re (s := s + (n + 1 : ℕ)) (by rw [hre]; positivity)
  rw [hre] at hΓ
  have hle : ‖s - 1‖ ≤ ‖s + (n + 2 : ℕ)‖ := by
    rw [← sq_le_sq₀ (norm_nonneg _) (norm_nonneg _), Complex.sq_norm, Complex.sq_norm,
      Complex.normSq_apply, Complex.normSq_apply]
    simp [hs]
    nlinarith [Nat.cast_nonneg (α := ℝ) n]
  have hpos : 0 < ‖s + (n + 2 : ℕ)‖ := lt_of_lt_of_le (by
    rw [norm_pos_iff]; exact sub_ne_zero.2 hs1) hle
  rw [hGF s hs1, norm_div, norm_mul, norm_mul, norm_pow, norm_pow]
  rw [div_le_iff₀ (pow_pos hpos m)]
  calc ‖s - 1‖ ^ m * ‖F s‖ * ‖Complex.Gamma (s + (n + 1 : ℕ))‖
      ≤ ‖s + (n + 2 : ℕ)‖ ^ m * K * Real.Gamma ((n : ℝ) + 3) := by gcongr
    _ = _ := by ring

open Complex Filter Topology MeasureTheory in
/-- The box integral around the pole `s = -n` of `F(s) Γ(s) x^{-s}`. -/
private lemma box_integral_pole_neg_nat (F : ℂ → ℂ) (hFd : DifferentiableOn ℂ F {1}ᶜ) (n : ℕ) (hn :
    1 ≤ n)
    (x : ℝ) (hx : 0 < x) :
    (∫ u : ℝ in (-(n : ℝ) - 1 / 2)..(-(n : ℝ) + 1 / 2),
        F (u + (-1 : ℝ) * I) * Complex.Gamma (u + (-1 : ℝ) * I) * (x : ℂ) ^ (-(u + (-1 : ℝ) * I))) -
      (∫ u : ℝ in (-(n : ℝ) - 1 / 2)..(-(n : ℝ) + 1 / 2),
        F (u + (1 : ℝ) * I) * Complex.Gamma (u + (1 : ℝ) * I) * (x : ℂ) ^ (-(u + (1 : ℝ) * I))) +
      I * (∫ y : ℝ in (-1 : ℝ)..1, F ((-(n : ℝ) + 1 / 2 : ℝ) + y * I) *
        Complex.Gamma ((-(n : ℝ) + 1 / 2 : ℝ) + y * I) *
          (x : ℂ) ^ (-(((-(n : ℝ) + 1 / 2 : ℝ) : ℂ) + y * I))) -
      I * (∫ y : ℝ in (-1 : ℝ)..1, F ((-(n : ℝ) - 1 / 2 : ℝ) + y * I) *
        Complex.Gamma ((-(n : ℝ) - 1 / 2 : ℝ) + y * I) *
          (x : ℂ) ^ (-(((-(n : ℝ) - 1 / 2 : ℝ) : ℂ) + y * I))) =
      2 * (Real.pi : ℂ) * I * (F (-(n : ℂ)) * ((x ^ n : ℝ) : ℂ) /
        ∏ k ∈ Finset.range n, ((k : ℂ) - n)) := by
  set h : ℂ → ℂ := fun s => F s * Complex.Gamma s * (x : ℂ) ^ (-s) with hh
  set p : ℂ := -(n : ℂ) with hp
  set H : ℂ → ℂ := fun s => F s * (x : ℂ) ^ (-s) * Complex.Gamma (s + (n + 1 : ℕ)) /
    ∏ k ∈ Finset.range n, (s + k) with hH
  have hx0 : (x : ℂ) ≠ 0 := by exact_mod_cast hx.ne'
  have hprod0 : ∏ k ∈ Finset.range n, (p + k) ≠ 0 := by
    rw [Finset.prod_ne_zero_iff]
    intro k hk h0
    have hk' := Finset.mem_range.1 hk
    have : (k : ℂ) = n := by rw [hp] at h0; linear_combination h0
    have : k = n := by exact_mod_cast this
    omega
  have hHa : AnalyticAt ℂ H p := by
    apply DifferentiableOn.analyticAt (s := Metric.ball p (1 / 2))
    · intro s hs
      rw [Metric.mem_ball, dist_eq_norm] at hs
      have hre : |s.re - p.re| < 1 / 2 := by
        have := Complex.abs_re_le_norm (s - p); simp at this; linarith
      have hpre : p.re = -(n : ℝ) := by simp [hp]
      rw [hpre] at hre
      have hs1 : s ≠ 1 := by
        intro h1; rw [h1] at hre; simp only [one_re, sub_neg_eq_add, one_div] at hre
        have : (1 : ℝ) ≤ n := by exact_mod_cast hn
        rw [abs_lt] at hre; linarith
      have hF : DifferentiableAt ℂ F s := hFd.differentiableAt (isOpen_compl_singleton.mem_nhds hs1)
      have hΓ : DifferentiableAt ℂ (fun s : ℂ => Complex.Gamma (s + (n + 1 : ℕ))) s := by
        apply DifferentiableAt.comp
        · apply Complex.differentiableAt_Gamma
          intro j hj
          have := congrArg Complex.re hj
          simp only [Nat.cast_add, Nat.cast_one, add_re, natCast_re, one_re, neg_re] at this
          rw [abs_lt] at hre
          have : (0 : ℝ) ≤ j := Nat.cast_nonneg j
          push_cast at *
          linarith
        · exact differentiableAt_id.add_const _
      have hP : ∏ k ∈ Finset.range n, (s + k) ≠ 0 := by
        rw [Finset.prod_ne_zero_iff]
        intro k hk h0
        have hk' := Finset.mem_range.1 hk
        have := congrArg Complex.re h0
        simp at this
        rw [abs_lt] at hre
        have : (k : ℝ) + 1 ≤ n := by exact_mod_cast hk'
        linarith
      have hPd : DifferentiableAt ℂ (fun s : ℂ => ∏ k ∈ Finset.range n, (s + k)) s :=
        DifferentiableAt.fun_finsetProd (fun k _ => differentiableAt_id.add_const _)
      exact (((hF.mul (differentiableAt_id.neg.const_cpow (Or.inl hx0))).mul hΓ).div hPd
        hP).differentiableWithinAt
    · exact Metric.ball_mem_nhds p (by norm_num)
  have hloc0 : ∀ᶠ s in 𝓝[≠] p, h s = 1 * H s / (s - p) + 0 := by
    have hb : Metric.ball p (1 / 2) ∈ 𝓝[≠] p :=
      nhdsWithin_le_nhds (Metric.ball_mem_nhds p (by norm_num))
    filter_upwards [hb, self_mem_nhdsWithin] with s hs hsp
    rw [Metric.mem_ball, dist_eq_norm] at hs
    have hre : |s.re - p.re| < 1 / 2 := by
      have := Complex.abs_re_le_norm (s - p); simp at this; linarith
    have hpre : p.re = -(n : ℝ) := by simp [hp]
    rw [hpre, abs_lt] at hre
    have hpole : ∀ j : ℕ, s ≠ -j := by
      intro j hj
      by_cases hjn : j = n
      · exact hsp (by rw [hj, hjn, hp]; exact Set.mem_singleton _)
      · have := congrArg Complex.re hj
        simp at this
        rcases lt_or_gt_of_ne hjn with h1 | h1
        · have : (j : ℝ) + 1 ≤ n := by exact_mod_cast h1
          linarith
        · have : (n : ℝ) + 1 ≤ j := by exact_mod_cast h1
          linarith
    have hΓ := Gamma_add_nat_eq_prod_mul s hpole (n + 1)
    have hsp' : s - p ≠ 0 := sub_ne_zero.2 hsp
    have hsn : s + n = s - p := by rw [hp]; ring
    have hP : ∏ k ∈ Finset.range n, (s + k) ≠ 0 := by
      rw [Finset.prod_ne_zero_iff]
      intro k hk h0
      exact hpole k (by linear_combination h0)
    simp only [hh, hH]
    rw [hΓ, Finset.prod_range_succ, hsn]
    field_simp
    ring
  obtain ⟨φ, hφd, hφe⟩ := Complex.exists_eventually_eq_div_sub_add_of_analyticAt hHa
    (differentiableAt_const (0 : ℂ)) hloc0
  set a : ℝ := -(n : ℝ) - 1 / 2 with ha
  set b : ℝ := -(n : ℝ) + 1 / 2 with hb
  set K : Set ℂ := Set.uIcc a b ×ℂ Set.uIcc (-1 : ℝ) 1 with hK
  have hab : a ≤ b := by rw [ha, hb]; linarith
  have hKmem : ∀ s ∈ K, a ≤ s.re ∧ s.re ≤ b := by
    intro s hs
    simp only [hK, Complex.mem_reProdIm, Set.uIcc_of_le hab, Set.mem_Icc] at hs
    exact hs.1
  obtain ⟨g, hgd, hgeq⟩ := exists_differentiableOn_eq_add_sum_div_sub K {p}
    (fun _ => 1 * H p) h (by
      intro q hq
      rw [Finset.mem_singleton] at hq
      subst hq
      exact ⟨φ, hφd, hφe⟩)
    (by
      intro s hs hsp
      rw [Finset.mem_singleton] at hsp
      obtain ⟨h1, h2⟩ := hKmem s hs
      have hs1 : s ≠ 1 := by
        intro e; rw [e] at h2; simp [hb] at h2; have : (1 : ℝ) ≤ n := by exact_mod_cast hn
        linarith
      have hpole : ∀ j : ℕ, s ≠ -j := by
        intro j hj
        by_cases hjn : j = n
        · exact hsp (by rw [hj, hjn, hp])
        · have := congrArg Complex.re hj
          rw [this] at h1 h2
          simp [ha, hb] at h1 h2
          rcases lt_or_gt_of_ne hjn with e | e
          · have : (j : ℝ) + 1 ≤ n := by exact_mod_cast e
            linarith
          · have : (n : ℝ) + 1 ≤ j := by exact_mod_cast e
            linarith
      have hF : DifferentiableAt ℂ F s := hFd.differentiableAt (isOpen_compl_singleton.mem_nhds hs1)
      exact ((hF.mul (Complex.differentiableAt_Gamma s hpole)).mul
        (differentiableAt_id.neg.const_cpow (Or.inl hx0))).differentiableWithinAt)
  have hres := RectilinearRectangle.boundaryIntegral_eq_two_pi_mul_I_mul_sum
    ⟨⟨a, -1⟩, ⟨b, 1⟩⟩ {p} (fun _ => 1 * H p) h g (by
      intro q hq
      rw [Finset.mem_singleton] at hq
      subst hq
      simp [hp, ha, hb]) hgd hgeq
  simp only [RectilinearRectangle.boundaryIntegral, Finset.sum_singleton, smul_eq_mul] at hres
  have hHp : H p = F (-(n : ℂ)) * ((x ^ n : ℝ) : ℂ) / ∏ k ∈ Finset.range n, ((k : ℂ) - n) := by
    simp only [hH, hp]
    rw [show -(n : ℂ) + ((n + 1 : ℕ) : ℂ) = 1 by push_cast; ring, Complex.Gamma_one, neg_neg,
      Complex.cpow_natCast]
    push_cast
    congr 1
    · ring
    · apply Finset.prod_congr rfl; intro k _; ring
  rw [hHp, one_mul] at hres
  rw [← hres]

open Complex Filter Topology MeasureTheory in
/-- The Mellin–Barnes representation `∑ a_n e^{-nx} = (1/2π) ∫ F(2+it) Γ(2+it) x^{-2-it} dt`. -/
private lemma hasSum_exp_neg_eq_integral_line_two (a : ArithmeticFunction ℂ) (F : ℂ → ℂ)
    (hF : ∀ s : ℂ, 1 < s.re → F s = LSeries (fun n => a n) s)
    (hsum : LSeriesSummable (fun n => a n) 2) (x : ℝ) (hx : 0 < x) :
    ∑' n : ℕ, a n * Complex.exp (-(n : ℂ) * x) = (1 / (2 * Real.pi) : ℂ) *
      ∫ t : ℝ, F (2 + t * I) * Complex.Gamma (2 + t * I) * (x : ℂ) ^ (-(2 + t * I)) := by
  set f : ℕ → ℝ → ℂ := fun n t => LSeries.term (fun n => a n) (2 + t * I) n *
    ((x : ℂ) ^ (-(2 + t * I)) * Complex.Gamma (2 + t * I)) with hf
  have hpi : (2 * Real.pi : ℂ) ≠ 0 := by
    have := Real.pi_pos; exact_mod_cast (by positivity : (2 * Real.pi : ℝ) ≠ 0)
  -- the `n`-th term
  have hcpow : ∀ n : ℕ, n ≠ 0 → ∀ t : ℝ,
      (((1 / (n * x) : ℝ)) : ℂ) ^ ((2 : ℝ) + t * I) =
        (x : ℂ) ^ (-(2 + t * I)) / (n : ℂ) ^ (2 + t * I) := by
    intro n hn t
    have hn0 : (0 : ℝ) < n := by exact_mod_cast Nat.pos_of_ne_zero hn
    have hy : (0 : ℝ) < 1 / (n * x) := by positivity
    have ofReal_cpow_eq_exp : ∀ {x : ℝ}, 0 < x → ∀ s : ℂ,
        (x : ℂ) ^ s = Complex.exp ((Real.log x : ℂ) * s) := fun hx s => by
      rw [Complex.cpow_def_of_ne_zero (by exact_mod_cast hx.ne'), Complex.ofReal_log hx.le]
    rw [ofReal_cpow_eq_exp hy, ofReal_cpow_eq_exp hx, show ((n : ℂ)) = ((n : ℝ) : ℂ) by simp,
      ofReal_cpow_eq_exp hn0, ← Complex.exp_sub]
    congr 1
    rw [Real.log_div one_ne_zero (by positivity), Real.log_one, Real.log_mul hn0.ne' hx.ne']
    push_cast; ring
  have hint_n : ∀ n : ℕ, ∫ t : ℝ, f n t = (2 * Real.pi : ℂ) * (a n * Complex.exp (-(n : ℂ) * x)) :=
      by
    intro n
    rcases eq_or_ne n 0 with rfl | hn
    · simp [hf]
    have hn0 : (0 : ℝ) < n := by exact_mod_cast Nat.pos_of_ne_zero hn
    have hy : (0 : ℝ) < 1 / (n * x) := by positivity
    have hM := Complex.integral_cpow_mul_Gamma_vertical (σ := 2) (by norm_num) hy
    have e : ∀ t : ℝ, f n t = a n * ((((1 / (n * x) : ℝ)) : ℂ) ^ ((2 : ℝ) + t * I) *
        Complex.Gamma ((2 : ℝ) + t * I)) := by
      intro t
      simp only [hf, LSeries.term_of_ne_zero hn, hcpow n hn t]
      push_cast; ring
    simp_rw [e]
    rw [integral_const_mul]
    have hM' : ∫ t : ℝ, (((1 / (n * x) : ℝ)) : ℂ) ^ ((2 : ℝ) + t * I) *
        Complex.Gamma ((2 : ℝ) + t * I) = (2 * Real.pi : ℂ) * ((Real.exp (-1 / (1 / (n * x))) : ℝ) :
            ℂ) := by
      rw [← hM, Complex.real_smul]
      push_cast
      rw [← mul_assoc, mul_one_div_cancel hpi, one_mul]
    rw [hM']
    have : (-1 / (1 / ((n : ℝ) * x))) = -(n * x) := by field_simp
    rw [this]
    push_cast
    ring_nf
  have hint : ∀ n : ℕ, Integrable (f n) := by
    intro n
    rcases eq_or_ne n 0 with rfl | hn
    · simp [hf]
    have hn0 : (0 : ℝ) < n := by exact_mod_cast Nat.pos_of_ne_zero hn
    have hy : (0 : ℝ) < 1 / (n * x) := by positivity
    have := (Complex.integrable_cpow_mul_Gamma_vertical (σ := 2) (by norm_num) hy).const_mul (a n)
    refine this.congr (Eventually.of_forall (fun t => ?_))
    simp only [hf, LSeries.term_of_ne_zero hn, hcpow n hn t]
    push_cast; ring
  -- the norm integrals
  have hG1 := Complex.integrable_cpow_mul_Gamma_vertical (σ := 2) (by norm_num) one_pos
  simp only [Complex.ofReal_one, Complex.one_cpow, one_mul] at hG1
  set I0 : ℝ := ∫ t : ℝ, ‖Complex.Gamma ((2 : ℝ) + t * I)‖ with hI0
  have hnorm : ∀ n : ℕ, ∫ t : ℝ, ‖f n t‖ =
      ‖LSeries.term (fun n => a n) 2 n‖ * x ^ (-2 : ℝ) * I0 := by
    intro n
    have e : ∀ t : ℝ, ‖f n t‖ = ‖LSeries.term (fun n => a n) 2 n‖ * x ^ (-2 : ℝ) *
        ‖Complex.Gamma ((2 : ℝ) + t * I)‖ := by
      intro t
      simp only [hf, norm_mul, LSeries.norm_term_eq, Complex.norm_cpow_eq_rpow_re_of_pos hx]
      simp
      split_ifs <;> ring
    simp_rw [e]
    rw [integral_const_mul]
  have hsumm : Summable (fun n => ∫ t : ℝ, ‖f n t‖) := by
    simp_rw [hnorm]
    exact (hsum.norm.mul_right _).mul_right _
  have hinter := integral_tsum_of_summable_integral_norm hint hsumm
  have hpt : ∀ t : ℝ, ∑' n, f n t =
      F (2 + t * I) * Complex.Gamma (2 + t * I) * (x : ℂ) ^ (-(2 + t * I)) := by
    intro t
    simp only [hf]
    rw [tsum_mul_right, ← LSeries, ← hF _ (by simp)]
    ring
  simp_rw [hpt] at hinter
  rw [← hinter]
  simp_rw [hint_n]
  rw [tsum_mul_left]
  field_simp
  apply tsum_congr; intro n; ring_nf

open Complex Filter Topology MeasureTheory in
/-- `t ↦ e^{-c|t|}` is integrable for `c > 0`. -/
private lemma integrable_exp_neg_mul_abs (c : ℝ) (hc : 0 < c) :
    Integrable (fun t : ℝ => Real.exp (-c * |t|)) := by
  have hI : Integrable (fun t : ℝ => 2 * (1 + (c * t) ^ 2)⁻¹) :=
    (integrable_inv_one_add_sq.comp_mul_left' hc.ne').const_mul 2
  refine hI.mono' (by fun_prop) (Eventually.of_forall (fun t => ?_))
  rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
  have hq := Real.quadratic_le_exp_of_nonneg (x := c * |t|) (by positivity)
  have hpos : 0 < 1 + (c * t) ^ 2 := by positivity
  have e : (c * |t|) ^ 2 = (c * t) ^ 2 := by rw [mul_pow, sq_abs, mul_pow]
  rw [e] at hq
  rw [show -c * |t| = -(c * |t|) by ring, Real.exp_neg, ← div_eq_mul_inv, ← one_div,
    div_le_div_iff₀ (Real.exp_pos _) hpos]
  nlinarith [abs_nonneg t, mul_nonneg hc.le (abs_nonneg t)]

open Complex Filter Topology MeasureTheory in
/-- A continuous function bounded by `B e^{-c|t|}` is integrable. -/
private lemma integrable_of_norm_le_exp_neg_mul_abs (g : ℝ → ℂ) (hg : Continuous g) (B c : ℝ) (hc :
    0 < c)
    (hb : ∀ t, ‖g t‖ ≤ B * Real.exp (-c * |t|)) : Integrable g :=
  ((integrable_exp_neg_mul_abs c hc).const_mul B).mono' hg.aestronglyMeasurable
    (Eventually.of_forall hb)

open Complex Filter Topology MeasureTheory in
/-- Continuity of `t ↦ F(σ+it) Γ(σ+it) x^{-(σ+it)}` on a line avoiding `1` and the poles. -/
private lemma continuous_mul_Gamma_line (F : ℂ → ℂ) (hFd : DifferentiableOn ℂ F {1}ᶜ) (σ : ℝ)
    (hσ1 : σ ≠ 1) (hσ : ∀ m : ℕ, σ ≠ -m) (x : ℝ) (hx : 0 < x) :
    Continuous (fun t : ℝ => F (σ + t * I) * Complex.Gamma (σ + t * I) *
      (x : ℂ) ^ (-((σ : ℂ) + t * I))) := by
  have hx0 : (x : ℂ) ≠ 0 := by exact_mod_cast hx.ne'
  have hpath : Continuous (fun t : ℝ => (σ : ℂ) + t * I) := by fun_prop
  rw [continuous_iff_continuousAt]
  intro t
  have hne1 : (σ : ℂ) + t * I ≠ 1 := by
    intro h; have := congrArg Complex.re h; simp only [add_re, ofReal_re, mul_re, I_re, mul_zero,
        ofReal_im, I_im, mul_one, sub_self, add_zero, one_re] at this; exact hσ1 this
  have hpole : ∀ m : ℕ, (σ : ℂ) + t * I ≠ -m := by
    intro m h; have := congrArg Complex.re h; simp only [add_re, ofReal_re, mul_re, I_re, mul_zero,
        ofReal_im, I_im, mul_one, sub_self, add_zero, neg_re, natCast_re] at this; exact hσ m this
  have hF : ContinuousAt F ((σ : ℂ) + t * I) :=
    (hFd.differentiableAt (isOpen_compl_singleton.mem_nhds hne1)).continuousAt
  have hG : ContinuousAt Complex.Gamma ((σ : ℂ) + t * I) :=
    (Complex.differentiableAt_Gamma _ hpole).continuousAt
  have hC : ContinuousAt (fun s : ℂ => (x : ℂ) ^ (-s)) ((σ : ℂ) + t * I) :=
    (differentiableAt_id.neg.const_cpow (Or.inl hx0)).continuousAt
  have hp : ContinuousAt (fun t : ℝ => (σ : ℂ) + t * I) t := hpath.continuousAt
  exact ((ContinuousAt.comp (f := fun t : ℝ => (σ : ℂ) + t * I) hF hp).mul
    (ContinuousAt.comp (f := fun t : ℝ => (σ : ℂ) + t * I) hG hp)).mul
    (ContinuousAt.comp (f := fun t : ℝ => (σ : ℂ) + t * I) hC hp)

open Complex Filter Topology MeasureTheory in
/-- A finite Laplace-type integral `w ↦ ∫_a^b φ(u) e^{-ψ(u) w} du` is entire. -/
private lemma differentiable_integral_mul_exp_neg_mul (φ ψ : ℝ → ℂ) (hφ : Continuous φ) (hψ :
    Continuous ψ) (a b : ℝ) :
    Differentiable ℂ (fun w : ℂ => ∫ u in a..b, φ u * Complex.exp (-(ψ u) * w)) := by
  intro w0
  obtain ⟨Mφ, hMφ⟩ := (isCompact_uIcc (a := a) (b := b)).exists_bound_of_continuousOn
    hφ.continuousOn
  obtain ⟨Mψ, hMψ⟩ := (isCompact_uIcc (a := a) (b := b)).exists_bound_of_continuousOn
    hψ.continuousOn
  have hMφ0 : 0 ≤ Mφ := (norm_nonneg _).trans (hMφ a Set.left_mem_uIcc)
  have hMψ0 : 0 ≤ Mψ := (norm_nonneg _).trans (hMψ a Set.left_mem_uIcc)
  set F' : ℂ → ℝ → ℂ := fun w u => φ u * (-(ψ u) * Complex.exp (-(ψ u) * w)) with hF'
  have key := intervalIntegral.hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (F := fun w u => φ u * Complex.exp (-(ψ u) * w)) (F' := F') (x₀ := w0)
    (bound := fun _ => Mφ * (Mψ * Real.exp (Mψ * (‖w0‖ + 1))))
    (μ := volume) (a := a) (b := b) (s := Metric.ball w0 1)
    (Metric.ball_mem_nhds w0 one_pos)
    (Eventually.of_forall (fun w => (by fun_prop : Continuous
      (fun u => φ u * Complex.exp (-(ψ u) * w))).aestronglyMeasurable))
    ((by fun_prop : Continuous (fun u => φ u * Complex.exp (-(ψ u) * w0))).intervalIntegrable _ _)
    ((by fun_prop : Continuous (F' w0)).aestronglyMeasurable)
    (Eventually.of_forall (fun u hu w hw => by
      have hu' : u ∈ Set.uIcc a b := Set.uIoc_subset_uIcc hu
      have h1 := hMφ u hu'
      have h2 := hMψ u hu'
      have hw' : ‖w‖ ≤ ‖w0‖ + 1 := by
        have := norm_le_norm_add_norm_sub' w w0
        rw [Metric.mem_ball, dist_eq_norm] at hw
        linarith
      simp only [hF', norm_mul, norm_neg]
      have he : ‖Complex.exp (-(ψ u) * w)‖ ≤ Real.exp (Mψ * (‖w0‖ + 1)) := by
        rw [Complex.norm_exp]
        apply Real.exp_le_exp.2
        calc (-(ψ u) * w).re ≤ ‖-(ψ u) * w‖ := Complex.re_le_norm _
          _ = ‖ψ u‖ * ‖w‖ := by rw [norm_mul, norm_neg]
          _ ≤ Mψ * (‖w0‖ + 1) := by gcongr
      gcongr))
    intervalIntegrable_const
    (Eventually.of_forall (fun u _ w _ => by
      simp only [hF']
      have h := ((hasDerivAt_id w).const_mul (-(ψ u))).cexp.const_mul (φ u)
      simpa [mul_comm, mul_left_comm, mul_assoc] using h))
  exact key.2.differentiableAt

open Complex Filter Topology MeasureTheory in
/-- Uniform decay of `F(s) Γ(s) x^{-s}` in a strip, from the decay of `F(s) Γ(s)`. -/
private lemma norm_mul_Gamma_cpow_strip_le (F : ℂ → ℂ) (a b M x : ℝ) (hx : 0 < x)
    (hM : ∀ s : ℂ, a ≤ s.re → s.re ≤ b → 1 ≤ |s.im| → ‖F s * Complex.Gamma s‖ ≤ M / |s.im|) :
    ∀ ε > (0 : ℝ), ∃ T₀, ∀ s : ℂ, a ≤ s.re → s.re ≤ b → T₀ ≤ |s.im| →
      ‖F s * Complex.Gamma s * (x : ℂ) ^ (-s)‖ ≤ ε := by
  intro ε hε
  set X : ℝ := x ^ (-a) + x ^ (-b) with hX
  have hX0 : 0 < X := by positivity
  have hxs : ∀ s : ℂ, a ≤ s.re → s.re ≤ b → ‖(x : ℂ) ^ (-s)‖ ≤ X := by
    intro s h1 h2
    rw [Complex.norm_cpow_eq_rpow_re_of_pos hx, Complex.neg_re]
    rcases le_or_gt 1 x with hx1 | hx1
    · have : x ^ (-s.re) ≤ x ^ (-a) := Real.rpow_le_rpow_of_exponent_le hx1 (by linarith)
      have : 0 ≤ x ^ (-b) := by positivity
      linarith
    · have : x ^ (-s.re) ≤ x ^ (-b) :=
        Real.rpow_le_rpow_of_exponent_ge hx hx1.le (by linarith)
      have : 0 ≤ x ^ (-a) := by positivity
      linarith
  refine ⟨max 1 (|M| * X / ε), fun s h1 h2 h3 => ?_⟩
  have ht1 : 1 ≤ |s.im| := le_trans (le_max_left _ _) h3
  have ht2 : |M| * X / ε ≤ |s.im| := le_trans (le_max_right _ _) h3
  have ht0 : 0 < |s.im| := by linarith
  rw [norm_mul]
  calc ‖F s * Complex.Gamma s‖ * ‖(x : ℂ) ^ (-s)‖ ≤ (|M| / |s.im|) * X := by
        apply mul_le_mul ((hM s h1 h2 ht1).trans (by gcongr; exact le_abs_self M)) (hxs s h1 h2)
          (norm_nonneg _) (by positivity)
    _ = |M| * X / |s.im| := by ring
    _ ≤ ε := by
        rw [div_le_iff₀ ht0]
        rw [div_le_iff₀ hε] at ht2
        linarith

open Complex Filter Topology MeasureTheory in
/-- One step of the contour shift: crossing the pole at `s = -(N+1)`. -/
private lemma contour_shift_step (F : ℂ → ℂ) (hFd : DifferentiableOn ℂ F {1}ᶜ) (N : ℕ)
    (x : ℝ) (hx : 0 < x) (A0 A1 c M : ℝ) (hc : 0 < c)
    (hl0 : ∀ t : ℝ, ‖F (-(N : ℂ) - 1 / 2 + t * I) * Complex.Gamma (-(N : ℂ) - 1 / 2 + t * I)‖ ≤
      A0 * Real.exp (-c * |t|))
    (hl1 : ∀ t : ℝ, ‖F (-((N + 1 : ℕ) : ℂ) - 1 / 2 + t * I) *
      Complex.Gamma (-((N + 1 : ℕ) : ℂ) - 1 / 2 + t * I)‖ ≤ A1 * Real.exp (-c * |t|))
    (hM : ∀ s : ℂ, -((N + 1 : ℕ) : ℝ) - 1 / 2 ≤ s.re → s.re ≤ -(N : ℝ) - 1 / 2 → 1 ≤ |s.im| →
      ‖F s * Complex.Gamma s‖ ≤ M / |s.im|) :
    (∫ t : ℝ, F ((-(N : ℝ) - 1 / 2 : ℝ) + t * I) * Complex.Gamma ((-(N : ℝ) - 1 / 2 : ℝ) + t * I) *
        (x : ℂ) ^ (-(((-(N : ℝ) - 1 / 2 : ℝ) : ℂ) + t * I))) =
      2 * (Real.pi : ℂ) * (F (-((N + 1 : ℕ) : ℂ)) * ((x ^ (N + 1) : ℝ) : ℂ) /
        ∏ k ∈ Finset.range (N + 1), ((k : ℂ) - ((N + 1 : ℕ) : ℂ))) +
      ∫ t : ℝ, F ((-((N + 1 : ℕ) : ℝ) - 1 / 2 : ℝ) + t * I) *
        Complex.Gamma ((-((N + 1 : ℕ) : ℝ) - 1 / 2 : ℝ) + t * I) *
          (x : ℂ) ^ (-(((-((N + 1 : ℕ) : ℝ) - 1 / 2 : ℝ) : ℂ) + t * I)) := by
  set h : ℂ → ℂ := fun s => F s * Complex.Gamma s * (x : ℂ) ^ (-s) with hh
  set a : ℝ := -((N + 1 : ℕ) : ℝ) - 1 / 2 with ha
  set b : ℝ := -(N : ℝ) - 1 / 2 with hb
  have hab : a ≤ b := by rw [ha, hb]; push_cast; linarith
  have hx0 : (x : ℂ) ≠ 0 := by exact_mod_cast hx.ne'
  have hnotint : ∀ (L : ℕ) (m : ℕ), (-(L : ℝ) - 1 / 2) ≠ -m := by
    intro L m h
    have h2 : (2 * (m : ℝ)) = 2 * L + 1 := by linarith
    have h3 : (2 * m : ℕ) = 2 * L + 1 := by exact_mod_cast h2
    omega
  have hne1 : ∀ L : ℕ, (-(L : ℝ) - 1 / 2) ≠ 1 := by
    intro L h; have := Nat.cast_nonneg (α := ℝ) L; linarith
  have hia : Integrable (fun t : ℝ => h (a + t * I)) := by
    apply integrable_of_norm_le_exp_neg_mul_abs _ (continuous_mul_Gamma_line F hFd a (hne1 _)
        (hnotint _) x hx)
      (A1 * x ^ (-a)) c hc
    intro t
    rw [norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos hx]
    have e : (-((a : ℂ) + t * I)).re = -a := by simp
    rw [e]
    have := hl1 t
    have e2 : ((a : ℝ) : ℂ) + t * I = -((N + 1 : ℕ) : ℂ) - 1 / 2 + t * I := by
      rw [ha]; push_cast; ring
    rw [e2]
    calc _ ≤ A1 * Real.exp (-c * |t|) * x ^ (-a) := by gcongr
      _ = _ := by ring
  have hib : Integrable (fun t : ℝ => h (b + t * I)) := by
    apply integrable_of_norm_le_exp_neg_mul_abs _ (continuous_mul_Gamma_line F hFd b (hne1 _)
        (hnotint _) x hx)
      (A0 * x ^ (-b)) c hc
    intro t
    rw [norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos hx]
    have e : (-((b : ℂ) + t * I)).re = -b := by simp
    rw [e]
    have := hl0 t
    have e2 : ((b : ℝ) : ℂ) + t * I = -(N : ℂ) - 1 / 2 + t * I := by
      rw [hb]; push_cast; ring
    rw [e2]
    calc _ ≤ A0 * Real.exp (-c * |t|) * x ^ (-b) := by gcongr
      _ = _ := by ring
  have hd : ∀ s : ℂ, a ≤ s.re → s.re ≤ b → 1 ≤ |s.im| → DifferentiableAt ℂ h s := by
    intro s h1 h2 h3
    have hs1 : s ≠ 1 := by
      intro e; rw [e] at h3; simp at h3; linarith
    have hpole : ∀ m : ℕ, s ≠ -m := by
      intro m e; rw [e] at h3; simp at h3; linarith
    exact ((hFd.differentiableAt (isOpen_compl_singleton.mem_nhds hs1)).mul
      (Complex.differentiableAt_Gamma s hpole)).mul
      (differentiableAt_id.neg.const_cpow (Or.inl hx0))
  have hS := sub_integral_vertical_eq_box h a b hab hd hia hib (norm_mul_Gamma_cpow_strip_le F a b M
      x hx hM)
  have hR := box_integral_pole_neg_nat F hFd (N + 1) (by omega) x hx
  have e1 : (-((N + 1 : ℕ) : ℝ) + 1 / 2) = b := by rw [hb]; push_cast; ring
  rw [e1] at hR
  simp only [hh] at hS
  rw [← ha] at hR
  rw [hR] at hS
  have hI : (I : ℂ) ≠ 0 := Complex.I_ne_zero
  have key : (∫ t : ℝ, F (b + t * I) * Complex.Gamma (b + t * I) * (x : ℂ) ^ (-((b : ℂ) + t * I))) -
      (∫ t : ℝ, F (a + t * I) * Complex.Gamma (a + t * I) * (x : ℂ) ^ (-((a : ℂ) + t * I))) =
      2 * (Real.pi : ℂ) * (F (-((N + 1 : ℕ) : ℂ)) * ((x ^ (N + 1) : ℝ) : ℂ) /
        ∏ k ∈ Finset.range (N + 1), ((k : ℂ) - ((N + 1 : ℕ) : ℂ))) := by
    apply mul_left_cancel₀ hI
    rw [hS]; ring
  linear_combination key

open Complex Filter Topology MeasureTheory in
/-- The first contour shift, from `Re s = 2` to `Re s = -N - 1/2`, across the box
`[-N - 1/2, 2] × [-1, 1]` which contains the poles at `1` and `0, -1, …, -N`. -/
private lemma contour_shift_first (a : ArithmeticFunction ℂ) (F : ℂ → ℂ)
    (hF : ∀ s : ℂ, 1 < s.re → F s = LSeries (fun n => a n) s)
    (hFd : DifferentiableOn ℂ F {1}ᶜ)
    (hsum : LSeriesSummable (fun n => a n) 2) (K : ℝ) (hK : ∀ s : ℂ, 3 / 2 ≤ s.re → ‖F s‖ ≤ K)
    (N : ℕ) (A0 c M : ℝ) (hc : 0 < c)
    (hl0 : ∀ t : ℝ, ‖F (-(N : ℂ) - 1 / 2 + t * I) * Complex.Gamma (-(N : ℂ) - 1 / 2 + t * I)‖ ≤
      A0 * Real.exp (-c * |t|))
    (hM : ∀ s : ℂ, -(N : ℝ) - 1 / 2 ≤ s.re → s.re ≤ 2 → 1 ≤ |s.im| →
      ‖F s * Complex.Gamma s‖ ≤ M / |s.im|)
    (x : ℝ) (hx : 0 < x) :
    ∑' n : ℕ, a n * Complex.exp (-(n : ℂ) * x) = (1 / (2 * Real.pi) : ℂ) *
      (∫ t : ℝ, F ((-(N : ℝ) - 1 / 2 : ℝ) + t * I) * Complex.Gamma ((-(N : ℝ) - 1 / 2 : ℝ) + t * I)
          *
        (x : ℂ) ^ (-(((-(N : ℝ) - 1 / 2 : ℝ) : ℂ) + t * I))) +
      (1 / (2 * Real.pi * I)) *
        ((∫ u : ℝ in (-(N : ℝ) - 1 / 2)..2, F (u + (-1 : ℝ) * I) * Complex.Gamma (u + (-1 : ℝ) * I)
            *
            Complex.exp (-(u + (-1 : ℝ) * I) * Complex.log x)) -
          (∫ u : ℝ in (-(N : ℝ) - 1 / 2)..2, F (u + (1 : ℝ) * I) * Complex.Gamma (u + (1 : ℝ) * I) *
            Complex.exp (-(u + (1 : ℝ) * I) * Complex.log x)) +
          I * (∫ y : ℝ in (-1 : ℝ)..1, F (((2 : ℝ) : ℂ) + y * I) * Complex.Gamma (((2 : ℝ) : ℂ) + y
              * I) *
            Complex.exp (-(((2 : ℝ) : ℂ) + y * I) * Complex.log x)) -
          I * (∫ y : ℝ in (-1 : ℝ)..1, F (((-(N : ℝ) - 1 / 2 : ℝ) : ℂ) + y * I) *
            Complex.Gamma (((-(N : ℝ) - 1 / 2 : ℝ) : ℂ) + y * I) *
            Complex.exp (-(((-(N : ℝ) - 1 / 2 : ℝ) : ℂ) + y * I) * Complex.log x))) := by
  set h : ℂ → ℂ := fun s => F s * Complex.Gamma s * (x : ℂ) ^ (-s) with hh
  set a0 : ℝ := -(N : ℝ) - 1 / 2 with ha0
  have hx0 : (x : ℂ) ≠ 0 := by exact_mod_cast hx.ne'
  have hab : a0 ≤ 2 := by rw [ha0]; have := Nat.cast_nonneg (α := ℝ) N; linarith
  have hnotint : ∀ m : ℕ, a0 ≠ -m := by
    intro m h
    rw [ha0] at h
    have h2 : (2 * (m : ℝ)) = 2 * N + 1 := by linarith
    have h3 : (2 * m : ℕ) = 2 * N + 1 := by exact_mod_cast h2
    omega
  have hne1 : a0 ≠ 1 := by rw [ha0]; have := Nat.cast_nonneg (α := ℝ) N; linarith
  have hia : Integrable (fun t : ℝ => h (a0 + t * I)) := by
    apply integrable_of_norm_le_exp_neg_mul_abs _ (continuous_mul_Gamma_line F hFd a0 hne1 hnotint x
        hx)
      (A0 * x ^ (-a0)) c hc
    intro t
    rw [norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos hx]
    have e : (-((a0 : ℂ) + t * I)).re = -a0 := by simp
    rw [e]
    have := hl0 t
    have e2 : ((a0 : ℝ) : ℂ) + t * I = -(N : ℂ) - 1 / 2 + t * I := by
      rw [ha0]; push_cast; ring
    rw [e2]
    calc _ ≤ A0 * Real.exp (-c * |t|) * x ^ (-a0) := by gcongr
      _ = _ := by ring
  have hG2 := Complex.integrable_cpow_mul_Gamma_vertical (σ := 2) (by norm_num) one_pos
  simp only [Complex.ofReal_one, Complex.one_cpow, one_mul] at hG2
  have hib : Integrable (fun t : ℝ => h ((2 : ℝ) + t * I)) := by
    refine (hG2.norm.const_mul (K * x ^ (-(2 : ℝ)))).mono'
      (continuous_mul_Gamma_line F hFd 2 (by norm_num) (fun m => by
        have := Nat.cast_nonneg (α := ℝ) m; intro h; linarith) x hx).aestronglyMeasurable
      (Eventually.of_forall (fun t => ?_))
    rw [norm_mul, norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos hx]
    have e : (-(((2 : ℝ) : ℂ) + t * I)).re = -2 := by simp
    rw [e]
    have hF2 := hK ((2 : ℝ) + t * I) (by simp; norm_num)
    calc ‖F ((2 : ℝ) + t * I)‖ * ‖Complex.Gamma ((2 : ℝ) + t * I)‖ * x ^ (-(2 : ℝ))
        ≤ K * ‖Complex.Gamma ((2 : ℝ) + t * I)‖ * x ^ (-(2 : ℝ)) := by gcongr
      _ = _ := by ring
  have hd : ∀ s : ℂ, a0 ≤ s.re → s.re ≤ 2 → 1 ≤ |s.im| → DifferentiableAt ℂ h s := by
    intro s h1 h2 h3
    have hs1 : s ≠ 1 := by
      intro e; rw [e] at h3; simp at h3; linarith
    have hpole : ∀ m : ℕ, s ≠ -m := by
      intro m e; rw [e] at h3; simp at h3; linarith
    exact ((hFd.differentiableAt (isOpen_compl_singleton.mem_nhds hs1)).mul
      (Complex.differentiableAt_Gamma s hpole)).mul
      (differentiableAt_id.neg.const_cpow (Or.inl hx0))
  have hS := sub_integral_vertical_eq_box h a0 2 hab hd hia hib (norm_mul_Gamma_cpow_strip_le F a0 2
      M x hx hM)
  have hMel := hasSum_exp_neg_eq_integral_line_two a F hF hsum x hx
  have hcp : ∀ s : ℂ, (x : ℂ) ^ (-s) = Complex.exp (-s * Complex.log x) := by
    intro s; rw [Complex.cpow_def_of_ne_zero hx0]; ring_nf
  simp only [hh, hcp] at hS
  simp only [hcp] at hMel ⊢
  rw [hMel]
  have hI : (I : ℂ) ≠ 0 := Complex.I_ne_zero
  have hpi : (2 * Real.pi : ℂ) ≠ 0 := by
    have := Real.pi_pos; exact_mod_cast (by positivity : (2 * Real.pi : ℝ) ≠ 0)
  have e2 : ∀ t : ℝ, (2 : ℂ) + t * I = ((2 : ℝ) : ℂ) + t * I := by intro t; push_cast; ring
  simp only [e2]
  have alg : ∀ X Y B : ℂ, I * (X - Y) = B →
      (1 / (2 * Real.pi) : ℂ) * X = (1 / (2 * Real.pi) : ℂ) * Y + (1 / (2 * Real.pi * I)) * B := by
    intro X Y B hB
    rw [← hB]
    field_simp
    ring
  exact alg _ _ _ hS

open Complex Filter Topology MeasureTheory in
/-- If `B N ρ^N → 0` for every `ρ > 0`, then `∑ B N ρ^N` converges for every `ρ > 0`. -/
private lemma summable_mul_pow_of_tendsto (B : ℕ → ℝ)
    (hB : ∀ ρ : ℝ, 0 < ρ → Tendsto (fun N : ℕ => B N * ρ ^ N) atTop (𝓝 0)) (ρ : ℝ) (hρ : 0 < ρ) :
    Summable (fun N : ℕ => B N * ρ ^ N) := by
  have h2 := hB (2 * ρ) (by positivity)
  have hev : ∀ᶠ N : ℕ in atTop, ‖B N * ρ ^ N‖ ≤ (1 / 2 : ℝ) ^ N := by
    filter_upwards [h2.eventually (Metric.ball_mem_nhds 0 one_pos)] with N hN
    rw [dist_zero_right] at hN
    have e : B N * ρ ^ N = (B N * (2 * ρ) ^ N) * (1 / 2) ^ N := by
      rw [mul_assoc, ← mul_pow, show (2 * ρ) * (1 / 2) = ρ by ring]
    rw [e, norm_mul, norm_pow, Real.norm_of_nonneg (by norm_num : (0 : ℝ) ≤ 1 / 2)]
    calc ‖B N * (2 * ρ) ^ N‖ * (1 / 2) ^ N ≤ 1 * (1 / 2) ^ N := by gcongr
      _ = _ := one_mul _
  exact Summable.of_norm_bounded_eventually_nat
    (summable_geometric_of_lt_one (by norm_num) (by norm_num)) hev

open Complex Filter Topology MeasureTheory in
/-- The power series produced by the contour shifts: summability and its sum. -/
private lemma hasSum_power_series_of_contour_shifts (J : ℕ → ℝ → ℂ) (B : ℕ → ℝ) (c : ℕ → ℂ) (N0 : ℕ)
    (hc0 : ∀ n ≤ N0, c n = 0)
    (hchain : ∀ N ≥ N0, ∀ x : ℝ, 0 < x → J N x = c (N + 1) * (x : ℂ) ^ (N + 1) + J (N + 1) x)
    (hJb : ∀ N ≥ N0, ∀ x : ℝ, 0 < x → ‖J N x‖ ≤ B N * x ^ ((N : ℝ) + 1 / 2))
    (hB : ∀ ρ : ℝ, 0 < ρ → Tendsto (fun N : ℕ => B N * ρ ^ N) atTop (𝓝 0)) :
    (∀ ρ : ℝ, 0 < ρ → Summable (fun n => ‖c n‖ * ρ ^ n)) ∧
      ∀ x : ℝ, 0 < x → J N0 x = ∑' n, c n * (x : ℂ) ^ n := by
  have hsumB := summable_mul_pow_of_tendsto B hB
  -- coefficient bound
  have hcb : ∀ N ≥ N0, ‖c (N + 1)‖ ≤ B N + B (N + 1) := by
    intro N hN
    have h := hchain N hN 1 one_pos
    simp only [Complex.ofReal_one, one_pow, mul_one] at h
    have e : c (N + 1) = J N 1 - J (N + 1) 1 := by rw [h]; ring
    have h1 := hJb N hN 1 one_pos
    have h2 := hJb (N + 1) (by omega) 1 one_pos
    simp only [Real.one_rpow, mul_one] at h1 h2
    rw [e]
    exact (norm_sub_le _ _).trans (add_le_add h1 h2)
  have hsumc : ∀ ρ : ℝ, 0 < ρ → Summable (fun n => ‖c n‖ * ρ ^ n) := by
    intro ρ hρ
    rw [← summable_nat_add_iff 1]
    have hg : Summable (fun N : ℕ => ρ * (B N * ρ ^ N) + B (N + 1) * ρ ^ (N + 1)) :=
      ((hsumB ρ hρ).mul_left ρ).add ((summable_nat_add_iff 1).mpr (hsumB ρ hρ))
    refine Summable.of_norm_bounded_eventually_nat hg ?_
    filter_upwards [eventually_ge_atTop N0] with N hN
    rw [Real.norm_of_nonneg (by positivity)]
    calc ‖c (N + 1)‖ * ρ ^ (N + 1) ≤ (B N + B (N + 1)) * ρ ^ (N + 1) := by
          gcongr; exact hcb N hN
      _ = ρ * (B N * ρ ^ N) + B (N + 1) * ρ ^ (N + 1) := by ring
  refine ⟨hsumc, fun x hx => ?_⟩
  -- partial sums
  have hpart : ∀ N ≥ N0, ∑ n ∈ Finset.range (N + 1), c n * (x : ℂ) ^ n = J N0 x - J N x := by
    intro N hN
    induction N, hN using Nat.le_induction with
    | base =>
      rw [sub_self]
      exact Finset.sum_eq_zero (fun n hn => by
        rw [hc0 n (Nat.lt_succ_iff.1 (Finset.mem_range.1 hn)), zero_mul])
    | succ N hN ih =>
      rw [Finset.sum_range_succ, ih, hchain N hN x hx]
      ring
  have hJ0 : Tendsto (fun N => J N x) atTop (𝓝 0) := by
    have hlim : Tendsto (fun N : ℕ => x ^ (1 / 2 : ℝ) * (B N * x ^ N)) atTop (𝓝 0) := by
      simpa using (hB x hx).const_mul (x ^ (1 / 2 : ℝ))
    refine squeeze_zero_norm' ?_ hlim
    filter_upwards [eventually_ge_atTop N0] with N hN
    refine (hJb N hN x hx).trans (le_of_eq ?_)
    rw [Real.rpow_add hx, Real.rpow_natCast]; ring
  have hS : Summable (fun n => c n * (x : ℂ) ^ n) := by
    refine Summable.of_norm ?_
    refine (hsumc x hx).congr (fun n => ?_)
    rw [norm_mul, norm_pow, Complex.norm_real, Real.norm_of_nonneg hx.le]
  have h1 : Tendsto (fun N => ∑ n ∈ Finset.range (N + 1), c n * (x : ℂ) ^ n) atTop
      (𝓝 (∑' n, c n * (x : ℂ) ^ n)) :=
    (hS.hasSum.tendsto_sum_nat).comp (tendsto_add_atTop_nat 1)
  have h2 : Tendsto (fun N => ∑ n ∈ Finset.range (N + 1), c n * (x : ℂ) ^ n) atTop
      (𝓝 (J N0 x)) := by
    have : Tendsto (fun N => J N0 x - J N x) atTop (𝓝 (J N0 x - 0)) :=
      tendsto_const_nhds.sub hJ0
    rw [sub_zero] at this
    refine this.congr' ?_
    filter_upwards [eventually_ge_atTop N0] with N hN
    exact (hpart N hN).symm
  exact tendsto_nhds_unique h2 h1

open Complex Filter Topology MeasureTheory in
/-- Continuity of `u ↦ F(γ u) Γ(γ u)` along a path avoiding `1` and the poles of `Γ`. -/
private lemma continuous_mul_Gamma_comp (F : ℂ → ℂ) (hFd : DifferentiableOn ℂ F {1}ᶜ) (γ : ℝ → ℂ)
    (hγ : Continuous γ) (h1 : ∀ u, γ u ≠ 1) (hp : ∀ u, ∀ m : ℕ, γ u ≠ -m) :
    Continuous (fun u => F (γ u) * Complex.Gamma (γ u)) := by
  rw [continuous_iff_continuousAt]
  intro u
  have hF : ContinuousAt F (γ u) :=
    (hFd.differentiableAt (isOpen_compl_singleton.mem_nhds (h1 u))).continuousAt
  have hG : ContinuousAt Complex.Gamma (γ u) :=
    (Complex.differentiableAt_Gamma _ (hp u)).continuousAt
  exact (ContinuousAt.comp (f := γ) hF hγ.continuousAt).mul
    (ContinuousAt.comp (f := γ) hG hγ.continuousAt)

open Complex Filter Topology MeasureTheory in
/-- The expansion `∑ a_n e^{-nx} = R(log x) + ∑ c_n x^n` for `x > 0`, with `R` entire and the
power series entire, valid when the degree is less than `1`. -/
private lemma exists_expansion_of_degree_lt_one (a : ArithmeticFunction ℂ) (F G : ℂ → ℂ) (m : ℕ) (D
    : FunctionalEquation F)
    (hF : ∀ s : ℂ, 1 < s.re → F s = LSeries (fun n => a n) s) (hFd : DifferentiableOn ℂ F {1}ᶜ)
    (hsum : LSeriesSummable (fun n => a n) 2) (K : ℝ) (hK : ∀ s : ℂ, 3 / 2 ≤ s.re → ‖F s‖ ≤ K)
    (hGd : Differentiable ℂ G) (hGF : ∀ s, s ≠ 1 → G s = (s - 1) ^ m * F s)
    (k C R : ℝ) (hk : 0 ≤ k) (hGg : ∀ s : ℂ, R ≤ ‖s‖ → ‖G s‖ ≤ C * Real.exp (‖s‖ ^ k))
    (hdeg : D.degree < 1) :
    ∃ (Rw : ℂ → ℂ) (c : ℕ → ℂ), Differentiable ℂ Rw ∧
      (∀ ρ : ℝ, 0 < ρ → Summable (fun n => ‖c n‖ * ρ ^ n)) ∧
      ∀ x : ℝ, 0 < x → ∑' n : ℕ, a n * Complex.exp (-(n : ℂ) * x) =
        Rw (Complex.log x) + ∑' n, c n * (x : ℂ) ^ n := by
  have hfe := FunctionalEquation.eq_of_re_lt_one hFd D
  have hK0 : 0 ≤ K := (norm_nonneg _).trans (hK 2 (by norm_num))
  set N0 : ℕ := ⌈∑ i, (D.r i).re / D.α i⌉₊ with hN0def
  have hN0 : ∀ N ≥ N0, ∀ i, (D.r i).re ≤ D.α i * N := by
    intro N hN i
    have hα := D.α_pos i
    have h1 : (D.r i).re / D.α i ≤ ∑ j, (D.r j).re / D.α j :=
      Finset.single_le_sum (f := fun j => (D.r j).re / D.α j)
        (fun j _ => div_nonneg (D.r_re_nonneg j) (D.α_pos j).le) (Finset.mem_univ i)
    have h2 : ∑ j, (D.r j).re / D.α j ≤ N0 := Nat.le_ceil _
    have h3 : (N0 : ℝ) ≤ N := by exact_mod_cast hN
    rw [div_le_iff₀ hα] at h1
    nlinarith
  set cc : ℝ := Real.pi * (1 - D.degree) / 2 with hcc
  have hcc0 : 0 < cc := by
    have := Real.pi_pos
    have : 0 < 1 - D.degree := by linarith
    positivity
  set A : ℕ → ℝ := fun N => K * D.Q ^ (2 * N + 2) *
    (∏ i, (Real.Gamma (D.α i * (N + 3 / 2) + (D.r i).re) *
      Real.Gamma (1 + D.α i * (N + 1 / 2) - (D.r i).re) *
        Real.exp (Real.pi * |(D.r i).im|) / Real.pi)) *
    (Real.sqrt (2 * Real.pi) / ∏ j ∈ Finset.range (N + 1), ((j : ℝ) + 1 / 2)) with hA
  have hl : ∀ N ≥ N0, ∀ t : ℝ, ‖F (-(N : ℂ) - 1 / 2 + t * I) *
      Complex.Gamma (-(N : ℂ) - 1 / 2 + t * I)‖ ≤ A N * Real.exp (-cc * |t|) := by
    intro N hN t
    have := norm_mul_Gamma_line_le F D K hfe hK N (hN0 N hN) t
    rw [hA, hcc]
    convert this using 3
  have hstrip : ∀ N ≥ N0, ∃ M, ∀ s : ℂ, -((N + 1 : ℕ) : ℝ) - 1 / 2 ≤ s.re →
      s.re ≤ -(N : ℝ) - 1 / 2 → 1 ≤ |s.im| → ‖F s * Complex.Gamma s‖ ≤ M / |s.im| := by
    intro N hN
    obtain ⟨B1, hB1⟩ := norm_edge_line_le F G m hGF (N + 1) (N + 1) le_rfl (A (N + 1)) cc hcc0
      (hl (N + 1) (by omega))
    obtain ⟨B2, hB2⟩ := norm_edge_line_le F G m hGF (N + 1) N (by omega) (A N) cc hcc0 (hl N hN)
    exact norm_mul_Gamma_strip_le F G m hGd hGF k C R hk hGg (N + 1) (-(N : ℝ) - 1 / 2)
      (by push_cast; linarith) (by have := Nat.cast_nonneg (α := ℝ) N; linarith) (max B1 B2)
      (fun s hs => by
        rcases hs with h | h
        · exact (hB1 s h).trans (le_max_left _ _)
        · exact (hB2 s h).trans (le_max_right _ _))
  obtain ⟨M0, hM0⟩ : ∃ M, ∀ s : ℂ, -(N0 : ℝ) - 1 / 2 ≤ s.re → s.re ≤ 2 → 1 ≤ |s.im| →
      ‖F s * Complex.Gamma s‖ ≤ M / |s.im| := by
    obtain ⟨B1, hB1⟩ := norm_edge_line_le F G m hGF N0 N0 le_rfl (A N0) cc hcc0 (hl N0 le_rfl)
    have hB2 := norm_edge_line_two_le F G m hGF K hK N0
    exact norm_mul_Gamma_strip_le F G m hGd hGF k C R hk hGg N0 2
      (by have := Nat.cast_nonneg (α := ℝ) N0; linarith) le_rfl
      (max B1 (K * Real.Gamma ((N0 : ℝ) + 3)))
      (fun s hs => by
        rcases hs with h | h
        · exact (hB1 s h).trans (le_max_left _ _)
        · exact (hB2 s h).trans (le_max_right _ _))
  set J : ℕ → ℝ → ℂ := fun N x => (1 / (2 * Real.pi) : ℂ) *
    ∫ t : ℝ, F ((-(N : ℝ) - 1 / 2 : ℝ) + t * I) * Complex.Gamma ((-(N : ℝ) - 1 / 2 : ℝ) + t * I) *
      (x : ℂ) ^ (-(((-(N : ℝ) - 1 / 2 : ℝ) : ℂ) + t * I)) with hJ
  set c : ℕ → ℂ := fun n => if N0 < n then F (-(n : ℂ)) / ∏ k ∈ Finset.range n, ((k : ℂ) - n)
    else 0 with hc
  set I1 : ℝ := ∫ t : ℝ, Real.exp (-cc * |t|) with hI1
  have hpi : (2 * Real.pi : ℂ) ≠ 0 := by
    have := Real.pi_pos; exact_mod_cast (by positivity : (2 * Real.pi : ℝ) ≠ 0)
  have hchain : ∀ N ≥ N0, ∀ x : ℝ, 0 < x →
      J N x = c (N + 1) * (x : ℂ) ^ (N + 1) + J (N + 1) x := by
    intro N hN x hx
    obtain ⟨M, hM⟩ := hstrip N hN
    have := contour_shift_step F hFd N x hx (A N) (A (N + 1)) cc M hcc0 (hl N hN)
      (hl (N + 1) (by omega)) hM
    simp only [hJ, hc, ite_eq_left (show N0 < N + 1 by omega)]
    rw [this, Complex.ofReal_pow]
    have alg : ∀ P Q X Y : ℂ, (1 / (2 * Real.pi) : ℂ) * (2 * Real.pi * (P * X / Q) + Y) =
        P / Q * X + (1 / (2 * Real.pi) : ℂ) * Y := by
      intro P Q X Y
      field_simp
    exact alg _ _ _ _
  have hJb : ∀ N ≥ N0, ∀ x : ℝ, 0 < x →
      ‖J N x‖ ≤ (I1 / (2 * Real.pi) * A N) * x ^ ((N : ℝ) + 1 / 2) := by
    intro N hN x hx
    simp only [hJ]
    rw [norm_mul]
    have hn : ‖(1 / (2 * Real.pi) : ℂ)‖ = 1 / (2 * Real.pi) := by
      rw [norm_div, norm_one, Complex.norm_mul, Complex.norm_two, Complex.norm_real,
        Real.norm_of_nonneg Real.pi_pos.le]
    rw [hn]
    have hint := (integrable_exp_neg_mul_abs cc hcc0).const_mul (A N * x ^ ((N : ℝ) + 1 / 2))
    have hle : ‖∫ t : ℝ, F ((-(N : ℝ) - 1 / 2 : ℝ) + t * I) *
        Complex.Gamma ((-(N : ℝ) - 1 / 2 : ℝ) + t * I) *
        (x : ℂ) ^ (-(((-(N : ℝ) - 1 / 2 : ℝ) : ℂ) + t * I))‖ ≤
        ∫ t : ℝ, A N * x ^ ((N : ℝ) + 1 / 2) * Real.exp (-cc * |t|) := by
      refine MeasureTheory.norm_integral_le_of_norm_le hint (Eventually.of_forall (fun t => ?_))
      rw [norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos hx]
      have e : (-(((-(N : ℝ) - 1 / 2 : ℝ) : ℂ) + t * I)).re = (N : ℝ) + 1 / 2 := by
        simp; ring
      rw [e]
      have e2 : (((-(N : ℝ) - 1 / 2 : ℝ) : ℂ) + t * I) = -(N : ℂ) - 1 / 2 + t * I := by
        push_cast; ring
      rw [e2]
      calc ‖F (-(N : ℂ) - 1 / 2 + t * I) * Complex.Gamma (-(N : ℂ) - 1 / 2 + t * I)‖ *
            x ^ ((N : ℝ) + 1 / 2) ≤ A N * Real.exp (-cc * |t|) * x ^ ((N : ℝ) + 1 / 2) := by
            gcongr; exact hl N hN t
        _ = _ := by ring
    rw [integral_const_mul] at hle
    calc 1 / (2 * Real.pi) * ‖∫ t : ℝ, F ((-(N : ℝ) - 1 / 2 : ℝ) + t * I) *
          Complex.Gamma ((-(N : ℝ) - 1 / 2 : ℝ) + t * I) *
          (x : ℂ) ^ (-(((-(N : ℝ) - 1 / 2 : ℝ) : ℂ) + t * I))‖
        ≤ 1 / (2 * Real.pi) * (A N * x ^ ((N : ℝ) + 1 / 2) * I1) := by
          gcongr
      _ = _ := by ring
  have hB : ∀ ρ : ℝ, 0 < ρ →
      Tendsto (fun N : ℕ => (I1 / (2 * Real.pi) * A N) * ρ ^ N) atTop (𝓝 0) := by
    intro ρ hρ
    have := (tendsto_line_bound_const_mul_pow D K hK0 hdeg N0 (hN0 N0 le_rfl) ρ hρ).const_mul (I1 /
        (2 * Real.pi))
    rw [mul_zero] at this
    refine this.congr (fun N => ?_)
    simp only [hA]
    ring
  obtain ⟨hsc, hser⟩ := hasSum_power_series_of_contour_shifts J _ c N0
    (fun n hn => by simp only [hc]; rw [ite_eq_right (by omega)]) hchain hJb hB
  set a0 : ℝ := -(N0 : ℝ) - 1 / 2 with ha0
  have hnotint : ∀ m : ℕ, a0 ≠ -m := by
    intro m h
    rw [ha0] at h
    have h2 : (2 * (m : ℝ)) = 2 * N0 + 1 := by linarith
    have h3 : (2 * m : ℕ) = 2 * N0 + 1 := by exact_mod_cast h2
    omega
  have hne1 : a0 ≠ 1 := by rw [ha0]; have := Nat.cast_nonneg (α := ℝ) N0; linarith
  refine ⟨fun w => (1 / (2 * Real.pi * I)) *
        ((∫ u : ℝ in a0..2, F (u + (-1 : ℝ) * I) * Complex.Gamma (u + (-1 : ℝ) * I) *
            Complex.exp (-(u + (-1 : ℝ) * I) * w)) -
          (∫ u : ℝ in a0..2, F (u + (1 : ℝ) * I) * Complex.Gamma (u + (1 : ℝ) * I) *
            Complex.exp (-(u + (1 : ℝ) * I) * w)) +
          I * (∫ y : ℝ in (-1 : ℝ)..1, F (((2 : ℝ) : ℂ) + y * I) *
            Complex.Gamma (((2 : ℝ) : ℂ) + y * I) *
            Complex.exp (-(((2 : ℝ) : ℂ) + y * I) * w)) -
          I * (∫ y : ℝ in (-1 : ℝ)..1, F ((a0 : ℂ) + y * I) *
            Complex.Gamma ((a0 : ℂ) + y * I) *
            Complex.exp (-((a0 : ℂ) + y * I) * w))), c, ?_, hsc, fun x hx => ?_⟩
  · have hc1 : Continuous (fun u : ℝ => F ((u : ℂ) + ((-1 : ℝ) : ℂ) * I) *
        Complex.Gamma ((u : ℂ) + ((-1 : ℝ) : ℂ) * I)) :=
      continuous_mul_Gamma_comp F hFd (fun u : ℝ => (u : ℂ) + ((-1 : ℝ) : ℂ) * I) (by fun_prop)
        (fun u h => by have := congrArg Complex.im h; simp at this)
        (fun u m h => by have := congrArg Complex.im h; simp at this)
    have hc2 : Continuous (fun u : ℝ => F ((u : ℂ) + ((1 : ℝ) : ℂ) * I) *
        Complex.Gamma ((u : ℂ) + ((1 : ℝ) : ℂ) * I)) :=
      continuous_mul_Gamma_comp F hFd (fun u : ℝ => (u : ℂ) + ((1 : ℝ) : ℂ) * I) (by fun_prop)
        (fun u h => by have := congrArg Complex.im h; simp at this)
        (fun u m h => by have := congrArg Complex.im h; simp at this)
    have hc3 : Continuous (fun y : ℝ => F (((2 : ℝ) : ℂ) + y * I) *
        Complex.Gamma (((2 : ℝ) : ℂ) + y * I)) :=
      continuous_mul_Gamma_comp F hFd (fun y : ℝ => ((2 : ℝ) : ℂ) + y * I) (by fun_prop)
        (fun u h => by have := congrArg Complex.re h; norm_num at this)
        (fun u m h => by
          have := congrArg Complex.re h; simp at this
          have := Nat.cast_nonneg (α := ℝ) m; linarith)
    have hc4 : Continuous (fun y : ℝ => F ((a0 : ℂ) + y * I) * Complex.Gamma ((a0 : ℂ) + y * I)) :=
      continuous_mul_Gamma_comp F hFd (fun y : ℝ => (a0 : ℂ) + y * I) (by fun_prop)
        (fun u h => by
            have := congrArg Complex.re h
            simp only [add_re, ofReal_re, mul_re, I_re, mul_zero, ofReal_im, I_im, mul_one,
              sub_self, add_zero, one_re] at this
            exact hne1 this)
        (fun u m h => by
            have := congrArg Complex.re h
            simp only [add_re, ofReal_re, mul_re, I_re, mul_zero, ofReal_im, I_im, mul_one,
              sub_self, add_zero, neg_re, natCast_re] at this
            exact hnotint m this)
    have D1 := differentiable_integral_mul_exp_neg_mul _ (fun u : ℝ => (u : ℂ) + ((-1 : ℝ) : ℂ) * I)
        hc1 (by fun_prop) a0 2
    have D2 := differentiable_integral_mul_exp_neg_mul _ (fun u : ℝ => (u : ℂ) + ((1 : ℝ) : ℂ) * I)
        hc2 (by fun_prop) a0 2
    have D3 := differentiable_integral_mul_exp_neg_mul _ (fun y : ℝ => ((2 : ℝ) : ℂ) + y * I) hc3
        (by fun_prop) (-1) 1
    have D4 := differentiable_integral_mul_exp_neg_mul _ (fun y : ℝ => (a0 : ℂ) + y * I) hc4 (by
        fun_prop) (-1) 1
    exact (((D1.sub D2).add (D3.const_mul I)).sub (D4.const_mul I)).const_mul _
  · rw [contour_shift_first a F hF hFd hsum K hK N0 (A N0) cc M0 hcc0 (hl N0 le_rfl) hM0 x hx,
      ← hser x hx]
    simp only [hJ]
    ring

open Complex Filter Topology MeasureTheory in
/-- Coefficients of a `2πi`-periodic function holomorphic on the upper half-plane, given by
`∑ a_k e^{-kz}` on the line `Re z = 1`, decay like `e^{-n}`. -/
private lemma norm_coeff_le_of_periodic (a : ℕ → ℂ) (g : ℂ → ℂ) (hg : DifferentiableOn ℂ g {z | 0 <
    z.im})
    (hper : ∀ z : ℂ, 0 < z.im → g (z + 2 * Real.pi * I) = g z)
    (hsum : Summable (fun k : ℕ => ‖a k‖ * Real.exp (-(k : ℝ))))
    (heq : ∀ y : ℝ, 0 < y → g (1 + y * I) = ∑' k : ℕ, a k * Complex.exp (-(k : ℂ) * (1 + y * I))) :
    ∃ M, ∀ n : ℕ, ‖a n‖ ≤ M * Real.exp (-(n : ℝ)) := by
  have hpi := Real.pi_pos
  -- a bound for `g` on the segment `Re z = -1`, `1 ≤ Im z ≤ 1 + 2π`
  have hcont : ContinuousOn (fun y : ℝ => g (-1 + y * I)) (Set.Icc 1 (1 + 2 * Real.pi)) := by
    refine hg.continuousOn.comp (by fun_prop) ?_
    intro y hy
    simp only [Set.mem_ofPred_eq]
    simp; linarith [hy.1]
  obtain ⟨Mf, hMf⟩ := isCompact_Icc.exists_bound_of_continuousOn hcont
  refine ⟨Mf, fun n => ?_⟩
  set φ : ℂ → ℂ := fun z => g z * Complex.exp (n * z) with hφ
  -- the rectangle
  have hrect := Complex.integral_boundary_rect_eq_zero_of_differentiableOn φ ⟨-1, 1⟩
    ⟨1, 1 + 2 * Real.pi⟩ (by
      intro z hz
      simp only [Complex.mem_reProdIm, Set.uIcc_of_le (show (-1 : ℝ) ≤ 1 by norm_num),
        Set.uIcc_of_le (show (1 : ℝ) ≤ 1 + 2 * Real.pi by linarith), Set.mem_Icc] at hz
      have hzH : z ∈ {z : ℂ | 0 < z.im} := by simp only [Set.mem_ofPred_eq]; linarith [hz.2.1]
      exact ((hg.differentiableAt (isOpen_lt continuous_const Complex.continuous_im |>.mem_nhds
        hzH)).mul ((differentiableAt_id.const_mul _).cexp)).differentiableWithinAt)
  simp only [smul_eq_mul] at hrect
  have htop : ∀ x : ℝ, φ ((x : ℂ) + ((1 + 2 * Real.pi : ℝ) : ℂ) * I) =
      φ ((x : ℂ) + ((1 : ℝ) : ℂ) * I) := by
    intro x
    simp only [hφ]
    have e : (x : ℂ) + ((1 + 2 * Real.pi : ℝ) : ℂ) * I = ((x : ℂ) + ((1 : ℝ) : ℂ) * I) +
        2 * Real.pi * I := by push_cast; ring
    rw [e, hper _ (by simp)]
    congr 1
    rw [mul_add, Complex.exp_add]
    have : Complex.exp (n * (2 * Real.pi * I)) = 1 := Complex.exp_nat_mul_two_pi_mul_I n
    rw [this, mul_one]
  simp only [htop, sub_self, zero_add] at hrect
  have hRL : (∫ y : ℝ in (1 : ℝ)..(1 + 2 * Real.pi), φ (((1 : ℝ) : ℂ) + y * I)) =
      ∫ y : ℝ in (1 : ℝ)..(1 + 2 * Real.pi), φ (((-1 : ℝ) : ℂ) + y * I) := by
    have : I * ((∫ y : ℝ in (1 : ℝ)..(1 + 2 * Real.pi), φ (((1 : ℝ) : ℂ) + y * I)) -
        ∫ y : ℝ in (1 : ℝ)..(1 + 2 * Real.pi), φ (((-1 : ℝ) : ℂ) + y * I)) = 0 := by
      rw [← hrect]; ring
    rcases mul_eq_zero.1 this with h | h
    · exact absurd h Complex.I_ne_zero
    · exact sub_eq_zero.1 h
  -- the right side is `2π a_n`
  have hterm : ∀ k : ℕ, ∫ y : ℝ in (1 : ℝ)..(1 + 2 * Real.pi),
      a k * Complex.exp (((n : ℂ) - k) * (1 + y * I)) =
        if k = n then 2 * Real.pi * a n else 0 := by
    intro k
    split_ifs with hk
    · subst hk
      simp only [sub_self, zero_mul, Complex.exp_zero, mul_one, intervalIntegral.integral_const,
        Complex.real_smul]
      push_cast; ring
    · have hc : ((n : ℂ) - k) * I ≠ 0 := by
        apply mul_ne_zero _ Complex.I_ne_zero
        intro h; apply hk; exact_mod_cast (sub_eq_zero.1 h).symm
      have e : ∀ y : ℝ, a k * Complex.exp (((n : ℂ) - k) * (1 + y * I)) =
          (a k * Complex.exp ((n : ℂ) - k)) * Complex.exp ((((n : ℂ) - k) * I) * y) := by
        intro y; rw [mul_assoc, ← Complex.exp_add]; ring_nf
      simp_rw [e]
      rw [intervalIntegral.integral_const_mul, integral_exp_mul_complex hc]
      have hper2 : Complex.exp ((((n : ℂ) - k) * I) * ((1 + 2 * Real.pi : ℝ) : ℂ)) =
          Complex.exp ((((n : ℂ) - k) * I) * ((1 : ℝ) : ℂ)) := by
        have : (((n : ℂ) - k) * I) * ((1 + 2 * Real.pi : ℝ) : ℂ) =
            (((n : ℂ) - k) * I) * ((1 : ℝ) : ℂ) + (((n : ℤ) - k : ℤ) : ℂ) * (2 * Real.pi * I) := by
          push_cast; ring
        rw [this, Complex.exp_add, Complex.exp_int_mul_two_pi_mul_I, mul_one]
      rw [hper2, sub_self, zero_div, mul_zero]
  have hsum' : Summable (fun k : ℕ => ‖a k‖ * Real.exp ((n : ℝ) - k)) := by
    refine (hsum.mul_left (Real.exp n)).congr (fun k => ?_)
    rw [Real.exp_sub]; field_simp; rw [Real.exp_neg]; field_simp
  have hR : (∫ y : ℝ in (1 : ℝ)..(1 + 2 * Real.pi), φ (((1 : ℝ) : ℂ) + y * I)) =
      2 * Real.pi * a n := by
    have hpt : ∀ y ∈ Set.uIcc (1 : ℝ) (1 + 2 * Real.pi), φ (((1 : ℝ) : ℂ) + y * I) =
        ∑' k : ℕ, a k * Complex.exp (((n : ℂ) - k) * (1 + y * I)) := by
      intro y hy
      rw [Set.uIcc_of_le (by linarith)] at hy
      simp only [hφ]
      push_cast
      rw [heq y (by linarith [hy.1]), ← tsum_mul_right]
      apply tsum_congr
      intro k
      rw [mul_assoc, ← Complex.exp_add]
      ring_nf
    rw [intervalIntegral.integral_congr hpt]
    let f : ℕ → C(ℝ, ℂ) := fun k =>
      ⟨fun y => a k * Complex.exp (((n : ℂ) - k) * (1 + y * I)), by fun_prop⟩
    have hinter := intervalIntegral.tsum_intervalIntegral_eq_of_summable_norm
      (a := 1) (b := 1 + 2 * Real.pi) (f := f) (by
        refine Summable.of_nonneg_of_le (fun _ => norm_nonneg _) (fun k => ?_) hsum'
        refine (ContinuousMap.norm_le _ (by positivity)).2 (fun y => ?_)
        simp only [f, ContinuousMap.restrict_apply, ContinuousMap.coe_mk]
        rw [norm_mul, Complex.norm_exp]
        apply le_of_eq
        congr 2
        simp)
    simp only [f, ContinuousMap.coe_mk] at hinter
    rw [← hinter]
    simp_rw [hterm]
    rw [tsum_ite_eq]
  have hL : ‖∫ y : ℝ in (1 : ℝ)..(1 + 2 * Real.pi), φ (((-1 : ℝ) : ℂ) + y * I)‖ ≤
      Mf * Real.exp (-(n : ℝ)) * |1 + 2 * Real.pi - 1| := by
    apply intervalIntegral.norm_integral_le_of_norm_le_const
    intro y hy
    rw [Set.uIoc_of_le (by linarith)] at hy
    simp only [hφ]
    rw [norm_mul, Complex.norm_exp]
    have h1 := hMf y ⟨hy.1.le, hy.2⟩
    have h2 : (n * (((-1 : ℝ) : ℂ) + y * I)).re = -(n : ℝ) := by simp
    rw [h2]
    gcongr
    simpa using h1
  rw [← hRL, hR] at hL
  rw [norm_mul, show |1 + 2 * Real.pi - 1| = 2 * Real.pi by rw [add_sub_cancel_left,
    abs_of_pos (by positivity)]] at hL
  have : ‖(2 * Real.pi : ℂ)‖ = 2 * Real.pi := by
    rw [Complex.norm_mul, Complex.norm_two, Complex.norm_real, Real.norm_of_nonneg hpi.le]
  rw [this] at hL
  nlinarith

open Complex Filter Topology MeasureTheory in
/-- From the expansion, the coefficients decay exponentially. -/
private lemma exists_norm_coeff_le_exp_neg_of_degree_lt_one (a : ArithmeticFunction ℂ) (Ca : ℝ)
    (hCa : ∀ n : ℕ, ‖a n‖ ≤ Ca * (n : ℝ) ^ (1 : ℝ)) (Rw : ℂ → ℂ) (c : ℕ → ℂ)
    (hRw : Differentiable ℂ Rw) (hc : ∀ ρ : ℝ, 0 < ρ → Summable (fun n => ‖c n‖ * ρ ^ n))
    (hexp : ∀ x : ℝ, 0 < x → ∑' n : ℕ, a n * Complex.exp (-(n : ℂ) * x) =
      Rw (Complex.log x) + ∑' n, c n * (x : ℂ) ^ n) :
    ∃ M, ∀ n : ℕ, ‖a n‖ ≤ M * Real.exp (-(n : ℝ)) := by
  have hCa' : ∀ n : ℕ, ‖a n‖ ≤ Ca * n := fun n => by simpa using hCa n
  set f : ℂ → ℂ := fun z => ∑' n : ℕ, a n * Complex.exp (-(n : ℂ) * z) with hf
  -- `f` is holomorphic on the right half-plane
  have hfd : DifferentiableOn ℂ f {z | 0 < z.re} := by
    intro z0 hz0
    simp only [Set.mem_ofPred_eq] at hz0
    set δ : ℝ := z0.re / 2 with hδ
    have hδ0 : 0 < δ := by positivity
    have hU : IsOpen {z : ℂ | δ < z.re} := isOpen_lt continuous_const Complex.continuous_re
    have hdU := differentiableOn_tsum_of_summable_norm
      (F := fun n : ℕ => fun z : ℂ => a n * Complex.exp (-(n : ℂ) * z))
      (u := fun n : ℕ => Ca * ((n : ℝ) ^ 1 * Real.exp (-δ * n)))
      ((Real.summable_pow_mul_exp_neg_nat_mul 1 hδ0).mul_left Ca)
      (fun n => ((differentiable_id.const_mul _).cexp.const_mul _).differentiableOn) hU
      (fun n w hw => by
        simp only [Set.mem_ofPred_eq] at hw
        rw [norm_mul, Complex.norm_exp, pow_one]
        have hre : (-(n : ℂ) * w).re = -(n * w.re) := by simp
        rw [hre]
        have h1 : Real.exp (-(n * w.re)) ≤ Real.exp (-δ * n) := by
          apply Real.exp_le_exp.2
          have := Nat.cast_nonneg (α := ℝ) n
          nlinarith
        calc ‖a n‖ * Real.exp (-(n * w.re)) ≤ (Ca * n) * Real.exp (-δ * n) :=
              mul_le_mul (hCa' n) h1 (by positivity) (le_trans (norm_nonneg _) (hCa' n))
          _ = _ := by ring)
    exact (hdU.differentiableAt
      (hU.mem_nhds (by simp only [Set.mem_ofPred_eq]; linarith))).differentiableWithinAt
  -- the power series is entire
  set E : ℂ → ℂ := fun z => ∑' n, c n * z ^ n with hE
  have hEd : Differentiable ℂ E := by
    intro z0
    set ρ : ℝ := ‖z0‖ + 1 with hρ
    have hρ0 : 0 < ρ := by positivity
    have hdU := differentiableOn_tsum_of_summable_norm
      (F := fun n : ℕ => fun z : ℂ => c n * z ^ n) (u := fun n => ‖c n‖ * ρ ^ n) (hc ρ hρ0)
      (fun n => ((differentiable_id.pow n).const_mul _).differentiableOn)
      (Metric.isOpen_ball (x := (0 : ℂ)) (ε := ρ))
      (fun n w hw => by
        rw [Metric.mem_ball, dist_zero_right] at hw
        rw [norm_mul, norm_pow]
        gcongr)
    exact hdU.differentiableAt (Metric.isOpen_ball.mem_nhds (by simp [hρ]))
  set g : ℂ → ℂ := fun z => Rw (Complex.log z) + E z with hg
  have hgd : DifferentiableOn ℂ g Complex.slitPlane := by
    intro z hz
    exact ((hRw _).comp z (Complex.differentiableAt_log hz) |>.add (hEd z)).differentiableWithinAt
  -- `f = g` on the right half-plane
  have hV : IsOpen {z : ℂ | 0 < z.re} := isOpen_lt continuous_const Complex.continuous_re
  have hVsl : {z : ℂ | 0 < z.re} ⊆ Complex.slitPlane := fun z hz => Or.inl hz
  have hfg : Set.EqOn f g {z | 0 < z.re} := by
    have hfa : AnalyticOnNhd ℂ f {z | 0 < z.re} := hfd.analyticOnNhd hV
    have hga : AnalyticOnNhd ℂ g {z | 0 < z.re} := (hgd.mono hVsl).analyticOnNhd hV
    refine hfa.eqOn_of_preconnected_of_frequently_eq hga (convex_halfSpace_re_gt 0).isPreconnected
      (show (1 : ℂ) ∈ {z : ℂ | 0 < z.re} by simp) ?_
    have hT : Tendsto (fun x : ℝ => (x : ℂ)) (𝓝[≠] (1 : ℝ)) (𝓝[≠] (1 : ℂ)) := by
      apply tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within
      · exact (Complex.continuous_ofReal.tendsto 1).mono_left nhdsWithin_le_nhds |>.trans
          (by simp)
      · filter_upwards [self_mem_nhdsWithin] with x hx
        simp only [Set.mem_compl_iff, Set.mem_singleton_iff] at hx ⊢
        exact_mod_cast hx
    apply hT.frequently
    apply Eventually.frequently
    have hpos : ∀ᶠ x : ℝ in 𝓝[≠] (1 : ℝ), 0 < x :=
      nhdsWithin_le_nhds (lt_mem_nhds (by norm_num : (0 : ℝ) < 1))
    filter_upwards [hpos] with x hx
    exact hexp x hx
  -- `f` is `2πi`-periodic
  have hfper : ∀ z : ℂ, f (z + 2 * Real.pi * I) = f z := by
    intro z
    simp only [hf]
    apply tsum_congr
    intro n
    congr 1
    rw [mul_add, Complex.exp_add]
    have : Complex.exp (-(n : ℂ) * (2 * Real.pi * I)) = 1 := by
      rw [neg_mul, Complex.exp_neg, Complex.exp_nat_mul_two_pi_mul_I, inv_one]
    rw [this, mul_one]
  -- `g` is `2πi`-periodic on the upper half-plane
  have hH : IsOpen {z : ℂ | 0 < z.im} := isOpen_lt continuous_const Complex.continuous_im
  have hHsl : {z : ℂ | 0 < z.im} ⊆ Complex.slitPlane := fun z hz => Or.inr (ne_of_gt hz)
  have hgper : ∀ z : ℂ, 0 < z.im → g (z + 2 * Real.pi * I) = g z := by
    have hga : AnalyticOnNhd ℂ g {z | 0 < z.im} := (hgd.mono hHsl).analyticOnNhd hH
    have hga' : AnalyticOnNhd ℂ (fun z => g (z + 2 * Real.pi * I)) {z | 0 < z.im} := by
      apply DifferentiableOn.analyticOnNhd _ hH
      intro z hz
      have hz' : z + 2 * Real.pi * I ∈ Complex.slitPlane := by
        apply hHsl
        simp only [Set.mem_ofPred_eq] at hz ⊢
        simp; have := Real.pi_pos; linarith
      exact ((hgd.differentiableAt (Complex.isOpen_slitPlane.mem_nhds hz')).comp z
        (differentiableAt_id.add_const _)).differentiableWithinAt
    have hloc : (fun z => g (z + 2 * Real.pi * I)) =ᶠ[𝓝 (1 + I)] g := by
      have hQ : {z : ℂ | 0 < z.re ∧ 0 < z.im} ∈ 𝓝 (1 + I) :=
        (hV.inter hH).mem_nhds (by simp)
      filter_upwards [hQ] with z hz
      have h1 : z + 2 * Real.pi * I ∈ {z : ℂ | 0 < z.re} := by simp [hz.1]
      rw [← hfg h1, ← hfg (show z ∈ {z : ℂ | 0 < z.re} from hz.1), hfper]
    intro z hz
    exact hga'.eqOn_of_preconnected_of_eventuallyEq hga (convex_halfSpace_im_gt 0).isPreconnected
      (show (1 + I : ℂ) ∈ {z : ℂ | 0 < z.im} by simp) hloc hz
  -- apply the coefficient bound
  have hsum : Summable (fun k : ℕ => ‖a k‖ * Real.exp (-(k : ℝ))) := by
    refine Summable.of_nonneg_of_le (fun _ => by positivity) (fun k => ?_)
      ((Real.summable_pow_mul_exp_neg_nat_mul 1 one_pos).mul_left Ca)
    calc ‖a k‖ * Real.exp (-(k : ℝ)) ≤ (Ca * k) * Real.exp (-(k : ℝ)) := by
          gcongr; exact hCa' k
      _ = Ca * ((k : ℝ) ^ 1 * Real.exp (-1 * k)) := by ring_nf
  exact norm_coeff_le_of_periodic (fun n => a n) g (hgd.mono hHsl) hgper hsum (fun y hy => by
    rw [← hfg (show (1 + y * I : ℂ) ∈ {z : ℂ | 0 < z.re} by simp)])

open Complex Filter Topology MeasureTheory in
/-- Stirling on vertical lines: `‖Γ(x₁+iy)‖ / ‖Γ(x₂+iy)‖ ≥ y^{x₁-x₂}/4` for large `y`. -/
private lemma eventually_norm_Gamma_div_ge (x1 x2 : ℝ) :
    ∀ᶠ y : ℝ in atTop, (1 / 4) * y ^ (x1 - x2) ≤
      ‖Complex.Gamma (x1 + y * I)‖ / ‖Complex.Gamma (x2 + y * I)‖ := by
  have hle : (atTop : Filter ℝ) ≤ Filter.comap (fun t : ℝ => |t|) atTop :=
    tendsto_abs_atTop_atTop.le_comap
  have h1 := ((Complex.norm_Gamma_vertical_isEquivalent x1).isLittleO.bound
    (by norm_num : (0 : ℝ) < 1 / 2))
  have h2 := ((Complex.norm_Gamma_vertical_isEquivalent x2).isLittleO.bound
    (by norm_num : (0 : ℝ) < 1 / 2))
  filter_upwards [hle h1, hle h2, eventually_gt_atTop 0] with y hy1 hy2 hy0
  simp only [Pi.sub_apply, Real.norm_eq_abs] at hy1 hy2
  set v1 := Real.exp (-(Real.pi * |y|) / 2) * |y| ^ (x1 - 1 / 2) * Real.sqrt (2 * Real.pi) with hv1
  set v2 := Real.exp (-(Real.pi * |y|) / 2) * |y| ^ (x2 - 1 / 2) * Real.sqrt (2 * Real.pi) with hv2
  have hv1p : 0 < v1 := by have := Real.pi_pos; positivity
  have hv2p : 0 < v2 := by have := Real.pi_pos; positivity
  rw [abs_of_pos hv1p] at hy1
  rw [abs_of_pos hv2p] at hy2
  have hu1 : v1 / 2 ≤ ‖Complex.Gamma (x1 + y * I)‖ := by
    have := (abs_le.1 hy1).1; linarith
  have hu2 : ‖Complex.Gamma (x2 + y * I)‖ ≤ 2 * v2 := by
    have := (abs_le.1 hy2).2; linarith
  have hu2p : 0 < ‖Complex.Gamma (x2 + y * I)‖ := by
    have := (abs_le.1 hy2).1; linarith
  have hratio : v1 / v2 = y ^ (x1 - x2) := by
    rw [hv1, hv2, abs_of_pos hy0]
    have hE : 0 < Real.exp (-(Real.pi * y) / 2) := Real.exp_pos _
    have hS : 0 < Real.sqrt (2 * Real.pi) := by have := Real.pi_pos; positivity
    have e : y ^ (x1 - 1 / 2) = y ^ (x2 - 1 / 2) * y ^ (x1 - x2) := by
      rw [← Real.rpow_add hy0]; ring_nf
    rw [e]
    have : 0 < y ^ (x2 - 1 / 2) := by positivity
    field_simp
  rw [le_div_iff₀ hu2p]
  calc 1 / 4 * y ^ (x1 - x2) * ‖Complex.Gamma (x2 + y * I)‖
      ≤ 1 / 4 * y ^ (x1 - x2) * (2 * v2) := by gcongr
    _ = v1 / 2 := by rw [← hratio]; field_simp; ring
    _ ≤ _ := hu1

open Complex Filter Topology MeasureTheory in
/-- If the coefficients decay exponentially, the functional equation of positive degree is
impossible: Stirling makes `F(1 - σ + it)` unbounded while the Dirichlet series bounds it. -/
private lemma degree_bound_of_coeff_decay (a : ArithmeticFunction ℂ) (ha1 : a 1 = 1) (M : ℝ)
    (hM : ∀ n : ℕ, ‖a n‖ ≤ M * Real.exp (-(n : ℝ))) (F : ℂ → ℂ) (hF : IsLSeriesContinuation a F)
    (D : FunctionalEquation F) (hpos : 0 < D.degree) : False := by
  have hfe := FunctionalEquation.eq_of_re_lt_one hF.2 D
  have hM0 : 0 ≤ M := by
    have := (norm_nonneg (a 0)).trans (hM 0); simpa using this
  -- the Dirichlet series converges everywhere
  have hsumm : ∀ s : ℂ, LSeriesSummable (fun n => a n) s := by
    intro s
    set k : ℕ := ⌈|s.re|⌉₊ with hk
    refine Summable.of_norm_bounded ((Real.summable_pow_mul_exp_neg_nat_mul k one_pos).mul_left M)
      (fun n => ?_)
    rw [LSeries.norm_term_eq]
    split_ifs with hn
    · positivity
    · have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast Nat.one_le_iff_ne_zero.2 hn
      have hn0 : (0 : ℝ) < n := by linarith
      rw [div_eq_mul_inv, ← Real.rpow_neg hn0.le]
      have h1 : (n : ℝ) ^ (-s.re) ≤ (n : ℝ) ^ k := by
        rw [← Real.rpow_natCast]
        apply Real.rpow_le_rpow_of_exponent_le hn1
        have := Nat.le_ceil |s.re|
        have := neg_le_abs s.re
        rw [← hk] at *; linarith
      calc ‖a n‖ * (n : ℝ) ^ (-s.re) ≤ (M * Real.exp (-(n : ℝ))) * (n : ℝ) ^ k :=
            mul_le_mul (hM n) h1 (by positivity) (by positivity)
        _ = M * ((n : ℝ) ^ k * Real.exp (-1 * n)) := by ring_nf
  -- `F` is the Dirichlet series off `s = 1`
  have hLa : AnalyticOnNhd ℂ (LSeries (fun n => a n)) Set.univ := by
    intro s _
    apply LSeries_analyticOnNhd
    simp only [Set.mem_ofPred_eq]
    have := LSeries.abscissaOfAbsConv_le_of_forall_lt_LSeriesSummable
      (f := fun n => a n) (x := s.re - 1) (fun y _ => hsumm y)
    calc LSeries.abscissaOfAbsConv (fun n => a n) ≤ ((s.re - 1 : ℝ) : EReal) := this
      _ < (s.re : EReal) := by exact_mod_cast (by linarith : s.re - 1 < s.re)
  have hFL : ∀ s : ℂ, s ≠ 1 → F s = LSeries (fun n => a n) s := by
    have hU : IsOpen ({1}ᶜ : Set ℂ) := isOpen_compl_singleton
    have hpc : IsPreconnected ({1}ᶜ : Set ℂ) :=
      (isConnected_compl_singleton_of_one_lt_rank (by simp) 1).isPreconnected
    have h3 : F =ᶠ[𝓝 (2 : ℂ)] LSeries (fun n => a n) := by
      filter_upwards [(isOpen_lt continuous_const Complex.continuous_re).mem_nhds
        (show (1 : ℝ) < (2 : ℂ).re by norm_num)] with s hs
      exact hF.1 s hs
    intro s hs
    exact (hF.2.analyticOnNhd hU).eqOn_of_preconnected_of_eventuallyEq
      (hLa.mono (Set.subset_univ _)) hpc (by simp : (2 : ℂ) ∈ ({1}ᶜ : Set ℂ)) h3 hs
  -- choice of `σ`
  set S2 : ℝ := ∑' n, ‖LSeries.term (fun n => a n) 2 n‖ with hS2
  obtain ⟨j, hj⟩ : ∃ j : ℕ, (1 / 2 : ℝ) ^ j * S2 ≤ 1 / 2 := by
    have h := (tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num : (0 : ℝ) ≤ 1 / 2)
      (by norm_num)).mul_const S2
    rw [zero_mul] at h
    obtain ⟨j, hj⟩ := (h.eventually (gt_mem_nhds (by norm_num : (0 : ℝ) < 1 / 2))).exists
    exact ⟨j, hj.le⟩
  set σ : ℝ := 2 + j with hσ
  have hσ2 : 2 ≤ σ := by rw [hσ]; have := Nat.cast_nonneg (α := ℝ) j; linarith
  -- lower bound on `Re s = σ`
  have hlow : ∀ t : ℝ, 1 / 2 ≤ ‖F ((σ : ℂ) + t * I)‖ := by
    intro t
    set s : ℂ := (σ : ℂ) + t * I with hs
    have hsre : s.re = σ := by simp [hs]
    have hs1 : s ≠ 1 := by intro h; rw [h] at hsre; simp at hsre; linarith
    rw [hFL s hs1]
    have hsum1 : Summable (fun n : ℕ => if n = 1 then (1 : ℂ) else 0) :=
      (hasSum_ite_eq 1 (1 : ℂ)).summable
    have hdiff : LSeries (fun n => a n) s - 1 =
        ∑' n : ℕ, (LSeries.term (fun n => a n) s n - if n = 1 then 1 else 0) := by
      rw [Summable.tsum_sub (hsumm s) hsum1, tsum_ite_eq, LSeries]
    have hb : ∀ n : ℕ, ‖LSeries.term (fun n => a n) s n - if n = 1 then 1 else 0‖ ≤
        (1 / 2 : ℝ) ^ j * ‖LSeries.term (fun n => a n) 2 n‖ := by
      intro n
      rcases Nat.lt_or_ge n 2 with hn | hn
      · interval_cases n
        · simp
        · simp [LSeries.term_of_ne_zero, ha1]
      · rw [ite_eq_right (by omega), sub_zero, LSeries.norm_term_eq, LSeries.norm_term_eq,
          ite_eq_right (by omega), ite_eq_right (by omega), hsre]
        have hn2 : (2 : ℝ) ≤ n := by exact_mod_cast hn
        have hn0 : (0 : ℝ) < n := by linarith
        rw [hσ, Real.rpow_add hn0, Real.rpow_natCast]
        simp only [Complex.re_ofNat]
        have h2j : (2 : ℝ) ^ j ≤ (n : ℝ) ^ j := pow_le_pow_left₀ (by norm_num) hn2 j
        have hpos : 0 < (n : ℝ) ^ (2 : ℝ) := by positivity
        rw [div_le_iff₀ (by positivity)]
        calc ‖a n‖ = (1 / 2) ^ j * (‖a n‖ / n ^ (2 : ℝ)) * (2 ^ j * n ^ (2 : ℝ)) := by
              field_simp
              rw [mul_assoc, ← mul_pow]; norm_num
          _ ≤ (1 / 2) ^ j * (‖a n‖ / n ^ (2 : ℝ)) * (n ^ (2 : ℝ) * n ^ j) := by
              rw [mul_comm ((2 : ℝ) ^ j)]
              gcongr
    have hle : ‖LSeries (fun n => a n) s - 1‖ ≤ 1 / 2 := by
      rw [hdiff]
      have hsb : Summable (fun n : ℕ => (1 / 2 : ℝ) ^ j * ‖LSeries.term (fun n => a n) 2 n‖) :=
        (hsumm 2).norm.mul_left _
      calc _ ≤ ∑' n : ℕ, ‖LSeries.term (fun n => a n) s n - if n = 1 then 1 else 0‖ :=
            norm_tsum_le_tsum_norm (hsb.of_nonneg_of_le (fun _ => norm_nonneg _) hb)
        _ ≤ ∑' n : ℕ, (1 / 2 : ℝ) ^ j * ‖LSeries.term (fun n => a n) 2 n‖ :=
            (hsb.of_nonneg_of_le (fun _ => norm_nonneg _) hb).tsum_le_tsum hb hsb
        _ = (1 / 2 : ℝ) ^ j * S2 := tsum_mul_left
        _ ≤ 1 / 2 := hj
    have h1 := norm_sub_norm_le (1 : ℂ) (LSeries (fun n => a n) s)
    rw [norm_one] at h1
    have h2 := norm_sub_rev (LSeries (fun n => a n) s) 1
    linarith
  -- upper bound on `Re s = 1 - σ`
  set K' : ℝ := ∑' n, ‖LSeries.term (fun n => a n) ((1 - σ : ℝ) : ℂ) n‖ with hK'
  have hK'0 : 0 ≤ K' := tsum_nonneg (fun _ => norm_nonneg _)
  have hup : ∀ t : ℝ, ‖F (((1 - σ : ℝ) : ℂ) + t * I)‖ ≤ K' := by
    intro t
    set s : ℂ := ((1 - σ : ℝ) : ℂ) + t * I with hs
    have hsre : s.re = 1 - σ := by simp [hs]
    have hs1 : s ≠ 1 := by intro h; rw [h] at hsre; simp at hsre; linarith
    rw [hFL s hs1, LSeries]
    refine (norm_tsum_le_tsum_norm (hsumm s).norm).trans (le_of_eq (tsum_congr (fun n => ?_)))
    rw [LSeries.norm_term_eq, LSeries.norm_term_eq, hsre]
    simp
  -- the functional equation in norms
  have hQ := D.Q_pos
  have hfeq : ∀ t : ℝ, D.Q ^ (2 * σ - 1) * (1 / 2) *
      ∏ i, (‖Complex.Gamma (D.α i * ((σ : ℂ) + t * I) + D.r i)‖ /
        ‖Complex.Gamma (D.α i * (((1 - σ : ℝ) : ℂ) + t * I) + D.r i)‖) ≤ K' := by
    intro t
    set s : ℂ := ((1 - σ : ℝ) : ℂ) + t * I with hs
    have hsre : s.re = 1 - σ := by simp [hs]
    have hs1 : s.re < 1 := by rw [hsre]; linarith
    have hs0 : s ≠ 0 := by intro h; rw [h] at hsre; simp at hsre; linarith
    have hc : 1 - starRingEnd ℂ s = (σ : ℂ) + t * I := by
      apply Complex.ext <;> simp [hs]
    have e := hfe s hs1 hs0
    rw [hc] at e
    have hn := congrArg norm e
    simp only [norm_mul, norm_prod, Complex.norm_conj, D.norm_w, one_mul, norm_inv,
      Complex.norm_cpow_eq_rpow_re_of_pos hQ] at hn
    have h1 : (-s).re = σ - 1 := by rw [Complex.neg_re, hsre]; ring
    have h2 : ((σ : ℂ) + t * I).re = σ := by simp
    rw [h1, h2] at hn
    have hQQ : D.Q ^ (σ - 1) * D.Q ^ σ = D.Q ^ (2 * σ - 1) := by
      rw [← Real.rpow_add hQ]; ring_nf
    have hprod : (∏ i, ‖Complex.Gamma (D.α i * s + D.r i)‖⁻¹) *
        (∏ i, ‖Complex.Gamma (D.α i * ((σ : ℂ) + t * I) + D.r i)‖) =
        ∏ i, (‖Complex.Gamma (D.α i * ((σ : ℂ) + t * I) + D.r i)‖ /
          ‖Complex.Gamma (D.α i * s + D.r i)‖) := by
      rw [← Finset.prod_mul_distrib]
      apply Finset.prod_congr rfl; intro i _; rw [div_eq_mul_inv, mul_comm]
    have hP0 : 0 ≤ ∏ i, (‖Complex.Gamma (D.α i * ((σ : ℂ) + t * I) + D.r i)‖ /
        ‖Complex.Gamma (D.α i * s + D.r i)‖) := Finset.prod_nonneg (fun i _ => by positivity)
    have hFs : ‖F s‖ = D.Q ^ (2 * σ - 1) *
        (∏ i, (‖Complex.Gamma (D.α i * ((σ : ℂ) + t * I) + D.r i)‖ /
          ‖Complex.Gamma (D.α i * s + D.r i)‖)) * ‖F ((σ : ℂ) + t * I)‖ := by
      rw [hn, ← hQQ, ← hprod]; ring
    have := hup t
    rw [← hs, hFs] at this
    calc D.Q ^ (2 * σ - 1) * (1 / 2) *
        ∏ i, (‖Complex.Gamma (D.α i * ((σ : ℂ) + t * I) + D.r i)‖ /
          ‖Complex.Gamma (D.α i * s + D.r i)‖)
        ≤ D.Q ^ (2 * σ - 1) * (∏ i, (‖Complex.Gamma (D.α i * ((σ : ℂ) + t * I) + D.r i)‖ /
          ‖Complex.Gamma (D.α i * s + D.r i)‖)) * ‖F ((σ : ℂ) + t * I)‖ := by
          rw [mul_right_comm]
          exact mul_le_mul_of_nonneg_left (hlow t) (by positivity)
      _ ≤ K' := this
  -- Stirling: each ratio grows like a positive power of `t`
  have hd0 : 0 < D.d := by
    rcases Nat.eq_zero_or_pos D.d with h | h
    · exfalso
      have : D.degree = 0 := by
        simp only [FunctionalEquation.degree]
        have : ∀ i : Fin D.d, False := fun i => by have := i.2; omega
        simp [Finset.univ_eq_empty_iff.2 ⟨fun i => this i⟩]
      linarith
    · exact h
  set i0 : Fin D.d := ⟨0, hd0⟩
  set B : ℝ := 2 * K' * D.Q ^ (1 - 2 * σ) + 1 with hB
  have hratio : ∀ i : Fin D.d, ∀ᶠ t : ℝ in atTop,
      1 ≤ ‖Complex.Gamma (D.α i * ((σ : ℂ) + t * I) + D.r i)‖ /
        ‖Complex.Gamma (D.α i * (((1 - σ : ℝ) : ℂ) + t * I) + D.r i)‖ ∧
      (i = i0 → B ≤ ‖Complex.Gamma (D.α i * ((σ : ℂ) + t * I) + D.r i)‖ /
        ‖Complex.Gamma (D.α i * (((1 - σ : ℝ) : ℂ) + t * I) + D.r i)‖) := by
    intro i
    have hα := D.α_pos i
    set x1 : ℝ := D.α i * σ + (D.r i).re with hx1
    set x2 : ℝ := D.α i * (1 - σ) + (D.r i).re with hx2
    have hy : Tendsto (fun t : ℝ => D.α i * t + (D.r i).im) atTop atTop :=
      tendsto_atTop_add_const_right _ _ (tendsto_id.const_mul_atTop hα)
    have he : 0 < x1 - x2 := by rw [hx1, hx2]; nlinarith
    have hpow : Tendsto (fun t : ℝ => (1 / 4) * (D.α i * t + (D.r i).im) ^ (x1 - x2)) atTop
        atTop := ((tendsto_rpow_atTop he).comp hy).const_mul_atTop (by norm_num)
    have hev := hy.eventually (eventually_norm_Gamma_div_ge x1 x2)
    filter_upwards [hev, hpow.eventually_ge_atTop (max 1 B)] with t ht1 ht2
    have e1 : D.α i * ((σ : ℂ) + t * I) + D.r i =
        (x1 : ℂ) + ((D.α i * t + (D.r i).im : ℝ) : ℂ) * I := by
      apply Complex.ext <;> simp [hx1]
    have e2 : D.α i * (((1 - σ : ℝ) : ℂ) + t * I) + D.r i =
        (x2 : ℂ) + ((D.α i * t + (D.r i).im : ℝ) : ℂ) * I := by
      apply Complex.ext <;> simp [hx2]
    rw [e1, e2]
    have hge := le_trans ht2 ht1
    exact ⟨le_trans (le_max_left _ _) hge, fun _ => le_trans (le_max_right _ _) hge⟩
  obtain ⟨t, ht⟩ := (eventually_all.2 hratio).exists
  have hprod : B ≤ ∏ i, (‖Complex.Gamma (D.α i * ((σ : ℂ) + t * I) + D.r i)‖ /
      ‖Complex.Gamma (D.α i * (((1 - σ : ℝ) : ℂ) + t * I) + D.r i)‖) := by
    rw [← Finset.mul_prod_erase _ _ (Finset.mem_univ i0)]
    have h1 : 1 ≤ ∏ i ∈ Finset.univ.erase i0,
        (‖Complex.Gamma (D.α i * ((σ : ℂ) + t * I) + D.r i)‖ /
          ‖Complex.Gamma (D.α i * (((1 - σ : ℝ) : ℂ) + t * I) + D.r i)‖) := by
      calc (1 : ℝ) = ∏ i ∈ Finset.univ.erase i0, (1 : ℝ) := by simp
        _ ≤ _ := Finset.prod_le_prod₀ (fun _ _ => zero_le_one) (fun i _ => (ht i).1)
    have h2 := (ht i0).2 rfl
    have hB1 : 0 ≤ B := by rw [hB]; positivity
    nlinarith
  have hfin := hfeq t
  have hQQ : D.Q ^ (2 * σ - 1) * D.Q ^ (1 - 2 * σ) = 1 := by
    rw [← Real.rpow_add hQ]; simp
  have hQp : 0 < D.Q ^ (2 * σ - 1) := by positivity
  have : D.Q ^ (2 * σ - 1) * (1 / 2) * B ≤ K' :=
    le_trans (mul_le_mul_of_nonneg_left hprod (by positivity)) hfin
  rw [hB] at this
  nlinarith

open Complex Filter Topology MeasureTheory in
/-- **Selberg's degree bound.** If `a ∈ 𝒮` has continuation `F` and `F` has a functional
equation `D` of positive degree, then `deg D ≥ 1`: there are no members of `𝒮` with degree in
`(0, 1)`. -/
theorem one_le_degree_of_pos (a : ArithmeticFunction ℂ) (ha : a ∈ selbergClass) (F : ℂ → ℂ)
    (hF : IsLSeriesContinuation a F) (D : FunctionalEquation F) (hpos : 0 < D.degree) :
    1 ≤ D.degree := by
  by_contra hlt
  push Not at hlt
  have ha' := ha
  obtain ⟨ha1, ⟨F₀, hF₀, ⟨m, G, β, hGd, hGo, hGF₀⟩, _⟩, _, hram⟩ := ha'
  -- `F` agrees with the function witnessed in `selbergClass`
  have hFF₀ : ∀ s, s ≠ 1 → F s = F₀ s := by
    have hU : IsOpen ({1}ᶜ : Set ℂ) := isOpen_compl_singleton
    have hpc : IsPreconnected ({1}ᶜ : Set ℂ) :=
      (isConnected_compl_singleton_of_one_lt_rank (by simp) 1).isPreconnected
    have h3 : F =ᶠ[𝓝 (2 : ℂ)] F₀ := by
      filter_upwards [(isOpen_lt continuous_const Complex.continuous_re).mem_nhds
        (show (1 : ℝ) < (2 : ℂ).re by norm_num)] with s hs
      rw [hF.1 s hs, hF₀.1 s hs]
    intro s hs
    exact (hF.2.analyticOnNhd hU).eqOn_of_preconnected_of_eventuallyEq
      (hF₀.2.analyticOnNhd hU) hpc (by simp : (2 : ℂ) ∈ ({1}ᶜ : Set ℂ)) h3 hs
  have hGF : ∀ s, s ≠ 1 → G s = (s - 1) ^ m * F s := fun s hs => by
    rw [hFF₀ s hs]; exact hGF₀ s hs
  -- the growth of `G`
  set k : ℝ := |β| + 1 with hk
  have hk0 : 0 ≤ k := by positivity
  obtain ⟨CG, hCG⟩ := (hGo (k - β) (by rw [hk]; have := le_abs_self β; linarith)).bound
  rw [← comap_norm_atTop, Filter.eventually_comap, Filter.eventually_atTop] at hCG
  obtain ⟨RG, hRG⟩ := hCG
  have hGg : ∀ s : ℂ, RG ≤ ‖s‖ → ‖G s‖ ≤ CG * Real.exp (‖s‖ ^ k) := by
    intro s hs
    have := hRG ‖s‖ hs s rfl
    rw [show β + (k - β) = k by ring, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)] at this
    exact this
  -- convergence of the Dirichlet series
  obtain ⟨C4, hC4⟩ := hram (1 / 4) (by norm_num)
  have hsumx : ∀ s : ℂ, 5 / 4 < s.re → LSeriesSummable (fun n => a n) s := fun s hs =>
    LSeriesSummable_of_le_const_mul_rpow hs ⟨C4, fun n _ => by
      have := hC4 n; convert this using 3; norm_num⟩
  have hsum : LSeriesSummable (fun n => a n) 2 := hsumx 2 (by norm_num)
  set K : ℝ := ∑' n, ‖LSeries.term (fun n => a n) (3 / 2 : ℂ) n‖ with hK
  have hKb : ∀ s : ℂ, 3 / 2 ≤ s.re → ‖F s‖ ≤ K := by
    intro s hs
    rw [hF.1 s (by linarith), LSeries]
    have h32 : Summable (fun n => ‖LSeries.term (fun n => a n) (3 / 2 : ℂ) n‖) :=
      (hsumx (3 / 2) (by norm_num)).norm
    have hle : ∀ n, ‖LSeries.term (fun n => a n) s n‖ ≤
        ‖LSeries.term (fun n => a n) (3 / 2 : ℂ) n‖ := by
      intro n
      rw [LSeries.norm_term_eq, LSeries.norm_term_eq]
      split_ifs with hn
      · exact le_rfl
      · have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast Nat.one_le_iff_ne_zero.2 hn
        apply div_le_div_of_nonneg_left (norm_nonneg _) (by positivity)
        apply Real.rpow_le_rpow_of_exponent_le hn1
        have : (3 / 2 : ℂ).re = 3 / 2 := by norm_num
        rw [this]; exact hs
    exact (norm_tsum_le_tsum_norm (h32.of_nonneg_of_le (fun _ => norm_nonneg _) hle)).trans
      ((h32.of_nonneg_of_le (fun _ => norm_nonneg _) hle).tsum_le_tsum hle h32)
  obtain ⟨Ca, hCa⟩ := hram 1 one_pos
  obtain ⟨Rw, c, hRw, hc, hexp⟩ := exists_expansion_of_degree_lt_one a F G m D hF.1 hF.2 hsum K hKb
      hGd hGF
    k CG RG hk0 hGg hlt
  obtain ⟨M, hM⟩ := exists_norm_coeff_le_exp_neg_of_degree_lt_one a Ca hCa Rw c hRw hc hexp
  exact degree_bound_of_coeff_decay a ha1 M hM F hF D hpos


end SelbergClass
