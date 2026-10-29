/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.NumberTheory.LSeries.RiemannXi
public import Mathlib.NumberTheory.ArithmeticFunction.VonMangoldt
public import Mathlib.Analysis.Analytic.Order
import MathlibExt.Analysis.Complex.RectangleResidue
import MathlibExt.Analysis.SpecialFunctions.Gamma.DigammaAsymptotics
import MathlibExt.NumberTheory.LSeries.RiemannXiLogDeriv
import MathlibExt.NumberTheory.LSeries.RiemannZetaLogDerivZeros
import MathlibExt.NumberTheory.LSeries.VerticalLine
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Analysis.SpecialFunctions.Gamma.Deriv
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.NumberTheory.LSeries.Dirichlet

/-!
# Landau's formula for the zeros of `ζ`

For an integer `n > 1`, the sums of `n^ρ` over the nontrivial zeros `ρ = β + iγ` of `ζ` with
`|γ| ≤ T`, counted with multiplicity, satisfy
`(1/T) ∑_{|γ| ≤ T} n^ρ → -Λ(n)/π` as `T → ∞`.

The proof integrates `ξ'/ξ(s) n^s` around the rectangle `[-1/2, 3/2] × [-T', T']` at a good height
`T'` near `T`. By the functional equation `ξ(1 - s) = ξ(s)` the left side is reflected onto the
line `Re s = 3/2`, where `ξ'/ξ = ζ'/ζ + 1/(s-1) - (log π)/2 + ψ(s/2+1)/2`. Integrating the
Dirichlet series of `ζ'/ζ` term by term against `n^s + n^{1-s}` isolates the term `2 T' Λ(n)`; the
Gamma-factor terms contribute `O(log T')`, and the horizontal sides `O(log² T')`.

## Main statements

* `tendsto_one_div_mul_tsum_natCast_cpow_zeros`: **Landau's formula**
  `(1/T) ∑_{|γ| ≤ T} n^ρ → -Λ(n)/π`.
-/

@[expose] public section

universe u

open Complex Filter Topology Set ArithmeticFunction RiemannXi

section Landau

/-! ### Integrals along a vertical segment -/

private lemma integral_inv_one_add (T : ℝ) (hT : 0 ≤ T) :
    ∫ t in (0 : ℝ)..T, (1 + t)⁻¹ = Real.log (1 + T) := by
  have hd : ∀ x ∈ Set.uIcc 0 T, HasDerivAt (fun t => Real.log (1 + t)) (1 + x)⁻¹ x := by
    intro x hx
    rw [Set.uIcc_of_le hT] at hx
    have := ((hasDerivAt_id x).const_add 1).log (by simp; linarith [hx.1])
    simpa [one_div] using this
  have hc : ContinuousOn (fun t : ℝ => (1 + t)⁻¹) (Set.uIcc 0 T) := by
    refine ContinuousOn.inv₀ (by fun_prop) fun x hx => ?_
    rw [Set.uIcc_of_le hT] at hx; linarith [hx.1]
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hd hc.intervalIntegrable]
  simp

/-- An integral over `[-T, T]` with majorant `K / (1 + |t|)` is at most `2 K log (1 + T)`. -/
private lemma norm_intervalIntegral_le_mul_log {f : ℝ → ℂ} {K T : ℝ} (hT : 0 ≤ T)
    (hf : IntervalIntegrable f MeasureTheory.volume (-T) T)
    (hb : ∀ t, ‖f t‖ ≤ K * (1 + |t|)⁻¹) :
    ‖∫ t in (-T)..T, f t‖ ≤ K * (2 * Real.log (1 + T)) := by
  have hint : IntervalIntegrable (fun t : ℝ => K * (1 + t)⁻¹) MeasureTheory.volume 0 T := by
    refine ContinuousOn.intervalIntegrable ?_
    refine continuousOn_const.mul (ContinuousOn.inv₀ (by fun_prop) fun x hx => ?_)
    rw [Set.uIcc_of_le hT] at hx; linarith [hx.1]
  have h1 : ‖∫ t in (0 : ℝ)..T, f t‖ ≤ K * Real.log (1 + T) := by
    rw [← integral_inv_one_add T hT, ← intervalIntegral.integral_const_mul]
    refine intervalIntegral.norm_integral_le_of_norm_le hT
      (Filter.Eventually.of_forall fun t ht => ?_) hint
    have := hb t; rwa [abs_of_pos ht.1] at this
  have h2 : ‖∫ t in (-T)..0, f t‖ ≤ K * Real.log (1 + T) := by
    have e : (∫ t in (-T)..0, f t) = ∫ t in (0 : ℝ)..T, f (-t) := by
      rw [intervalIntegral.integral_comp_neg]; simp
    rw [e, ← integral_inv_one_add T hT, ← intervalIntegral.integral_const_mul]
    refine intervalIntegral.norm_integral_le_of_norm_le hT
      (Filter.Eventually.of_forall fun t ht => ?_) hint
    have := hb (-t); rwa [abs_neg, abs_of_pos ht.1] at this
  have m0 : (0 : ℝ) ∈ Set.uIcc (-T) T := by
    rw [Set.mem_uIcc]; left; constructor <;> linarith
  have i1 : IntervalIntegrable f MeasureTheory.volume (-T) 0 :=
    hf.mono_set (Set.uIcc_subset_uIcc Set.left_mem_uIcc m0)
  have i2 : IntervalIntegrable f MeasureTheory.volume 0 T :=
    hf.mono_set (Set.uIcc_subset_uIcc m0 Set.right_mem_uIcc)
  rw [← intervalIntegral.integral_add_adjacent_intervals i1 i2]
  refine (norm_add_le _ _).trans ?_
  linarith

private lemma hasDerivAt_cexp_mul_div {c : ℂ} (hc : c ≠ 0) (x : ℝ) :
    HasDerivAt (fun y : ℝ => Complex.exp (c * y) / c) (Complex.exp (c * x)) x := by
  conv => congr
  rw [← mul_div_cancel_right₀ (Complex.exp (c * x)) hc]
  apply ((Complex.hasDerivAt_exp _).comp x _).div_const c
  simpa only [mul_one] using! ((hasDerivAt_id (x : ℂ)).const_mul _).comp_ofReal

private lemma norm_cexp_ofReal_mul_I_mul (b t : ℝ) : ‖Complex.exp ((b : ℂ) * I * t)‖ = 1 := by
  rw [Complex.norm_exp]; simp

private lemma norm_integral_cexp_ofReal_mul_I_mul_le {b : ℝ} (hb : b ≠ 0) (T : ℝ) :
    ‖∫ t in (-T)..T, Complex.exp ((b : ℂ) * I * t)‖ ≤ 2 / |b| := by
  have hc : (b : ℂ) * I ≠ 0 := mul_ne_zero (by exact_mod_cast hb) I_ne_zero
  rw [integral_exp_mul_complex hc, norm_div]
  have : ‖(b : ℂ) * I‖ = |b| := by simp
  rw [this]
  gcongr
  refine (norm_sub_le _ _).trans ?_
  rw [norm_cexp_ofReal_mul_I_mul, norm_cexp_ofReal_mul_I_mul]; norm_num

/-! ### The Gamma-factor terms on the line `Re s = 3/2` -/

private lemma norm_seven_fourths_add_le (t : ℝ) :
    (1 + |t|) / 4 ≤ ‖((7 / 4 : ℂ) + (t / 2 : ℂ) * I)‖ := by
  have h1 : (7 / 4 : ℝ) ≤ ‖((7 / 4 : ℂ) + (t / 2 : ℂ) * I)‖ := by
    have := Complex.abs_re_le_norm ((7 / 4 : ℂ) + (t / 2 : ℂ) * I)
    simp at this; norm_num at this ⊢; linarith
  have h2 : |t| / 2 ≤ ‖((7 / 4 : ℂ) + (t / 2 : ℂ) * I)‖ := by
    have := Complex.abs_im_le_norm ((7 / 4 : ℂ) + (t / 2 : ℂ) * I)
    simp [abs_div] at this; linarith
  linarith

private lemma seven_fourths_add_mem_slitPlane (t : ℝ) :
    ((7 / 4 : ℂ) + (t / 2 : ℂ) * I) ∈ slitPlane := by
  left; norm_num

private lemma hasDerivAt_seven_fourths_add (t : ℝ) :
    HasDerivAt (fun t : ℝ => (7 / 4 : ℂ) + (t / 2 : ℂ) * I) (I / 2) t := by
  have := ((((hasDerivAt_id t).ofReal_comp).div_const (2 : ℂ)).mul_const I).const_add (7 / 4 : ℂ)
  refine this.congr_deriv ?_
  simp; ring

/-- Integration by parts: `∫_{-T}^{T} e^{ibt} log (7/4 + it/2) dt = O(log T / |b|)`. -/
private lemma norm_integral_cexp_mul_log_le {b : ℝ} (hb : b ≠ 0) {T : ℝ} (hT : 0 ≤ T) :
    ‖∫ t in (-T)..T,
        Complex.exp ((b : ℂ) * I * t) * Complex.log ((7 / 4 : ℂ) + (t / 2 : ℂ) * I)‖
      ≤ 2 * (Real.log (2 + T) + Real.pi) / |b| + 4 * Real.log (1 + T) / |b| := by
  set c : ℂ := (b : ℂ) * I with hc_def
  have hc : c ≠ 0 := mul_ne_zero (by exact_mod_cast hb) I_ne_zero
  have hcn : ‖c‖ = |b| := by simp [c]
  set w : ℝ → ℂ := fun t => (7 / 4 : ℂ) + (t / 2 : ℂ) * I with hw
  have hw0 : ∀ t, w t ≠ 0 := fun t => slitPlane_ne_zero (seven_fourths_add_mem_slitPlane t)
  have hu : ∀ t ∈ Set.uIcc (-T) T,
      HasDerivAt (fun t => Complex.log (w t)) ((I / 2) / w t) t :=
    fun t _ => (hasDerivAt_seven_fourths_add t).clog_real (seven_fourths_add_mem_slitPlane t)
  have hv : ∀ t ∈ Set.uIcc (-T) T, HasDerivAt (fun y : ℝ => Complex.exp (c * y) / c)
      (Complex.exp (c * t)) t := fun t _ => hasDerivAt_cexp_mul_div hc t
  have hwc : Continuous w := by simp only [w]; fun_prop
  have hu'c : Continuous fun t => (I / 2) / w t := continuous_const.div hwc hw0
  have hibp := intervalIntegral.integral_mul_deriv_eq_deriv_mul hu hv
    (hu'c.intervalIntegrable _ _)
    ((by fun_prop : Continuous fun t : ℝ => Complex.exp (c * t)).intervalIntegrable _ _)
  have hcomm : (∫ t in (-T)..T, Complex.exp (c * t) * Complex.log (w t)) =
      ∫ t in (-T)..T, Complex.log (w t) * Complex.exp (c * t) := by
    congr 1; funext t; ring
  change ‖∫ t in (-T)..T, Complex.exp (c * t) * Complex.log (w t)‖ ≤ _
  rw [hcomm, hibp]
  have hlog : ∀ t, |t| ≤ T → ‖Complex.log (w t)‖ ≤ Real.log (2 + T) + Real.pi := by
    intro t ht
    have hn1 : 1 ≤ ‖w t‖ := by
      have h1 : (7 / 4 : ℝ) ≤ ‖w t‖ := by
        have := Complex.abs_re_le_norm (w t)
        simp [w] at this; norm_num at this ⊢; linarith
      linarith
    have hn2 : ‖w t‖ ≤ 2 + T := by
      calc ‖w t‖ ≤ |(w t).re| + |(w t).im| := Complex.norm_le_abs_re_add_abs_im _
        _ ≤ 2 + T := by
          simp only [w]; simp [abs_div]; norm_num
          linarith [abs_nonneg t]
    calc ‖Complex.log (w t)‖ ≤ |(Complex.log (w t)).re| + |(Complex.log (w t)).im| :=
          Complex.norm_le_abs_re_add_abs_im _
      _ ≤ _ := by
        rw [Complex.log_re, Complex.log_im, abs_of_nonneg (Real.log_nonneg hn1)]
        exact add_le_add (Real.log_le_log (by linarith) hn2) (Complex.abs_arg_le_pi _)
  have hvn : ∀ t : ℝ, ‖Complex.exp (c * t) / c‖ = 1 / |b| := by
    intro t; rw [norm_div, hcn, hc_def, norm_cexp_ofReal_mul_I_mul]
  have hT1 := hlog T (by rw [abs_of_nonneg hT])
  have hT2 := hlog (-T) (by rw [abs_neg, abs_of_nonneg hT])
  have hint : ‖∫ t in (-T)..T, (I / 2) / w t * (Complex.exp (c * t) / c)‖
      ≤ (2 / |b|) * (2 * Real.log (1 + T)) := by
    apply norm_intervalIntegral_le_mul_log hT
    · exact (hu'c.mul (by fun_prop)).intervalIntegrable _ _
    intro t
    rw [norm_mul, hvn, norm_div, norm_div, Complex.norm_I, Complex.norm_two]
    have h1 := norm_seven_fourths_add_le t
    have hs : 0 < 1 + |t| := by positivity
    have key : 1 / 2 / ‖w t‖ ≤ 2 * (1 + |t|)⁻¹ := by
      rw [div_div, inv_eq_one_div, mul_one_div, div_le_div_iff₀ (by nlinarith) hs]
      nlinarith
    calc 1 / 2 / ‖w t‖ * (1 / |b|) ≤ 2 * (1 + |t|)⁻¹ * (1 / |b|) := by gcongr
      _ = _ := by ring
  calc _ ≤ ‖Complex.log (w T) * (Complex.exp (c * T) / c)‖ +
        ‖Complex.log (w (-T)) * (Complex.exp (c * (-T : ℝ)) / c)‖ +
        ‖∫ t in (-T)..T, (I / 2) / w t * (Complex.exp (c * t) / c)‖ := by
        refine (norm_sub_le _ _).trans ?_; gcongr; exact norm_sub_le _ _
    _ ≤ (Real.log (2 + T) + Real.pi) * (1 / |b|) + (Real.log (2 + T) + Real.pi) * (1 / |b|)
        + (2 / |b|) * (2 * Real.log (1 + T)) := by
        rw [norm_mul, norm_mul, hvn, hvn]
        gcongr
    _ = _ := by ring

private lemma continuousAt_digamma_of_re_pos {w : ℂ} (hw : 0 < w.re) :
    ContinuousAt Complex.digamma w := by
  have hne : ∀ v : ℂ, 0 < v.re → ∀ m : ℕ, v ≠ -(m : ℂ) := by
    intro v hv m h
    have := congrArg Complex.re h; simp at this; linarith [(Nat.cast_nonneg m : (0 : ℝ) ≤ m)]
  have hA : AnalyticAt ℂ Complex.Gamma w := by
    rw [Complex.analyticAt_iff_eventually_differentiableAt]
    filter_upwards [(isOpen_lt continuous_const Complex.continuous_re).mem_nhds hw] with v hv
    exact Complex.differentiableAt_Gamma v (hne v hv)
  have h : Complex.digamma = fun v => deriv Complex.Gamma v / Complex.Gamma v := by
    funext v; rfl
  rw [h]
  exact hA.deriv.continuousAt.div hA.continuousAt (Complex.Gamma_ne_zero (hne w hw))

/-- The Gamma-factor term `1/(s-1) - (log π)/2 + ψ(s/2+1)/2` integrated against `e^{ibt}` on
`Re s = 3/2` is `O(log T)`. -/
private lemma exists_norm_integral_cexp_mul_gammaTerm_le {b : ℝ} (hb : b ≠ 0) :
    ∃ K : ℝ, ∀ T : ℝ, 0 ≤ T →
      ‖∫ t in (-T)..T, Complex.exp ((b : ℂ) * I * t) *
          (1 / (((3 / 2 : ℂ) + t * I) - 1) - (Real.log Real.pi : ℂ) / 2 +
            Complex.digamma (((3 / 2 : ℂ) + t * I) / 2 + 1) / 2)‖
        ≤ K * (1 + Real.log (1 + T) + Real.log (2 + T)) := by
  obtain ⟨Cψ, hCψ⟩ := Complex.exists_norm_digamma_sub_log_le (Real.pi / 2) (by positivity)
  set w : ℝ → ℂ := fun t => (7 / 4 : ℂ) + (t / 2 : ℂ) * I with hw
  have hwre : ∀ t, (w t).re = 7 / 4 := fun t => by simp [w]
  have hw0 : ∀ t, w t ≠ 0 := fun t => slitPlane_ne_zero (seven_fourths_add_mem_slitPlane t)
  have hwc : Continuous w := by simp only [w]; fun_prop
  have hsw : ∀ t : ℝ, ((3 / 2 : ℂ) + t * I) / 2 + 1 = w t := fun t => by simp only [w]; ring
  have hs1 : ∀ t : ℝ, ((3 / 2 : ℂ) + t * I) - 1 = (1 / 2 : ℂ) + t * I := fun t => by ring
  set e : ℝ → ℂ := fun t => Complex.exp ((b : ℂ) * I * t) with he
  have hec : Continuous e := by simp only [e]; fun_prop
  have hen : ∀ t, ‖e t‖ = 1 := fun t => norm_cexp_ofReal_mul_I_mul b t
  set E : ℝ → ℂ := fun t => Complex.digamma (w t) - Complex.log (w t) with hE
  have hψc : Continuous fun t => Complex.digamma (w t) :=
    continuous_iff_continuousAt.mpr fun t =>
      (continuousAt_digamma_of_re_pos (by rw [hwre]; norm_num)).comp hwc.continuousAt
  have hlogc : Continuous fun t => Complex.log (w t) :=
    continuous_iff_continuousAt.mpr fun t =>
      ContinuousAt.comp (f := w) (continuousAt_clog (seven_fourths_add_mem_slitPlane t))
        hwc.continuousAt
  have hEc : Continuous E := hψc.sub hlogc
  have hEb : ∀ t, ‖E t‖ ≤ (4 * |Cψ|) * (1 + |t|)⁻¹ := by
    intro t
    have harg : |Complex.arg (w t)| < Real.pi / 2 :=
      Complex.abs_arg_lt_pi_div_two_iff.mpr (Or.inl (by rw [hwre]; norm_num))
    have h := hCψ (w t) (hw0 t) (by linarith [(abs_lt.mp harg).1])
      (by linarith [(abs_lt.mp harg).2])
    have hn := norm_seven_fourths_add_le t
    have hs : 0 < 1 + |t| := by positivity
    calc ‖E t‖ ≤ Cψ / ‖w t‖ := h
      _ ≤ |Cψ| / ‖w t‖ := by gcongr; exact le_abs_self _
      _ ≤ |Cψ| / ((1 + |t|) / 4) := by gcongr
      _ = _ := by field_simp
  set q : ℝ → ℂ := fun t => (1 / 2 : ℂ) + t * I with hq
  have hq0 : ∀ t, q t ≠ 0 := fun t h => by
    have := congrArg Complex.re h; simp [q] at this
  have hqc : Continuous q := by simp only [q]; fun_prop
  have hqb : ∀ t, ‖1 / q t‖ ≤ 4 * (1 + |t|)⁻¹ := by
    intro t
    have h1 : (1 / 2 : ℝ) ≤ ‖q t‖ := by
      have := Complex.abs_re_le_norm (q t); simp [q] at this; linarith
    have h2 : |t| ≤ ‖q t‖ := by
      have := Complex.abs_im_le_norm (q t); simpa [q] using this
    have hs : 0 < 1 + |t| := by positivity
    rw [norm_div, norm_one, inv_eq_one_div, mul_one_div, div_le_div_iff₀ (by linarith) hs]
    linarith
  refine ⟨8 + 2 * (|Real.log Real.pi| * (1 / |b|)) + 4 * |Cψ| + (8 + 2 * Real.pi) * (1 / |b|),
    fun T hT => ?_⟩
  have hpt : ∀ t : ℝ, e t * (1 / (((3 / 2 : ℂ) + t * I) - 1) - (Real.log Real.pi : ℂ) / 2 +
      Complex.digamma (((3 / 2 : ℂ) + t * I) / 2 + 1) / 2) =
      e t * (1 / q t) - (Real.log Real.pi : ℂ) / 2 * e t + (1 / 2 : ℂ) * (e t * E t)
        + (1 / 2 : ℂ) * (e t * Complex.log (w t)) := by
    intro t; rw [hsw, hs1]; simp only [E, q]; ring
  change ‖∫ t in (-T)..T, e t * _‖ ≤ _
  simp_rw [hpt]
  have i1 : IntervalIntegrable (fun t => e t * (1 / q t)) MeasureTheory.volume (-T) T :=
    (hec.mul (continuous_const.div hqc hq0)).intervalIntegrable _ _
  have i2 : IntervalIntegrable (fun t => (Real.log Real.pi : ℂ) / 2 * e t)
      MeasureTheory.volume (-T) T :=
    (continuous_const.mul hec).intervalIntegrable _ _
  have i3 : IntervalIntegrable (fun t => (1 / 2 : ℂ) * (e t * E t))
      MeasureTheory.volume (-T) T :=
    (continuous_const.mul (hec.mul hEc)).intervalIntegrable _ _
  have i4 : IntervalIntegrable (fun t => (1 / 2 : ℂ) * (e t * Complex.log (w t)))
      MeasureTheory.volume (-T) T :=
    (continuous_const.mul (hec.mul hlogc)).intervalIntegrable _ _
  rw [intervalIntegral.integral_add ((i1.sub i2).add i3) i4,
    intervalIntegral.integral_add (i1.sub i2) i3, intervalIntegral.integral_sub i1 i2,
    intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul,
    intervalIntegral.integral_const_mul]
  have b1 : ‖∫ t in (-T)..T, e t * (1 / q t)‖ ≤ 4 * (2 * Real.log (1 + T)) :=
    norm_intervalIntegral_le_mul_log hT i1 fun t => by rw [norm_mul, hen, one_mul]; exact hqb t
  have b2 : ‖(Real.log Real.pi : ℂ) / 2 * ∫ t in (-T)..T, e t‖ ≤
      |Real.log Real.pi| / 2 * (2 / |b|) := by
    rw [norm_mul, norm_div, Complex.norm_real, Real.norm_eq_abs, Complex.norm_two]
    gcongr
    exact norm_integral_cexp_ofReal_mul_I_mul_le hb T
  have b3 : ‖(1 / 2 : ℂ) * ∫ t in (-T)..T, e t * E t‖ ≤
      1 / 2 * ((4 * |Cψ|) * (2 * Real.log (1 + T))) := by
    rw [norm_mul, show ‖(1 / 2 : ℂ)‖ = 1 / 2 by norm_num]
    gcongr
    exact norm_intervalIntegral_le_mul_log hT ((hec.mul hEc).intervalIntegrable _ _) fun t => by
      rw [norm_mul, hen, one_mul]; exact hEb t
  have b4 : ‖(1 / 2 : ℂ) * ∫ t in (-T)..T, e t * Complex.log (w t)‖ ≤
      1 / 2 * (2 * (Real.log (2 + T) + Real.pi) / |b| + 4 * Real.log (1 + T) / |b|) := by
    rw [norm_mul, show ‖(1 / 2 : ℂ)‖ = 1 / 2 by norm_num]
    gcongr
    exact norm_integral_cexp_mul_log_le hb hT
  have hl1 : 0 ≤ Real.log (1 + T) := Real.log_nonneg (by linarith)
  have hl2 : 0 ≤ Real.log (2 + T) := Real.log_nonneg (by linarith)
  have hpos2 : 0 ≤ 1 / |b| := by positivity
  calc _ ≤ ‖∫ t in (-T)..T, e t * (1 / q t)‖
        + ‖(Real.log Real.pi : ℂ) / 2 * ∫ t in (-T)..T, e t‖
        + ‖(1 / 2 : ℂ) * ∫ t in (-T)..T, e t * E t‖
        + ‖(1 / 2 : ℂ) * ∫ t in (-T)..T, e t * Complex.log (w t)‖ := by
        refine (norm_add_le _ _).trans ?_; gcongr
        refine (norm_add_le _ _).trans ?_; gcongr
        exact norm_sub_le _ _
    _ ≤ 4 * (2 * Real.log (1 + T)) + |Real.log Real.pi| / 2 * (2 / |b|)
        + 1 / 2 * ((4 * |Cψ|) * (2 * Real.log (1 + T)))
        + 1 / 2 * (2 * (Real.log (2 + T) + Real.pi) / |b| + 4 * Real.log (1 + T) / |b|) := by
        gcongr
    _ ≤ _ := by
        have e1 : |Real.log Real.pi| / 2 * (2 / |b|) = |Real.log Real.pi| * (1 / |b|) := by ring
        have e2 : 1 / 2 * (2 * (Real.log (2 + T) + Real.pi) / |b| + 4 * Real.log (1 + T) / |b|)
            = (1 / |b|) * Real.log (2 + T) + Real.pi * (1 / |b|)
              + 2 * (1 / |b|) * Real.log (1 + T) := by
          ring
        rw [e1, e2]
        have hC : 0 ≤ |Cψ| := abs_nonneg _
        have hL : 0 ≤ |Real.log Real.pi| := abs_nonneg _
        generalize 1 / |b| = u at hpos2 ⊢
        generalize Real.log (1 + T) = x at hl1 ⊢
        generalize Real.log (2 + T) = y at hl2 ⊢
        generalize |Real.log Real.pi| = L at hL ⊢
        generalize |Cψ| = C at hC ⊢
        have hp := Real.pi_pos.le
        generalize Real.pi = p at hp ⊢
        nlinarith [mul_nonneg hL hpos2, mul_nonneg (mul_nonneg hL hpos2) hl1,
          mul_nonneg (mul_nonneg hL hpos2) hl2, mul_nonneg hC hl1, mul_nonneg hC hl2,
          mul_nonneg hpos2 hl1, mul_nonneg hpos2 hl2, mul_nonneg hp hpos2,
          mul_nonneg (mul_nonneg hp hpos2) hl1, mul_nonneg (mul_nonneg hp hpos2) hl2]

/-! ### The Dirichlet series of `ζ'/ζ` on the line `Re s = 3/2` -/

private lemma one_div_add_one_le_abs_log_sub_log {n m : ℕ} (hn : 1 ≤ n) (hm : 1 ≤ m)
    (hmn : m ≠ n) : 1 / ((n : ℝ) + 1) ≤ |Real.log n - Real.log m| := by
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  have hm' : (0 : ℝ) < m := by exact_mod_cast hm
  have hp : 0 < 1 / ((n : ℝ) + 1) := by positivity
  rcases lt_or_gt_of_ne hmn with h | h
  · have hmn' : (m : ℝ) + 1 ≤ n := by exact_mod_cast h
    have h1 := Real.one_sub_inv_le_log_of_pos (div_pos hn' hm')
    rw [Real.log_div hn'.ne' hm'.ne', inv_div] at h1
    have h2 : 1 / ((n : ℝ) + 1) ≤ 1 - m / n := by
      have e : 1 - (m : ℝ) / n = (n - m) / n := by field_simp
      rw [e]
      calc 1 / ((n : ℝ) + 1) ≤ 1 / n := one_div_le_one_div_of_le hn' (by linarith)
        _ ≤ (n - m) / n := div_le_div_of_nonneg_right (by linarith) hn'.le
    rw [abs_of_nonneg (by linarith)]; linarith
  · have hnm' : (n : ℝ) + 1 ≤ m := by exact_mod_cast h
    have h1 := Real.one_sub_inv_le_log_of_pos (div_pos (by positivity : (0 : ℝ) < n + 1) hn')
    rw [Real.log_div (by positivity) hn'.ne', inv_div] at h1
    have h2 : 1 - (n : ℝ) / (n + 1) = 1 / (n + 1) := by field_simp; ring
    have h3 : Real.log ((n : ℝ) + 1) ≤ Real.log m := Real.log_le_log (by positivity) hnm'
    rw [abs_sub_comm, abs_of_nonneg (by linarith)]; linarith

/-- `(x : ℂ) ^ s = exp (log x * s)` for `x > 0`. -/
private lemma ofReal_cpow_eq_cexp {x : ℝ} (hx : 0 < x) (s : ℂ) :
    (x : ℂ) ^ s = Complex.exp ((Real.log x : ℂ) * s) := by
  rw [Complex.cpow_def_of_ne_zero (Complex.ofReal_ne_zero.mpr hx.ne'),
    Complex.ofReal_log hx.le]

/-- Integrating `-ζ'/ζ(3/2 + it)` against `n^{3/2+it} + n^{-1/2-it}` over `[-T, T]` gives
`2 T Λ(n) + O(1)`. -/
private lemma exists_norm_integral_LSeries_vonMangoldt_mul_sub_le {n : ℕ} (hn : 2 ≤ n) :
    ∃ K : ℝ, ∀ T : ℝ, 0 < T →
      ‖(∫ t in (-T)..T, LSeries (fun m => (Λ m : ℂ)) (((3 / 2 : ℝ) : ℂ) + t * I) *
          ((n : ℂ) ^ (((3 / 2 : ℝ) : ℂ) + t * I) + (n : ℂ) ^ ((-(1 / 2 : ℝ) : ℂ) - t * I)))
        - 2 * (T : ℂ) * (Λ n : ℂ)‖ ≤ K := by
  have hn0 : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
  set Ln : ℝ := Real.log n with hLn
  have hLn2 : Real.log 2 ≤ Ln := Real.log_le_log (by norm_num) (by exact_mod_cast hn)
  have hl2 : (1 / 2 : ℝ) ≤ Real.log 2 := by linarith [Real.log_two_gt_d9]
  set N : ℝ := Real.exp ((3 / 2) * Ln) with hN
  set D : ℝ := 2 * (n + 1) * N + 4 with hD
  have hsum : LSeriesSummable (fun m => (Λ m : ℂ)) (((3 / 2 : ℝ) : ℂ)) :=
    LSeriesSummable_vonMangoldt (by norm_num)
  set τ : ℕ → ℝ := fun m => ‖LSeries.term (fun m => (Λ m : ℂ)) (((3 / 2 : ℝ) : ℂ)) m‖ with hτ
  have hτs : Summable τ := summable_norm_iff.mpr hsum
  refine ⟨D * ∑' m, τ m, fun T hT => ?_⟩
  set Kf : ℝ → ℂ := fun t => (n : ℂ) ^ (((3 / 2 : ℝ) : ℂ) + t * I) +
    (n : ℂ) ^ ((-(1 / 2 : ℝ) : ℂ) - t * I) with hKf
  have hnC : (n : ℂ) = ((n : ℝ) : ℂ) := by norm_cast
  have hKe : ∀ t : ℝ, Kf t = Complex.exp ((Ln : ℂ) * (((3 / 2 : ℝ) : ℂ) + t * I)) +
      Complex.exp ((Ln : ℂ) * ((-(1 / 2 : ℝ) : ℂ) - t * I)) := by
    intro t; simp only [Kf]; rw [hnC, ofReal_cpow_eq_cexp hn0, ofReal_cpow_eq_cexp hn0]
  have hKc : Continuous Kf := by
    have : Kf = fun t : ℝ => Complex.exp ((Ln : ℂ) * (((3 / 2 : ℝ) : ℂ) + t * I)) +
      Complex.exp ((Ln : ℂ) * ((-(1 / 2 : ℝ) : ℂ) - t * I)) := funext hKe
    rw [this]; fun_prop
  have hKb : ∀ t, ‖Kf t‖ ≤ N + 1 := by
    intro t
    rw [hKe]
    refine (norm_add_le _ _).trans (add_le_add (le_of_eq ?_) ?_)
    · rw [Complex.norm_exp]; simp [N, mul_comm]
    · rw [Complex.norm_exp]; apply Real.exp_le_one_iff.mpr; simp; nlinarith
  have hS := hsum.hasSum_intervalIntegral_term_vertical_mul hKc hKb T
  set J : ℝ → ℂ := fun β => ∫ t in (-T)..T, Complex.exp ((β : ℂ) * I * t) with hJ
  have hJb : ∀ β : ℝ, β ≠ 0 → ‖J β‖ ≤ 2 / |β| :=
    fun β hβ => norm_integral_cexp_ofReal_mul_I_mul_le hβ T
  have hJ0 : J 0 = 2 * (T : ℂ) := by simp [J]; ring
  set α : ℕ → ℝ := fun m => (3 / 2) * (Ln - Real.log m) with hα
  set β : ℕ → ℝ := fun m => Ln - Real.log m with hβ
  set α' : ℕ → ℝ := fun m => -(1 / 2) * Ln - (3 / 2) * Real.log m with hα'
  set β' : ℕ → ℝ := fun m => -(Ln + Real.log m) with hβ'
  have hterm : ∀ m : ℕ, m ≠ 0 → ∀ t : ℝ,
      LSeries.term (fun m => (Λ m : ℂ)) (((3 / 2 : ℝ) : ℂ) + (t : ℂ) * I) m * Kf t =
        (Λ m : ℂ) * (Complex.exp (α m : ℂ) * Complex.exp ((β m : ℂ) * I * t) +
          Complex.exp (α' m : ℂ) * Complex.exp ((β' m : ℂ) * I * t)) := by
    intro m hm t
    have hm0 : (0 : ℝ) < m := by exact_mod_cast Nat.pos_of_ne_zero hm
    rw [LSeries.term_of_ne_zero hm, hKe, show (m : ℂ) = ((m : ℝ) : ℂ) by norm_cast,
      ofReal_cpow_eq_cexp hm0, div_eq_mul_inv, ← Complex.exp_neg, mul_assoc, mul_add,
      ← Complex.exp_add, ← Complex.exp_add, ← Complex.exp_add, ← Complex.exp_add]
    congr 2 <;> congr 1 <;> simp only [α, β, α', β'] <;> push_cast <;> ring
  have hec : ∀ γ : ℝ, Continuous fun t : ℝ => Complex.exp ((γ : ℂ) * I * t) := fun γ => by
    fun_prop
  have hint : ∀ m : ℕ, m ≠ 0 →
      (∫ t in (-T)..T,
          LSeries.term (fun m => (Λ m : ℂ)) (((3 / 2 : ℝ) : ℂ) + (t : ℂ) * I) m * Kf t)
        = (Λ m : ℂ) * (Complex.exp (α m : ℂ) * J (β m) +
          Complex.exp (α' m : ℂ) * J (β' m)) := by
    intro m hm
    have h1 : IntervalIntegrable
        (fun x : ℝ => Complex.exp (α m : ℂ) * Complex.exp ((β m : ℂ) * I * x))
        MeasureTheory.volume (-T) T := (continuous_const.mul (hec _)).intervalIntegrable _ _
    have h2 : IntervalIntegrable
        (fun x : ℝ => Complex.exp (α' m : ℂ) * Complex.exp ((β' m : ℂ) * I * x))
        MeasureTheory.volume (-T) T := (continuous_const.mul (hec _)).intervalIntegrable _ _
    rw [intervalIntegral.integral_congr (fun t _ => hterm m hm t),
      intervalIntegral.integral_const_mul, intervalIntegral.integral_add h1 h2,
      intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul]
  have hS' := hS.sub (hasSum_ite_eq n (2 * (T : ℂ) * (Λ n : ℂ)))
  have hτm : ∀ m : ℕ, m ≠ 0 → τ m = Λ m * Real.exp (-(3 / 2) * Real.log m) := by
    intro m hm
    have hm0 : (0 : ℝ) < m := by exact_mod_cast Nat.pos_of_ne_zero hm
    simp only [τ]
    rw [LSeries.norm_term_eq, ite_eq_right hm, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg vonMangoldt_nonneg, Complex.ofReal_re, Real.rpow_def_of_pos hm0,
      div_eq_mul_inv, ← Real.exp_neg]
    congr 2; ring
  have hbound : ∀ m : ℕ,
      ‖(∫ t in (-T)..T,
          LSeries.term (fun m => (Λ m : ℂ)) (((3 / 2 : ℝ) : ℂ) + (t : ℂ) * I) m * Kf t)
        - (if m = n then 2 * (T : ℂ) * (Λ n : ℂ) else 0)‖ ≤ D * τ m := by
    intro m
    rcases eq_or_ne m 0 with rfl | hm
    · simp [LSeries.term_zero, τ]; omega
    have hm1 : 1 ≤ m := Nat.one_le_iff_ne_zero.mpr hm
    set em : ℝ := Real.exp (-(3 / 2) * Real.log m) with hem
    have hem0 : 0 ≤ em := (Real.exp_pos _).le
    have hΛ0 : 0 ≤ Λ m := vonMangoldt_nonneg
    have hαe : Real.exp (α m) = N * em := by
      rw [hN, hem, ← Real.exp_add]; congr 1; simp only [α]; ring
    have hα'e : Real.exp (α' m) ≤ em := by
      rw [hem]; apply Real.exp_le_exp.mpr; simp only [α']
      have : 0 ≤ Ln := by linarith
      linarith
    have hβ'n : 1 / 2 ≤ |β' m| := by
      simp only [β']
      have : 0 ≤ Real.log m := Real.log_nonneg (by exact_mod_cast hm1)
      rw [abs_neg, abs_of_nonneg (by linarith)]; linarith
    have hJ' : ‖J (β' m)‖ ≤ 4 := by
      have hne : β' m ≠ 0 := fun h => by rw [h, abs_zero] at hβ'n; linarith
      refine (hJb _ hne).trans ?_
      rw [div_le_iff₀ (by linarith)]; linarith
    have hτ' := hτm m hm
    rw [hint m hm, hτ']
    have hN0 : 0 ≤ N := (Real.exp_pos _).le
    split_ifs with hmn
    · subst hmn
      have hb0 : β m = 0 := by simp [β, Ln]
      have ha0 : α m = 0 := by simp [α, Ln]
      rw [hb0, ha0, hJ0]
      have : (Λ m : ℂ) * (Complex.exp ((0 : ℝ) : ℂ) * (2 * (T : ℂ)) +
          Complex.exp (α' m : ℂ) * J (β' m)) - 2 * (T : ℂ) * (Λ m : ℂ) =
          (Λ m : ℂ) * (Complex.exp (α' m : ℂ) * J (β' m)) := by
        simp; ring
      rw [this, norm_mul, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hΛ0,
        Complex.norm_exp_ofReal]
      calc Λ m * (Real.exp (α' m) * ‖J (β' m)‖) ≤ Λ m * (em * 4) := by gcongr
        _ ≤ D * (Λ m * em) := by
          have : 4 ≤ D := by
            simp only [D]
            have := mul_nonneg (by positivity : (0 : ℝ) ≤ 2 * (m + 1)) hN0
            linarith
          nlinarith [mul_nonneg hΛ0 hem0]
    · rw [sub_zero, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hΛ0]
      have hsep := one_div_add_one_le_abs_log_sub_log (by omega) hm1 hmn
      have hβne : β m ≠ 0 := fun h => by
        simp only [β] at h; rw [h, abs_zero] at hsep
        have : 0 < 1 / ((n : ℝ) + 1) := by positivity
        linarith
      have hJβ : ‖J (β m)‖ ≤ 2 * (n + 1) := by
        refine (hJb _ hβne).trans ?_
        rw [div_le_iff₀ (abs_pos.mpr hβne)]
        have := mul_le_mul_of_nonneg_left hsep (by positivity : (0 : ℝ) ≤ 2 * (n + 1))
        rw [show 2 * ((n : ℝ) + 1) * (1 / ((n : ℝ) + 1)) = 2 by field_simp] at this
        simpa [β] using this
      calc Λ m * ‖Complex.exp (α m : ℂ) * J (β m) + Complex.exp (α' m : ℂ) * J (β' m)‖
          ≤ Λ m * (Real.exp (α m) * ‖J (β m)‖ + Real.exp (α' m) * ‖J (β' m)‖) := by
            gcongr
            refine (norm_add_le _ _).trans ?_
            rw [norm_mul, norm_mul, Complex.norm_exp_ofReal, Complex.norm_exp_ofReal]
        _ ≤ Λ m * (N * em * (2 * (n + 1)) + em * 4) := by
            rw [hαe]; gcongr
        _ = D * (Λ m * em) := by simp only [D]; ring
  exact hS'.norm_le_of_bounded (hτs.hasSum.mul_left D) hbound

/-! ### The logarithmic derivative of `ξ` -/

private lemma riemannXi_ne_zero_and_deriv_div_eq {s : ℂ} (hs1 : s ≠ 1)
    (hs : riemannZeta s ≠ 0) :
    riemannXi s ≠ 0 ∧ deriv riemannXi s / riemannXi s = deriv riemannZeta s / riemannZeta s +
      (1 / (s - 1) - (Real.log Real.pi : ℂ) / 2 + Complex.digamma (s / 2 + 1) / 2) := by
  refine ⟨riemannXi_ne_zero_of_riemannZeta_ne_zero hs1 hs, ?_⟩
  rw [← logDeriv_apply, ← logDeriv_apply]
  exact logDeriv_riemannXi_eq hs1 hs

/-! ### The residue theorem for `ξ'/ξ(s) x^s` -/

/-- The boundary integral of `ξ'/ξ(s) x^s` over `[-1/2, 3/2] × [-R, R]` is `2πi ∑_{|γ| < R} x^ρ`,
the sum over the nontrivial zeros counted with multiplicity. -/
private lemma boundaryIntegral_logDeriv_riemannXi_mul_cpow {ι : Type*} (z : ι → ℂ)
    (hz : ∀ w, ENat.card {n // z n = w} = analyticOrderAt riemannXi w)
    (x : ℝ) (hx : 0 < x) (R : ℝ) (hR : 0 < R)
    (hRz : ∀ ρ ∈ riemannZetaNontrivialZeros, |ρ.im| ≠ R) :
    (RectilinearRectangle.ofBounds (-1 / 2) (3 / 2) (-R) R).boundaryIntegral
        (fun s => deriv riemannXi s / riemannXi s * (x : ℂ) ^ s) =
      2 * (Real.pi : ℂ) * I * ∑' n, (if |(z n).im| < R then (x : ℂ) ^ z n else 0) := by
  classical
  set F : ℂ → ℂ := fun s => deriv riemannXi s / riemannXi s * (x : ℂ) ^ s with hF
  have hx0 : (x : ℂ) ≠ 0 := by exact_mod_cast hx.ne'
  have hmem_of := mem_riemannZetaNontrivialZeros_of_card_eq_analyticOrderAt hz
  have hNfin := finite_setOf_abs_im_lt_of_card_eq_analyticOrderAt hz R
  set NF := hNfin.toFinset with hNF
  set Z : Finset ℂ := NF.image z with hZ
  have hZmem : ∀ p, p ∈ Z ↔ p ∈ riemannZetaNontrivialZeros ∧ |p.im| < R := by
    intro p; constructor
    · intro hp
      obtain ⟨n, hn, rfl⟩ := Finset.mem_image.mp hp
      exact ⟨hmem_of n, by simpa [NF] using hn⟩
    · rintro ⟨hp, hpR⟩
      obtain ⟨n, hn⟩ := exists_eq_of_card_eq_analyticOrderAt hz hp
      exact Finset.mem_image.mpr ⟨n, by simp [NF, hn, hpR], hn⟩
  have hZprop : ∀ p ∈ Z, 0 ≤ p.re ∧ p.re ≤ 1 ∧ |p.im| < R := by
    intro p hp
    obtain ⟨hnt, hpR⟩ := (hZmem p).mp hp
    exact ⟨hnt.2.1, hnt.2.2, hpR⟩
  let mo : ℂ → ℕ := fun p => (analyticOrderAt riemannXi p).toNat
  let r : ℂ → ℂ := fun p => (mo p : ℂ) * (x : ℂ) ^ p
  have hcpowd : ∀ s : ℂ, DifferentiableAt ℂ (fun s : ℂ => (x : ℂ) ^ s) s :=
    fun s => differentiableAt_id.const_cpow (Or.inl hx0)
  have hloc : ∀ p ∈ Z, ∃ φ : ℂ → ℂ, DifferentiableAt ℂ φ p ∧
      ∀ᶠ s in 𝓝[≠] p, F s = r p / (s - p) + φ s := by
    intro p _
    have hm : analyticOrderAt riemannXi p = (mo p : ℕ) :=
      (ENat.natCast_toNat (analyticOrderAt_riemannXi_ne_top p)).symm
    obtain ⟨ξ₁, hξ₁a, hξ₁0, hξ₁e⟩ :=
      (differentiable_riemannXi.analyticAt p).analyticOrderAt_eq_natCast.mp hm
    have hξloc : ∀ᶠ s in 𝓝[≠] p, riemannXi s = (s - p) ^ ((mo p : ℕ) : ℤ) * ξ₁ s := by
      filter_upwards [nhdsWithin_le_nhds hξ₁e] with s hs
      rw [hs, zpow_natCast, smul_eq_mul]
    have hL := Complex.eventually_logDeriv_eq_of_eq_zpow_mul hξ₁a hξ₁0 hξloc
    have hH : AnalyticAt ℂ (fun s : ℂ => (x : ℂ) ^ s) p := by
      rw [Complex.analyticAt_iff_eventually_differentiableAt]
      exact Eventually.of_forall hcpowd
    have hΨ : DifferentiableAt ℂ (fun s => deriv ξ₁ s / ξ₁ s * (x : ℂ) ^ s) p :=
      (hξ₁a.deriv.differentiableAt.div hξ₁a.differentiableAt hξ₁0).mul (hcpowd p)
    obtain ⟨φ, hφ, hφe⟩ := Complex.exists_eventually_eq_div_sub_add_of_analyticAt
      (c := (mo p : ℂ)) hH hΨ (F := F) (by
        filter_upwards [hL] with s hs
        simp only [F]
        rw [← logDeriv_apply, hs, logDeriv_apply]
        push_cast
        ring)
    exact ⟨φ, hφ, hφe⟩
  set rect := RectilinearRectangle.ofBounds (-1 / 2) (3 / 2) (-R) R with hrect
  have hKre : ∀ s ∈ rect.carrier, -1 / 2 ≤ s.re ∧ s.re ≤ 3 / 2 ∧ -R ≤ s.im ∧ s.im ≤ R := by
    intro s hs
    obtain ⟨h1, h2⟩ := Complex.mem_reProdIm.mp hs
    simp only [rect, RectilinearRectangle.ofBounds_first_re,
      RectilinearRectangle.ofBounds_second_re, RectilinearRectangle.ofBounds_first_im,
      RectilinearRectangle.ofBounds_second_im] at h1 h2
    rw [Set.uIcc_of_le (by norm_num)] at h1
    rw [Set.uIcc_of_le (by linarith)] at h2
    exact ⟨h1.1, h1.2, h2.1, h2.2⟩
  have hdiff : ∀ s ∈ rect.carrier, s ∉ Z → DifferentiableAt ℂ F s := by
    intro s hsK hsZ
    obtain ⟨-, -, k3, k4⟩ := hKre s hsK
    have hξs : riemannXi s ≠ 0 := by
      intro h0
      have hnt := (riemannXi_eq_zero_iff s).mp h0
      have hIm : |s.im| < R := lt_of_le_of_ne (abs_le.mpr ⟨k3, k4⟩) (hRz s hnt)
      exact hsZ ((hZmem s).mpr ⟨hnt, hIm⟩)
    exact (((differentiable_riemannXi.analyticAt s).deriv.differentiableAt).div
      (differentiable_riemannXi s) hξs).mul (hcpowd s)
  obtain ⟨g, hg, hfg⟩ := Complex.exists_differentiableOn_eq_add_sum_div_sub _ Z r F hloc
    fun s hs hsS => (hdiff s hs hsS).differentiableWithinAt
  have hin : ∀ p ∈ Z, rect.first.re < p.re ∧ p.re < rect.second.re ∧ rect.first.im < p.im ∧
      p.im < rect.second.im := by
    intro p hp
    simp only [rect, RectilinearRectangle.ofBounds_first_re,
      RectilinearRectangle.ofBounds_second_re, RectilinearRectangle.ofBounds_first_im,
      RectilinearRectangle.ofBounds_second_im]
    obtain ⟨h1, h2, h3⟩ := hZprop p hp
    exact ⟨by linarith, by linarith, (abs_lt.mp h3).1, (abs_lt.mp h3).2⟩
  have hRS := rect.boundaryIntegral_eq_two_pi_mul_I_mul_sum Z r F g hin hg hfg
  have hcard : ∀ p ∈ Z, (NF.filter (fun n => z n = p)).card = mo p := by
    intro p hp
    have hpR := (hZprop p hp).2.2
    have := finite_of_card_eq_analyticOrderAt hz p
    have h := hz p
    rw [ENat.card_eq_coe_natCard, Nat.subtype_card (NF.filter (fun n => z n = p)) (by
      intro n
      simp only [NF, Finset.mem_filter, Set.Finite.mem_toFinset, mem_ofPred_eq]
      exact ⟨And.right, fun h => ⟨h ▸ hpR, h⟩⟩),
      ← ENat.natCast_toNat (analyticOrderAt_riemannXi_ne_top p)] at h
    exact_mod_cast h
  have htsum : ∑' n, (if |(z n).im| < R then (x : ℂ) ^ z n else 0) = ∑ p ∈ Z, r p := by
    rw [tsum_eq_sum (s := NF) (fun n hn => ite_eq_right (by simpa [NF] using hn))]
    rw [Finset.sum_congr rfl (fun n hn => ite_eq_left (by simpa [NF] using hn))]
    rw [Finset.sum_comp (fun p => (x : ℂ) ^ p) z]
    refine Finset.sum_congr rfl fun p hp => ?_
    rw [hcard p hp, nsmul_eq_mul]
  rw [htsum]
  exact hRS

/-! ### The vertical sides -/

/-- The vertical sides of the rectangle contribute `-2 i R Λ(n) + O(log R)`. -/
private lemma exists_norm_vertical_sides_sub_le {n : ℕ} (hn : 2 ≤ n) :
    ∃ C : ℝ, ∀ R : ℝ, 1 ≤ R →
      ‖(I • (∫ y : ℝ in (-R)..R,
          deriv riemannXi (((3 / 2 : ℝ) : ℂ) + (y : ℂ) * I) /
            riemannXi (((3 / 2 : ℝ) : ℂ) + (y : ℂ) * I) *
            ((n : ℝ) : ℂ) ^ (((3 / 2 : ℝ) : ℂ) + (y : ℂ) * I))
      - I • (∫ y : ℝ in (-R)..R,
          deriv riemannXi (((-1 / 2 : ℝ) : ℂ) + (y : ℂ) * I) /
            riemannXi (((-1 / 2 : ℝ) : ℂ) + (y : ℂ) * I) *
            ((n : ℝ) : ℂ) ^ (((-1 / 2 : ℝ) : ℂ) + (y : ℂ) * I)))
        - I * (-(2 * (R : ℂ) * (Λ n : ℂ)))‖ ≤ C * (1 + Real.log (1 + R) + Real.log (2 + R)) := by
  obtain ⟨K0, hK0⟩ := exists_norm_integral_LSeries_vonMangoldt_mul_sub_le hn
  have hn0 : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
  set Ln : ℝ := Real.log n with hLn
  have hLn0 : Ln ≠ 0 := (Real.log_pos (by exact_mod_cast (by omega : 1 < n))).ne'
  obtain ⟨K1, hK1⟩ := exists_norm_integral_cexp_mul_gammaTerm_le hLn0
  obtain ⟨K2, hK2⟩ := exists_norm_integral_cexp_mul_gammaTerm_le (neg_ne_zero.mpr hLn0)
  set N : ℝ := Real.exp ((3 / 2) * Ln) with hN
  set M : ℝ := Real.exp (-(1 / 2) * Ln) with hM
  have hN0 : 0 ≤ N := (Real.exp_pos _).le
  have hM0 : 0 ≤ M := (Real.exp_pos _).le
  refine ⟨|K0| + N * |K1| + M * |K2|, fun R hR => ?_⟩
  have hR0 : (0 : ℝ) ≤ R := by linarith
  set L : ℂ → ℂ := fun s => deriv riemannXi s / riemannXi s with hL
  set G : ℝ → ℂ := fun t => 1 / (((3 / 2 : ℂ) + t * I) - 1) - (Real.log Real.pi : ℂ) / 2 +
      Complex.digamma (((3 / 2 : ℂ) + t * I) / 2 + 1) / 2 with hG
  set Λs : ℝ → ℂ := fun t => LSeries (fun m => (Λ m : ℂ)) (((3 / 2 : ℝ) : ℂ) + t * I) with hΛs
  have hline : ∀ t : ℝ, (((3 / 2 : ℝ) : ℂ) + t * I) ≠ 1 ∧
      riemannZeta (((3 / 2 : ℝ) : ℂ) + t * I) ≠ 0 ∧ 1 < (((3 / 2 : ℝ) : ℂ) + t * I).re := by
    intro t
    have hre : (((3 / 2 : ℝ) : ℂ) + t * I).re = 3 / 2 := by simp
    refine ⟨fun h => ?_, riemannZeta_ne_zero_of_one_le_re (by rw [hre]; norm_num),
      by rw [hre]; norm_num⟩
    have := congrArg Complex.re h; rw [hre] at this; norm_num at this
  have hLdec : ∀ t : ℝ, L (((3 / 2 : ℝ) : ℂ) + t * I) = -Λs t + G t := by
    intro t
    obtain ⟨h1, h2, h3⟩ := hline t
    obtain ⟨-, hx⟩ := riemannXi_ne_zero_and_deriv_div_eq h1 h2
    simp only [L, Λs, G]
    rw [hx, LSeries_vonMangoldt_eq_deriv_riemannZeta_div h3]
    push_cast
    ring
  have hsum : LSeriesSummable (fun m => (Λ m : ℂ)) (((3 / 2 : ℝ) : ℂ)) :=
    LSeriesSummable_vonMangoldt (by norm_num)
  have hΛc : Continuous Λs := hsum.continuous_vertical
  have hLc : Continuous fun t : ℝ => L (((3 / 2 : ℝ) : ℂ) + t * I) := by
    refine continuous_iff_continuousAt.mpr fun t => ?_
    obtain ⟨h1, h2, -⟩ := hline t
    have hξ := (riemannXi_ne_zero_and_deriv_div_eq h1 h2).1
    have hc : Continuous fun t : ℝ => (((3 / 2 : ℝ) : ℂ) + t * I) := by fun_prop
    have hA := differentiable_riemannXi.analyticAt (((3 / 2 : ℝ) : ℂ) + t * I)
    exact ContinuousAt.comp (f := fun t : ℝ => (((3 / 2 : ℝ) : ℂ) + t * I))
      (hA.deriv.continuousAt.div hA.continuousAt hξ) hc.continuousAt
  have hGc : Continuous G := by
    have : G = fun t : ℝ => L (((3 / 2 : ℝ) : ℂ) + t * I) + Λs t := by
      funext t; rw [hLdec]; ring
    rw [this]; exact hLc.add hΛc
  have hK1e : ∀ t : ℝ, ((n : ℝ) : ℂ) ^ (((3 / 2 : ℝ) : ℂ) + t * I) =
      (N : ℂ) * Complex.exp ((Ln : ℂ) * I * t) := by
    intro t
    rw [ofReal_cpow_eq_cexp hn0, hN, Complex.ofReal_exp, ← Complex.exp_add]
    congr 1
    simp only [Complex.ofReal_mul, Complex.ofReal_div, Complex.ofReal_ofNat]
    ring
  have hK2e : ∀ t : ℝ, ((n : ℝ) : ℂ) ^ ((-(1 / 2 : ℝ) : ℂ) - t * I) =
      (M : ℂ) * Complex.exp (((-Ln : ℝ) : ℂ) * I * t) := by
    intro t
    rw [ofReal_cpow_eq_cexp hn0, hM, Complex.ofReal_exp, ← Complex.exp_add]
    congr 1
    simp only [Complex.ofReal_mul, Complex.ofReal_div, Complex.ofReal_ofNat, Complex.ofReal_neg,
      Complex.ofReal_one]
    ring
  -- the left side, reflected by the functional equation
  have hleft : ∀ y : ℝ, L (((-1 / 2 : ℝ) : ℂ) + y * I) =
      -L (((3 / 2 : ℝ) : ℂ) + ((-y : ℝ) : ℂ) * I) := by
    intro y
    have e : ((-1 / 2 : ℝ) : ℂ) + y * I = 1 - (((3 / 2 : ℝ) : ℂ) + ((-y : ℝ) : ℂ) * I) := by
      push_cast; ring
    simp only [L]
    rw [e, riemannXi_one_sub, deriv_riemannXi_one_sub, neg_div]
  have hcont1 : Continuous fun y : ℝ => L (((3 / 2 : ℝ) : ℂ) + y * I) *
      ((n : ℝ) : ℂ) ^ (((3 / 2 : ℝ) : ℂ) + (y : ℂ) * I) := by
    simp only [hK1e]; exact hLc.mul (by fun_prop)
  have hcont2 : Continuous fun y : ℝ => L (((3 / 2 : ℝ) : ℂ) + y * I) *
      ((n : ℝ) : ℂ) ^ ((-(1 / 2 : ℝ) : ℂ) - (y : ℂ) * I) := by
    simp only [hK2e]; exact hLc.mul (by fun_prop)
  have hA : (∫ y : ℝ in (-R)..R, L (((-1 / 2 : ℝ) : ℂ) + y * I) *
        ((n : ℝ) : ℂ) ^ (((-1 / 2 : ℝ) : ℂ) + (y : ℂ) * I)) =
      -∫ y : ℝ in (-R)..R, L (((3 / 2 : ℝ) : ℂ) + y * I) *
        ((n : ℝ) : ℂ) ^ ((-(1 / 2 : ℝ) : ℂ) - (y : ℂ) * I) := by
    rw [intervalIntegral.integral_congr (g := fun y : ℝ => -(fun y : ℝ =>
        L (((3 / 2 : ℝ) : ℂ) + y * I) * ((n : ℝ) : ℂ) ^ ((-(1 / 2 : ℝ) : ℂ) - (y : ℂ) * I)) (-y))
      (fun y _ => by simp only [hleft]; push_cast; ring_nf),
      intervalIntegral.integral_neg, intervalIntegral.integral_comp_neg (fun y : ℝ =>
        L (((3 / 2 : ℝ) : ℂ) + y * I) * ((n : ℝ) : ℂ) ^ ((-(1 / 2 : ℝ) : ℂ) - (y : ℂ) * I)),
      neg_neg]
  change ‖(I • (∫ y : ℝ in (-R)..R, L (((3 / 2 : ℝ) : ℂ) + y * I) *
        ((n : ℝ) : ℂ) ^ (((3 / 2 : ℝ) : ℂ) + (y : ℂ) * I)) - I • (∫ y : ℝ in (-R)..R,
        L (((-1 / 2 : ℝ) : ℂ) + y * I) * ((n : ℝ) : ℂ) ^ (((-1 / 2 : ℝ) : ℂ) + (y : ℂ) * I)))
      - I * (-(2 * (R : ℂ) * (Λ n : ℂ)))‖ ≤ _
  rw [hA]
  simp only [Complex.ofReal_natCast] at hK1e hK2e hcont1 hcont2 ⊢
  set e1 : ℝ → ℂ := fun t => Complex.exp ((Ln : ℂ) * I * t) with he1
  set e2 : ℝ → ℂ := fun t => Complex.exp (((-Ln : ℝ) : ℂ) * I * t) with he2
  have he1c : Continuous e1 := by simp only [e1]; fun_prop
  have he2c : Continuous e2 := by simp only [e2]; fun_prop
  set Kf : ℝ → ℂ := fun t => (n : ℂ) ^ (((3 / 2 : ℝ) : ℂ) + t * I) +
    (n : ℂ) ^ ((-(1 / 2 : ℝ) : ℂ) - t * I) with hKf
  have hKfc : Continuous Kf := by
    have : Kf = fun t => (N : ℂ) * e1 t + (M : ℂ) * e2 t := by
      funext t; simp only [Kf, hK1e, hK2e, e1, e2]
    rw [this]; fun_prop
  have hpt : ∀ t : ℝ, L (((3 / 2 : ℝ) : ℂ) + t * I) * (n : ℂ) ^ (((3 / 2 : ℝ) : ℂ) + (t : ℂ) * I) +
      L (((3 / 2 : ℝ) : ℂ) + t * I) * (n : ℂ) ^ ((-(1 / 2 : ℝ) : ℂ) - (t : ℂ) * I) =
      -(Λs t * Kf t) + (N : ℂ) * (e1 t * G t) + (M : ℂ) * (e2 t * G t) := by
    intro t
    simp only [Kf]
    rw [hLdec, hK1e, hK2e]
    ring
  have hAB : (∫ y : ℝ in (-R)..R, L (((3 / 2 : ℝ) : ℂ) + y * I) *
        (n : ℂ) ^ (((3 / 2 : ℝ) : ℂ) + (y : ℂ) * I)) +
      (∫ y : ℝ in (-R)..R, L (((3 / 2 : ℝ) : ℂ) + y * I) *
        (n : ℂ) ^ ((-(1 / 2 : ℝ) : ℂ) - (y : ℂ) * I)) =
      -(∫ t in (-R)..R, Λs t * Kf t) + (N : ℂ) * (∫ t in (-R)..R, e1 t * G t)
        + (M : ℂ) * (∫ t in (-R)..R, e2 t * G t) := by
    rw [← intervalIntegral.integral_add (hcont1.intervalIntegrable _ _)
      (hcont2.intervalIntegrable _ _)]
    simp_rw [hpt]
    have i1 : IntervalIntegrable (fun t => -(Λs t * Kf t)) MeasureTheory.volume (-R) R :=
      ((hΛc.mul hKfc).neg).intervalIntegrable _ _
    have i2 : IntervalIntegrable (fun t => (N : ℂ) * (e1 t * G t)) MeasureTheory.volume (-R) R :=
      (continuous_const.mul (he1c.mul hGc)).intervalIntegrable _ _
    have i3 : IntervalIntegrable (fun t => (M : ℂ) * (e2 t * G t)) MeasureTheory.volume (-R) R :=
      (continuous_const.mul (he2c.mul hGc)).intervalIntegrable _ _
    rw [intervalIntegral.integral_add (i1.add i2) i3, intervalIntegral.integral_add i1 i2,
      intervalIntegral.integral_neg, intervalIntegral.integral_const_mul,
      intervalIntegral.integral_const_mul]
  have hP := hK0 R (by linarith)
  have hQ1 := hK1 R hR0
  have hQ2 := hK2 R hR0
  set X := 1 + Real.log (1 + R) + Real.log (2 + R) with hX
  have hX1 : 1 ≤ X := by
    have h1 : 0 ≤ Real.log (1 + R) := Real.log_nonneg (by linarith)
    have h2 : 0 ≤ Real.log (2 + R) := Real.log_nonneg (by linarith)
    linarith
  have heq : (I • (∫ y : ℝ in (-R)..R, L (((3 / 2 : ℝ) : ℂ) + y * I) *
        (n : ℂ) ^ (((3 / 2 : ℝ) : ℂ) + (y : ℂ) * I)) -
      I • -(∫ y : ℝ in (-R)..R, L (((3 / 2 : ℝ) : ℂ) + y * I) *
        (n : ℂ) ^ ((-(1 / 2 : ℝ) : ℂ) - (y : ℂ) * I))) - I * (-(2 * (R : ℂ) * (Λ n : ℂ))) =
      I * (-((∫ t in (-R)..R, Λs t * Kf t) - 2 * (R : ℂ) * (Λ n : ℂ)) +
        (N : ℂ) * (∫ t in (-R)..R, e1 t * G t) + (M : ℂ) * (∫ t in (-R)..R, e2 t * G t)) := by
    rw [smul_eq_mul, smul_eq_mul]
    linear_combination I * hAB
  rw [heq, norm_mul, Complex.norm_I, one_mul]
  have hPf : ‖(∫ t in (-R)..R, Λs t * Kf t) - 2 * (R : ℂ) * (Λ n : ℂ)‖ ≤ K0 := hP
  calc _ ≤ ‖(∫ t in (-R)..R, Λs t * Kf t) - 2 * (R : ℂ) * (Λ n : ℂ)‖
        + N * ‖∫ t in (-R)..R, e1 t * G t‖ + M * ‖∫ t in (-R)..R, e2 t * G t‖ := by
        refine (norm_add_le _ _).trans ?_
        rw [norm_mul (M : ℂ), Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hM0]
        gcongr
        refine (norm_add_le _ _).trans ?_
        rw [norm_neg, norm_mul (N : ℂ), Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hN0]
    _ ≤ |K0| * X + N * (|K1| * X) + M * (|K2| * X) := by
        gcongr
        · exact hPf.trans ((le_abs_self K0).trans (le_mul_of_one_le_right (abs_nonneg _) hX1))
        · exact hQ1.trans (mul_le_mul_of_nonneg_right (le_abs_self _) (by linarith))
        · exact hQ2.trans (mul_le_mul_of_nonneg_right (le_abs_self _) (by linarith))
    _ = _ := by ring

/-! ### Good heights and the horizontal sides -/

/-- `‖ξ'/ξ(σ ± iT')‖ = O(log² T')` for `-1/2 ≤ σ ≤ 3/2` at a good height `T'` near `T`, in the
form used below (from `RiemannXi.exists_good_height_norm_logDeriv_riemannXi_le`). -/
private lemma exists_good_height_norm_deriv_div_riemannXi_le :
    ∃ A T₀ : ℝ, 2 ≤ T₀ ∧ ∀ T ≥ T₀, ∃ T' : ℝ, |T' - T| ≤ 1 ∧ 2 ≤ T' ∧
      (∀ ρ ∈ riemannZetaNontrivialZeros, |ρ.im| ≠ T') ∧
      ∀ σ : ℝ, -1 / 2 ≤ σ → σ ≤ 3 / 2 →
        ‖deriv riemannXi (σ + T' * I) / riemannXi (σ + T' * I)‖ ≤
          A * (1 + Real.log T' + Real.log T' ^ 2) ∧
        ‖deriv riemannXi (σ - T' * I) / riemannXi (σ - T' * I)‖ ≤
          A * (1 + Real.log T' + Real.log T' ^ 2) := by
  obtain ⟨K, T₁, -, hg⟩ := exists_good_height_norm_logDeriv_riemannXi_le (ε := 1 / 2)
    (by norm_num)
  refine ⟨|K|, max T₁ 2, le_max_right _ _, fun T hT => ?_⟩
  obtain ⟨T', hT'1, hT'2, hz', hb⟩ := hg T (le_trans (le_max_left _ _) hT)
  have hlog0 : 0 ≤ Real.log T' := Real.log_nonneg (by linarith)
  have hK : ∀ y : ℝ, y ≤ K * Real.log T' ^ 2 →
      y ≤ |K| * (1 + Real.log T' + Real.log T' ^ 2) := by
    intro y hy
    have h1 : K * Real.log T' ^ 2 ≤ |K| * Real.log T' ^ 2 :=
      mul_le_mul_of_nonneg_right (le_abs_self _) (sq_nonneg _)
    have h2 : |K| * Real.log T' ^ 2 ≤ |K| * (1 + Real.log T' + Real.log T' ^ 2) :=
      mul_le_mul_of_nonneg_left (by linarith) (abs_nonneg _)
    linarith
  refine ⟨T', hT'1, hT'2, hz', fun σ h1 h2 => ?_⟩
  obtain ⟨hp, hm⟩ := hb σ (by linarith) (by linarith)
  rw [logDeriv_apply] at hp hm
  exact ⟨hK _ hp, hK _ hm⟩

/-- Moving the height from `T` to `T'` with `|T' - T| ≤ 1` changes the zero sum by `O(log T)`. -/
private lemma exists_norm_tsum_le_sub_tsum_lt_le {ι : Type u} (z : ι → ℂ)
    (hz : ∀ w, ENat.card {n // z n = w} = analyticOrderAt riemannXi w) (n : ℕ) (hn : 2 ≤ n) :
    ∃ C : ℝ, ∀ T T' : ℝ, 2 ≤ T → |T' - T| ≤ 1 →
      ‖(∑' k, if |(z k).im| ≤ T then (n : ℂ) ^ z k else 0) -
          ∑' k, if |(z k).im| < T' then (n : ℂ) ^ z k else 0‖ ≤ C * Real.log T := by
  classical
  obtain ⟨C4, h74⟩ := exists_tsum_one_div_one_add_sq_sub_im_le_log.{u}
  refine ⟨n * (4 * |C4|), fun T T' hT hTT' => ?_⟩
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast (by omega : 1 ≤ n)
  set NF := (finite_setOf_abs_im_le_of_card_eq_analyticOrderAt hz (T + 1)).toFinset with hNF
  have hT'le : T' ≤ T + 1 := by rw [abs_le] at hTT'; linarith
  rw [tsum_eq_sum (s := NF) (fun k hk => ite_eq_right (by
      simp only [NF, Set.Finite.mem_toFinset, Set.mem_ofPred_eq] at hk; linarith)),
    tsum_eq_sum (s := NF) (fun k hk => ite_eq_right (by
      simp only [NF, Set.Finite.mem_toFinset, Set.mem_ofPred_eq] at hk; linarith)),
    ← Finset.sum_sub_distrib]
  set g : ι → ℝ := fun k => n * (2 * (1 / (1 + (T - (z k).im) ^ 2)) +
    2 * (1 / (1 + (T - (1 - z k).im) ^ 2))) with hg
  have hpt : ∀ k, ‖(if |(z k).im| ≤ T then (n : ℂ) ^ z k else 0) -
      (if |(z k).im| < T' then (n : ℂ) ^ z k else 0)‖ ≤ g k := by
    intro k
    have hρ := mem_riemannZetaNontrivialZeros_of_card_eq_analyticOrderAt hz k
    have hnorm : ‖(n : ℂ) ^ z k‖ ≤ n := by
      rw [Complex.norm_natCast_cpow_of_pos (by omega)]
      calc (n : ℝ) ^ (z k).re ≤ (n : ℝ) ^ (1 : ℝ) := Real.rpow_le_rpow_of_exponent_le hn1 hρ.2.2
        _ = n := Real.rpow_one _
    have key : ∀ x : ℝ, |T - x| ≤ 1 → 1 ≤ 2 * (1 / (1 + (T - x) ^ 2)) := by
      intro x hx
      have : (T - x) ^ 2 ≤ 1 := by
        have := sq_le_sq' (abs_le.mp hx).1 (abs_le.mp hx).2; simpa using this
      rw [mul_one_div, le_div_iff₀ (by positivity)]; linarith
    have hbetween : (|(z k).im| ≤ T ∧ ¬ |(z k).im| < T') ∨ (¬ |(z k).im| ≤ T ∧ |(z k).im| < T') →
        ‖(n : ℂ) ^ z k‖ ≤ g k := by
      intro h
      have hd : abs (T - |(z k).im|) ≤ 1 := by
        rw [abs_le] at hTT' ⊢
        rcases h with ⟨h1, h2⟩ | ⟨h1, h2⟩
        · rw [not_lt] at h2; constructor <;> linarith
        · rw [not_le] at h1; constructor <;> linarith
      have hg0 : 0 ≤ 2 * (1 / (1 + (T - (z k).im) ^ 2)) := by positivity
      have hg1 : 0 ≤ 2 * (1 / (1 + (T - (1 - z k).im) ^ 2)) := by positivity
      simp only [g]
      rcases le_or_gt 0 (z k).im with h0 | h0
      · rw [abs_of_nonneg h0] at hd
        have := key _ hd
        nlinarith
      · rw [abs_of_neg h0] at hd
        have hi : (1 - z k).im = -(z k).im := by simp
        have := key (1 - z k).im (by rw [hi]; exact hd)
        nlinarith
    split_ifs with h1 h2 h2
    · simp only [sub_self, norm_zero]; simp only [g]; positivity
    · rw [sub_zero]; exact hbetween (Or.inl ⟨h1, h2⟩)
    · rw [zero_sub, norm_neg]; exact hbetween (Or.inr ⟨h1, h2⟩)
    · simp only [sub_self, norm_zero]; simp only [g]; positivity
  have hsumF : ∀ y : ι → ℂ, (∀ w, ENat.card {n // y n = w} = analyticOrderAt riemannXi w) →
      ∑ k ∈ NF, 1 / (1 + (T - (y k).im) ^ 2) ≤ C4 * Real.log T := by
    intro y hy
    obtain ⟨hs, ht⟩ := h74 y hy T hT
    exact (hs.sum_le_tsum NF fun _ _ => by positivity).trans ht
  have hs1 := hsumF z hz
  have hs2 := hsumF (fun k => 1 - z k) (card_one_sub_eq_analyticOrderAt hz)
  have hlog : 0 ≤ Real.log T := Real.log_nonneg (by linarith)
  calc _ ≤ ∑ k ∈ NF, ‖(if |(z k).im| ≤ T then (n : ℂ) ^ z k else 0) -
        (if |(z k).im| < T' then (n : ℂ) ^ z k else 0)‖ := norm_sum_le _ _
    _ ≤ ∑ k ∈ NF, g k := Finset.sum_le_sum fun k _ => hpt k
    _ = n * (2 * ∑ k ∈ NF, 1 / (1 + (T - (z k).im) ^ 2) +
          2 * ∑ k ∈ NF, 1 / (1 + (T - (1 - z k).im) ^ 2)) := by
        simp only [g, ← Finset.mul_sum, Finset.sum_add_distrib]
    _ ≤ n * (2 * (C4 * Real.log T) + 2 * (C4 * Real.log T)) := by gcongr
    _ ≤ n * (4 * |C4|) * Real.log T := by
        have : C4 * Real.log T ≤ |C4| * Real.log T :=
          mul_le_mul_of_nonneg_right (le_abs_self _) hlog
        have hn0 : (0 : ℝ) ≤ n := by linarith
        nlinarith

private lemma norm_add_div_pi_le_of_eq {Hb Ht Va Vb S' Λc : ℂ} {T' : ℝ}
    (h : Hb - Ht + Va - Vb = 2 * (Real.pi : ℂ) * I * S') :
    ‖S' + (T' : ℂ) * Λc / (Real.pi : ℂ)‖ ≤
      ‖Hb‖ + ‖Ht‖ + ‖(Va - Vb) - I * (-(2 * (T' : ℂ) * Λc))‖ := by
  have hpi : (Real.pi : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  have e : S' + (T' : ℂ) * Λc / (Real.pi : ℂ) =
      (Hb - Ht + ((Va - Vb) - I * (-(2 * (T' : ℂ) * Λc)))) / (2 * (Real.pi : ℂ) * I) := by
    field_simp
    linear_combination (-(1 : ℂ)) * h
  rw [e, norm_div]
  have h2 : ‖2 * (Real.pi : ℂ) * I‖ = 2 * Real.pi := by
    rw [norm_mul, norm_mul, Complex.norm_I, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos Real.pi_pos]; simp
  rw [h2]
  have h6 : 1 ≤ 2 * Real.pi := by linarith [Real.pi_gt_three]
  rw [div_le_iff₀ (by linarith)]
  have hn : ‖Hb - Ht + ((Va - Vb) - I * (-(2 * (T' : ℂ) * Λc)))‖ ≤
      ‖Hb‖ + ‖Ht‖ + ‖(Va - Vb) - I * (-(2 * (T' : ℂ) * Λc))‖ :=
    (norm_add_le _ _).trans (add_le_add (norm_sub_le _ _) le_rfl)
  have h0 : 0 ≤ ‖Hb‖ + ‖Ht‖ + ‖(Va - Vb) - I * (-(2 * (T' : ℂ) * Λc))‖ := by positivity
  nlinarith

private lemma norm_horizontal_sides_le {n : ℕ} (hn1 : 1 ≤ n) {T' B : ℝ}
    (hL : ∀ σ : ℝ, -1 / 2 ≤ σ → σ ≤ 3 / 2 →
      ‖deriv riemannXi (σ + T' * I) / riemannXi (σ + T' * I)‖ ≤ B ∧
      ‖deriv riemannXi (σ - T' * I) / riemannXi (σ - T' * I)‖ ≤ B) :
    ‖∫ u : ℝ in (-1 / 2 : ℝ)..(3 / 2 : ℝ),
        deriv riemannXi ((u : ℂ) + ((-T' : ℝ) : ℂ) * I) /
          riemannXi ((u : ℂ) + ((-T' : ℝ) : ℂ) * I) *
          ((n : ℝ) : ℂ) ^ ((u : ℂ) + ((-T' : ℝ) : ℂ) * I)‖ ≤ (n : ℝ) ^ 2 * B * 2 ∧
    ‖∫ u : ℝ in (-1 / 2 : ℝ)..(3 / 2 : ℝ),
        deriv riemannXi ((u : ℂ) + (T' : ℂ) * I) / riemannXi ((u : ℂ) + (T' : ℂ) * I) *
          ((n : ℝ) : ℂ) ^ ((u : ℂ) + (T' : ℂ) * I)‖ ≤ (n : ℝ) ^ 2 * B * 2 := by
  have hn0 : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
  have hn1' : (1 : ℝ) ≤ n := by exact_mod_cast hn1
  have hcp : ∀ (u : ℝ) (v : ℝ), u ≤ 3 / 2 →
      ‖((n : ℝ) : ℂ) ^ ((u : ℂ) + (v : ℂ) * I)‖ ≤ (n : ℝ) ^ 2 := by
    intro u v hu
    rw [Complex.norm_cpow_eq_rpow_re_of_pos hn0]
    simp only [Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.ofReal_im,
      Complex.I_re, Complex.I_im, mul_zero, zero_mul, sub_zero, add_zero]
    rw [← Real.rpow_natCast]
    exact Real.rpow_le_rpow_of_exponent_le hn1' (by push_cast; linarith)
  have hab : |(3 / 2 : ℝ) - (-1 / 2)| = 2 := by norm_num
  constructor
  · have := intervalIntegral.norm_integral_le_of_norm_le_const (a := (-1 / 2 : ℝ)) (b := 3 / 2)
      (C := (n : ℝ) ^ 2 * B) (f := fun u : ℝ =>
        deriv riemannXi ((u : ℂ) + ((-T' : ℝ) : ℂ) * I) /
          riemannXi ((u : ℂ) + ((-T' : ℝ) : ℂ) * I) *
          ((n : ℝ) : ℂ) ^ ((u : ℂ) + ((-T' : ℝ) : ℂ) * I)) (fun u hu => by
        rw [Set.uIoc_of_le (by norm_num)] at hu
        have e : (u : ℂ) + ((-T' : ℝ) : ℂ) * I = (u : ℂ) - (T' : ℂ) * I := by push_cast; ring
        rw [norm_mul]
        have h1 := (hL u (by linarith [hu.1]) hu.2).2
        have h2 := hcp u (-T') hu.2
        rw [e] at h2 ⊢
        have hB : 0 ≤ B := (norm_nonneg _).trans h1
        rw [mul_comm ((n : ℝ) ^ 2)]
        exact mul_le_mul h1 h2 (norm_nonneg _) hB)
    rwa [hab] at this
  · have := intervalIntegral.norm_integral_le_of_norm_le_const (a := (-1 / 2 : ℝ)) (b := 3 / 2)
      (C := (n : ℝ) ^ 2 * B) (f := fun u : ℝ =>
        deriv riemannXi ((u : ℂ) + (T' : ℂ) * I) / riemannXi ((u : ℂ) + (T' : ℂ) * I) *
          ((n : ℝ) : ℂ) ^ ((u : ℂ) + (T' : ℂ) * I)) (fun u hu => by
        rw [Set.uIoc_of_le (by norm_num)] at hu
        rw [norm_mul]
        have h1 := (hL u (by linarith [hu.1]) hu.2).1
        have h2 := hcp u T' hu.2
        have hB : 0 ≤ B := (norm_nonneg _).trans h1
        rw [mul_comm ((n : ℝ) ^ 2)]
        exact mul_le_mul h1 h2 (norm_nonneg _) hB)
    rwa [hab] at this

private lemma norm_one_div_mul_sub_le {ST S' : ℂ} {T T' Λn Ct A Cv n2 : ℝ} (hT3 : 3 ≤ T)
    (hT'1 : |T' - T| ≤ 1) (hT'2 : 2 ≤ T') (hΛ0 : 0 ≤ Λn) (hn2 : 0 ≤ n2)
    (hS'b : ‖S' + (T' : ℂ) * (Λn : ℂ) / (Real.pi : ℂ)‖ ≤
      n2 * (A * (1 + Real.log T' + Real.log T' ^ 2)) * 2 +
        n2 * (A * (1 + Real.log T' + Real.log T' ^ 2)) * 2 +
        Cv * (1 + Real.log (1 + T') + Real.log (2 + T')))
    (htr : ‖ST - S'‖ ≤ Ct * Real.log T) :
    ‖(1 / (T : ℂ)) * ST - (-(Λn : ℂ) / (Real.pi : ℂ))‖ ≤
      (|Ct| + 4 * n2 * |A| + |Cv| + Λn) * (7 + 5 * Real.log T + Real.log T ^ 2) / T := by
  set Y : ℝ := 1 + Real.log T' + Real.log T' ^ 2 with hY
  set X : ℝ := 1 + Real.log (1 + T') + Real.log (2 + T') with hX
  set L : ℝ := Real.log T with hL'
  have hL0 : 0 ≤ L := Real.log_nonneg (by linarith)
  have hT'le : T' ≤ T + 1 := by rw [abs_le] at hT'1; linarith
  have hlog4 : Real.log 4 < 2 := by
    have : Real.log 4 = 2 * Real.log 2 := by
      rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]; norm_num
    rw [this]; linarith [Real.log_two_lt_d9]
  have hlog4T : Real.log (4 * T) ≤ 2 + L := by
    rw [Real.log_mul (by norm_num) (by linarith)]; linarith
  have hl1 : Real.log T' ≤ 2 + L :=
    (Real.log_le_log (by linarith) (by linarith)).trans hlog4T
  have hl2 : Real.log (1 + T') ≤ 2 + L :=
    (Real.log_le_log (by linarith) (by linarith)).trans hlog4T
  have hl3 : Real.log (2 + T') ≤ 2 + L :=
    (Real.log_le_log (by linarith) (by linarith)).trans hlog4T
  have hl1' : 0 ≤ Real.log T' := Real.log_nonneg (by linarith)
  have hl2' : 0 ≤ Real.log (1 + T') := Real.log_nonneg (by linarith)
  have hl3' : 0 ≤ Real.log (2 + T') := Real.log_nonneg (by linarith)
  have hYb : Y ≤ 7 + 5 * L + L ^ 2 := by
    have : Real.log T' ^ 2 ≤ (2 + L) ^ 2 := pow_le_pow_left₀ hl1' hl1 2
    simp only [Y]; nlinarith
  have hXb : X ≤ 7 + 5 * L + L ^ 2 := by simp only [X]; nlinarith
  have hY0 : 0 ≤ Y := by simp only [Y]; positivity
  have hX0 : 0 ≤ X := by simp only [X]; positivity
  clear_value Y X L
  have hS'b' : ‖S' + (T' : ℂ) * (Λn : ℂ) / (Real.pi : ℂ)‖ ≤
      (4 * n2 * |A| + |Cv|) * (7 + 5 * L + L ^ 2) := by
    refine hS'b.trans ?_
    have hAY : A * Y ≤ |A| * (7 + 5 * L + L ^ 2) :=
      (mul_le_mul_of_nonneg_right (le_abs_self A) hY0).trans
        (mul_le_mul_of_nonneg_left hYb (abs_nonneg A))
    have hCX : Cv * X ≤ |Cv| * (7 + 5 * L + L ^ 2) :=
      (mul_le_mul_of_nonneg_right (le_abs_self Cv) hX0).trans
        (mul_le_mul_of_nonneg_left hXb (abs_nonneg Cv))
    have h1' : n2 * (A * Y) ≤ n2 * (|A| * (7 + 5 * L + L ^ 2)) :=
      mul_le_mul_of_nonneg_left hAY hn2
    nlinarith
  have hSS : ‖ST - S'‖ ≤ |Ct| * L :=
    htr.trans (mul_le_mul_of_nonneg_right (le_abs_self _) hL0)
  have hTT : ‖((T : ℂ) - T') * (Λn : ℂ) / (Real.pi : ℂ)‖ ≤ Λn := by
    rw [norm_div, norm_mul, ← Complex.ofReal_sub, Complex.norm_real, Complex.norm_real,
      Complex.norm_real, Real.norm_eq_abs, Real.norm_eq_abs, Real.norm_eq_abs,
      abs_of_nonneg hΛ0, abs_of_pos Real.pi_pos, abs_sub_comm]
    rw [div_le_iff₀ Real.pi_pos]
    have := mul_le_mul_of_nonneg_right hT'1 hΛ0
    nlinarith [Real.pi_gt_three]
  have hT0 : (T : ℂ) ≠ 0 := by exact_mod_cast (by linarith : T ≠ 0)
  have hpi : (Real.pi : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  have e : (1 / (T : ℂ)) * ST - (-(Λn : ℂ) / (Real.pi : ℂ)) =
      (1 / (T : ℂ)) * ((ST - S') + (S' + (T' : ℂ) * (Λn : ℂ) / (Real.pi : ℂ)) +
        ((T : ℂ) - T') * (Λn : ℂ) / (Real.pi : ℂ)) := by
    field_simp; ring
  rw [e, norm_mul, norm_div, norm_one, Complex.norm_real, Real.norm_eq_abs,
    abs_of_pos (by linarith), one_div_mul_eq_div, div_le_div_iff_of_pos_right (by linarith)]
  calc _ ≤ ‖ST - S'‖ + ‖S' + (T' : ℂ) * (Λn : ℂ) / (Real.pi : ℂ)‖ +
        ‖((T : ℂ) - T') * (Λn : ℂ) / (Real.pi : ℂ)‖ :=
        (norm_add_le _ _).trans (add_le_add (norm_add_le _ _) le_rfl)
    _ ≤ |Ct| * L + (4 * n2 * |A| + |Cv|) * (7 + 5 * L + L ^ 2) + Λn := by gcongr
    _ ≤ _ := by
        have hC : 0 ≤ |Ct| := abs_nonneg _
        nlinarith [mul_nonneg hC hL0, mul_nonneg hC (sq_nonneg L), mul_nonneg hΛ0 hL0,
          mul_nonneg hΛ0 (sq_nonneg L)]

end Landau

/-- **Landau's formula.** For every integer `n > 1`,
`(1/T) ∑_{|γ| ≤ T} n^ρ → -Λ(n)/π` as `T → ∞`, the sum running over the nontrivial zeros
`ρ = β + iγ` of `ζ` counted with multiplicity (any family `z` listing the zeros of `ξ` with
multiplicity). Each truncated sum has finite support. -/
theorem tendsto_one_div_mul_tsum_natCast_cpow_zeros {ι : Type u} (z : ι → ℂ)
    (hz : ∀ w, ENat.card {k // z k = w} = analyticOrderAt riemannXi w) {n : ℕ} (hn : 1 < n) :
    Tendsto (fun T : ℝ => (1 / (T : ℂ)) *
        ∑' k, (if |(z k).im| ≤ T then (n : ℂ) ^ z k else 0)) atTop
      (𝓝 (-(Λ n : ℂ) / (Real.pi : ℂ))) := by
  have hn2 : 2 ≤ n := hn
  have hn1 : 1 ≤ n := by omega
  have hn0 : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
  obtain ⟨Cv, hCv⟩ := exists_norm_vertical_sides_sub_le hn2
  obtain ⟨A, T₀, -, hgood⟩ := exists_good_height_norm_deriv_div_riemannXi_le
  obtain ⟨Ct, hCt⟩ := exists_norm_tsum_le_sub_tsum_lt_le z hz n hn2
  have hΛ0 : 0 ≤ Λ n := vonMangoldt_nonneg
  have hmain : ∀ T : ℝ, max T₀ 3 ≤ T →
      ‖(1 / (T : ℂ)) * ∑' k, (if |(z k).im| ≤ T then (n : ℂ) ^ z k else 0) -
          (-(Λ n : ℂ) / (Real.pi : ℂ))‖ ≤
        (|Ct| + 4 * (n : ℝ) ^ 2 * |A| + |Cv| + Λ n) *
          (7 + 5 * Real.log T + Real.log T ^ 2) / T := by
    intro T hT
    have hT3 : 3 ≤ T := le_trans (le_max_right _ _) hT
    obtain ⟨T', hT'1, hT'2, hz', hL⟩ := hgood T (le_trans (le_max_left _ _) hT)
    have hres := boundaryIntegral_logDeriv_riemannXi_mul_cpow z hz (n : ℝ) hn0 T' (by linarith) hz'
    simp only [RectilinearRectangle.boundaryIntegral, RectilinearRectangle.ofBounds_first_re,
      RectilinearRectangle.ofBounds_second_re, RectilinearRectangle.ofBounds_first_im,
      RectilinearRectangle.ofBounds_second_im] at hres
    have hV := hCv T' (by linarith)
    have hH := norm_horizontal_sides_le hn1 hL
    have halg := norm_add_div_pi_le_of_eq (Λc := (Λ n : ℂ)) (T' := T') hres
    have hS'b := halg.trans (add_le_add (add_le_add hH.1 hH.2) hV)
    simp only [Complex.ofReal_natCast] at hS'b
    have htr := hCt T T' (by linarith) hT'1
    exact norm_one_div_mul_sub_le hT3 hT'1 hT'2 hΛ0 (by positivity) hS'b htr
  -- the bound tends to `0`
  have h0 := Real.tendsto_pow_log_div_mul_add_atTop 1 0 0 one_ne_zero
  have h1 := Real.tendsto_pow_log_div_mul_add_atTop 1 0 1 one_ne_zero
  have h2 := Real.tendsto_pow_log_div_mul_add_atTop 1 0 2 one_ne_zero
  simp only [pow_zero, pow_one, one_mul, add_zero] at h0 h1 h2
  set B : ℝ := |Ct| + 4 * (n : ℝ) ^ 2 * |A| + |Cv| + Λ n with hB
  have hlim : Tendsto (fun T : ℝ => B * (7 + 5 * Real.log T + Real.log T ^ 2) / T) atTop
      (𝓝 0) := by
    have := (((h0.const_mul 7).add (h1.const_mul 5)).add h2).const_mul B
    simp only [mul_zero, add_zero] at this
    refine this.congr' ?_
    filter_upwards [eventually_gt_atTop 0] with T hT
    field_simp
  rw [tendsto_iff_norm_sub_tendsto_zero]
  refine squeeze_zero' (Eventually.of_forall fun _ => norm_nonneg _) ?_ hlim
  filter_upwards [eventually_ge_atTop (max T₀ 3)] with T hT
  exact hmain T hT
