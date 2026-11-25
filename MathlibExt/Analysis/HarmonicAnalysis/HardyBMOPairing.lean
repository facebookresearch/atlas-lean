/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
public import Mathlib.MeasureTheory.Function.LocallyIntegrable
public import Mathlib.MeasureTheory.Integral.Average
public import Mathlib.MeasureTheory.Measure.Lebesgue.Basic

import Mathlib.Analysis.Calculus.ParametricIntegral
import Mathlib.Analysis.Calculus.TangentCone.DimOne
import Mathlib.Analysis.Complex.Liouville
import Mathlib.Analysis.SpecialFunctions.Complex.LogDeriv
import Mathlib.MeasureTheory.Integral.IntervalIntegral.AbsolutelyContinuousFun
import Mathlib.MeasureTheory.Integral.IntervalIntegral.LebesgueDifferentiationThm
import Mathlib.MeasureTheory.Integral.Lebesgue.Markov
import Mathlib.Probability.Distributions.Cauchy
import Mathlib.Topology.Algebra.MetricSpace.Lipschitz
import Mathlib.Topology.Connected.LocallyConnected
import Mathlib.Topology.Order.Separable

/-!
# Bounded mean oscillation on the real line

A locally integrable `f : ℝ → ℝ` has bounded mean oscillation with constant `B` when
`⨍_I |f - f_I| ≤ B` for every bounded interval `I = [a, b]`, `a < b`, where `f_I = ⨍_I f`.
The main theorem gives the one-dimensional case of the Hardy space pairing estimate.

The proof modifies a primitive of the test function over the superlevel sets of its
non-tangential Poisson maximal function. At successive levels, differences of the modified
primitives vanish at the endpoints of the component intervals. Their derivatives therefore have
zero integral on those intervals, allowing the pairing to be estimated by mean oscillation.
-/

open Complex Filter Function MeasureTheory Metric Set
open scoped Topology ENNReal NNReal

namespace MathlibExt.Analysis.HarmonicAnalysis.BoundedMeanOscillationWanted

-- The analytic Cauchy integral and its primitive.
private noncomputable def cauchy (f : ℝ → ℝ) (w : ℂ) : ℂ :=
  ∫ x : ℝ, (w - x)⁻¹ * (f x : ℂ)

private noncomputable def cauchyDeriv (f : ℝ → ℝ) (w : ℂ) : ℂ :=
  ∫ x : ℝ, (-(w - x)⁻¹ ^ 2) * (f x : ℂ)

private noncomputable def logPrimitive (f : ℝ → ℝ) (w : ℂ) : ℂ :=
  ∫ x : ℝ, Complex.log (w - x) * (f x : ℂ)

private theorem im_le_norm_sub_real (w : ℂ) (x : ℝ) : w.im ≤ ‖w - x‖ := by
  calc
    _ ≤ |(w - (x : ℂ)).im| := by simpa using le_abs_self w.im
    _ ≤ _ := abs_im_le_norm _

private theorem im_pos_of_mem_ball_half {w z : ℂ}
    (hz : z ∈ ball w (w.im / 2)) : w.im / 2 < z.im := by
  have him := abs_im_le_norm (z - w)
  rw [Complex.sub_im] at him
  rw [mem_ball, dist_eq_norm] at hz
  have := neg_abs_le (z.im - w.im)
  linarith

private theorem inv_sub_real_ne_zero {w : ℂ} (hw : 0 < w.im) (x : ℝ) :
    w - (x : ℂ) ≠ 0 := by
  exact norm_pos_iff.mp (hw.trans_le (im_le_norm_sub_real w x))

private theorem integrable_cauchyKernel {f : ℝ → ℝ} (hf : Integrable f) {w : ℂ}
    (hw : 0 < w.im) :
    Integrable (fun x : ℝ => (w - (x : ℂ))⁻¹ * (f x : ℂ)) := by
  apply (hf.norm.const_mul (w.im⁻¹)).mono'
    ((by fun_prop : Measurable (fun x : ℝ => (w - (x : ℂ))⁻¹)).aestronglyMeasurable.mul
      (Complex.continuous_ofReal.comp_aestronglyMeasurable hf.aestronglyMeasurable))
  refine ae_of_all _ fun x => ?_
  change ‖(w - (x : ℂ))⁻¹ * (f x : ℂ)‖ ≤ _
  rw [norm_mul, norm_inv, Complex.norm_real]
  exact mul_le_mul_of_nonneg_right
    (inv_anti₀ hw (im_le_norm_sub_real w x)) (norm_nonneg _)

private theorem hasDerivAt_cauchy {f : ℝ → ℝ} (hf : Integrable f) {w : ℂ}
    (hw : 0 < w.im) : HasDerivAt (cauchy f) (cauchyDeriv f w) w := by
  let r := w.im / 2
  have hr : 0 < r := by dsimp [r]; positivity
  refine (hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (F := fun z (x : ℝ) => (z - (x : ℂ))⁻¹ * (f x : ℂ))
    (F' := fun z (x : ℝ) => (-(z - (x : ℂ))⁻¹ ^ 2) * (f x : ℂ))
    (bound := fun x => r⁻¹ ^ 2 * ‖f x‖) (ball_mem_nhds w hr) ?_
    (integrable_cauchyKernel hf hw) ?_ ?_ (hf.norm.const_mul _) ?_).2
  · exact Filter.Eventually.of_forall fun z =>
      ((by fun_prop : Measurable (fun x : ℝ => (z - (x : ℂ))⁻¹)).aestronglyMeasurable.mul
        (Complex.continuous_ofReal.comp_aestronglyMeasurable hf.aestronglyMeasurable))
  · exact ((by fun_prop : Measurable (fun x : ℝ => -(w - (x : ℂ))⁻¹ ^ 2))).aestronglyMeasurable.mul
      (Complex.continuous_ofReal.comp_aestronglyMeasurable hf.aestronglyMeasurable)
  · refine ae_of_all _ fun x z hz => ?_
    rw [norm_mul, norm_neg, norm_pow, norm_inv, Complex.norm_real]
    gcongr
    exact (im_pos_of_mem_ball_half hz).le.trans (im_le_norm_sub_real z x)
  · refine ae_of_all _ fun x z hz => ?_
    have hzi := hr.trans (im_pos_of_mem_ball_half hz)
    have h := (((hasDerivAt_id z).sub_const (x : ℂ)).inv
      (inv_sub_real_ne_zero hzi x)).mul_const (f x : ℂ)
    simpa [inv_pow, div_eq_mul_inv] using h

private theorem hasDerivAt_logPrimitive {f : ℝ → ℝ} (hf : Integrable f)
    {w : ℂ} (hw : 0 < w.im)
    (hlog : Integrable (fun x : ℝ => Complex.log (w - x) * (f x : ℂ))) :
    HasDerivAt (logPrimitive f) (cauchy f w) w := by
  let r := w.im / 2
  have hr : 0 < r := by dsimp [r]; positivity
  refine (hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (F := fun z (x : ℝ) => Complex.log (z - (x : ℂ)) * (f x : ℂ))
    (F' := fun z (x : ℝ) => (z - (x : ℂ))⁻¹ * (f x : ℂ))
    (bound := fun x => r⁻¹ * ‖f x‖) (ball_mem_nhds w hr) ?_ hlog
    (integrable_cauchyKernel hf hw).aestronglyMeasurable ?_ (hf.norm.const_mul _) ?_).2
  · exact Filter.Eventually.of_forall fun z =>
      ((by fun_prop : Measurable (fun x : ℝ => Complex.log (z - (x : ℂ))))).aestronglyMeasurable.mul
          (Complex.continuous_ofReal.comp_aestronglyMeasurable hf.aestronglyMeasurable)
  · refine ae_of_all _ fun x z hz => ?_
    rw [norm_mul, norm_inv, Complex.norm_real]
    exact mul_le_mul_of_nonneg_right
      (inv_anti₀ hr ((im_pos_of_mem_ball_half hz).le.trans (im_le_norm_sub_real z x)))
        (norm_nonneg _)
  · refine ae_of_all _ fun x z hz => ?_
    have hzi : 0 < z.im := hr.trans (im_pos_of_mem_ball_half hz)
    have hs : z - (x : ℂ) ∈ slitPlane := by
      right
      simpa using hzi.ne'
    simpa [one_div] using (((hasDerivAt_id z).sub_const (x : ℂ)).clog hs).mul_const (f x : ℂ)

-- Poisson integrals and their maximal function.
private noncomputable def poissonValue (f : ℝ → ℝ) (t y : ℝ) :=
  ∫ z : ℝ, t / (Real.pi * (t ^ 2 + (y - z) ^ 2)) * f z

private noncomputable def poissonMax (f : ℝ → ℝ) (x : ℝ) : ℝ≥0∞ :=
  ⨆ t : ℝ, ⨆ (_ : 0 < t), ⨆ y : ℝ, ⨆ (_ : |y - x| < t), ‖poissonValue f t y‖ₑ

private theorem isOpen_poissonMax_gt (f : ℝ → ℝ) (a : ℝ≥0∞) :
    IsOpen {x | a < poissonMax f x} := by
  rw [show {x | a < poissonMax f x} =
      ⋃ (t : ℝ) (_ : 0 < t) (y : ℝ) (_ : a < ‖poissonValue f t y‖ₑ), ball y t by
    ext x
    simp [poissonMax, lt_iSup_iff, Real.dist_eq, abs_sub_comm x]
    grind]
  exact isOpen_iUnion fun _ => isOpen_iUnion fun _ => isOpen_iUnion fun _ =>
    isOpen_iUnion fun _ => isOpen_ball

private theorem measurable_poissonMax (f : ℝ → ℝ) : Measurable (poissonMax f) := by
  apply measurable_of_Ioi
  exact fun a => (isOpen_poissonMax_gt f a).measurableSet

private theorem poissonValue_le_max (f : ℝ → ℝ) {t y x : ℝ}
    (ht : 0 < t) (hxy : |y - x| < t) : ‖poissonValue f t y‖ₑ ≤ poissonMax f x :=
  le_iSup_of_le t (le_iSup_of_le ht
    (le_iSup_of_le y (le_iSup (fun _ : |y - x| < t => ‖poissonValue f t y‖ₑ) hxy)))

private theorem poissonValue_eq_im_cauchy {f : ℝ → ℝ} (hf : Integrable f)
    {w : ℂ} (hw : 0 < w.im) : poissonValue f w.im w.re = -(cauchy f w).im / Real.pi := by
  change (∫ x : ℝ, w.im / (Real.pi * (w.im ^ 2 + (w.re - x) ^ 2)) * f x) =
    -(Complex.imCLM (cauchy f w)) / Real.pi
  rw [cauchy, ← Complex.imCLM.integral_comp_comm (integrable_cauchyKernel hf hw),
    ← integral_neg, ← integral_div]
  refine integral_congr_ae (ae_of_all _ fun x => ?_)
  simp only [Complex.imCLM_apply, Complex.mul_im, Complex.ofReal_im, Complex.ofReal_re,
    mul_zero, zero_add, Complex.inv_im]
  change _ = -(-((w - (x : ℂ)).im) /
    ((w - (x : ℂ)).re * (w - (x : ℂ)).re + (w - (x : ℂ)).im * (w - (x : ℂ)).im) * f x) /
      Real.pi
  simp only [Complex.sub_im, Complex.ofReal_im, sub_zero, Complex.sub_re, Complex.ofReal_re,
    div_eq_mul_inv, mul_inv_rev]
  ring

private theorem cauchy_deriv_bound {f : ℝ → ℝ} (hf : Integrable f)
    {w : ℂ} {A : ℝ} (hw : 0 < w.im) (hA : 0 < A)
    (hbound : ∀ z ∈ closedBall w (w.im / 4), |(cauchy f z).im| ≤ A) :
    w.im * ‖cauchyDeriv f w‖ ≤ 4 * Real.exp 2 * A := by
  let r := w.im / 4
  have hr : 0 < r := by dsimp [r]; positivity
  let F := fun z => Complex.exp (Complex.I * (cauchy f z - cauchy f w) / (A : ℂ))
  have hF (z : ℂ) (hz : z ∈ closedBall w r) : HasDerivAt F
      (Complex.exp (Complex.I * (cauchy f z - cauchy f w) / (A : ℂ)) *
        (Complex.I * cauchyDeriv f z / (A : ℂ))) z := by
    have hi := im_pos_of_mem_ball_half
      (ball_subset_ball (by linarith) (show z ∈ ball w (w.im / 3) by
        rw [mem_ball]
        exact (mem_closedBall.mp hz).trans_lt (by dsimp [r]; linarith)))
    exact (((((hasDerivAt_cauchy (w := z) hf (by linarith)).sub_const (cauchy f w)).const_mul
      Complex.I).div_const (A : ℂ))).cexp
  have hdc : DiffContOnCl ℂ F (ball w r) := by
    apply DifferentiableOn.diffContOnCl
    simpa [closure_ball _ hr.ne'] using
      (show DifferentiableOn ℂ F (closedBall w r) from
        fun z hz => (hF z hz).differentiableAt.differentiableWithinAt)
  have hest := Complex.norm_deriv_le_of_forall_mem_sphere_norm_le hr hdc
    (C := Real.exp 2) (fun z hz => by
      have hz' := hbound z (sphere_subset_closedBall hz)
      have hw' := hbound w (mem_closedBall_self hr.le)
      have hre : (Complex.I * (cauchy f z - cauchy f w) / (A : ℂ)).re =
          ((cauchy f w).im - (cauchy f z).im) / A := by
        rw [Complex.div_ofReal_re, Complex.mul_re]
        simp
      rw [show F z = _ from rfl, Complex.norm_exp, hre, Real.exp_le_exp,
        div_le_iff₀ hA]
      linarith [le_abs_self (cauchy f w).im, neg_abs_le (cauchy f z).im])
  have hd := (hF w (mem_closedBall_self hr.le)).deriv
  simp only [sub_self, mul_zero, zero_div, Complex.exp_zero, one_mul] at hd
  rw [hd, norm_div, norm_mul, Complex.norm_I, one_mul, Complex.norm_real,
    Real.norm_eq_abs, abs_of_pos hA, div_le_div_iff₀ hA hr] at hest
  dsimp [r] at hest
  linarith

private theorem integrable_logKernel {f : ℝ → ℝ} (hf : Integrable f)
    (hs : HasCompactSupport f) {w : ℂ} (hw : 0 < w.im) :
    Integrable (fun x : ℝ => Complex.log (w - (x : ℂ)) * (f x : ℂ)) := by
  apply (integrableOn_iff_integrable_of_support_subset (s := tsupport f) ?_).mp
  · have hc : Continuous (fun x : ℝ => Complex.log (w - (x : ℂ))) := by
      rw [continuous_iff_continuousAt]
      intro x
      apply (continuousAt_clog (Or.inr ?_)).comp (by fun_prop)
      simpa using hw.ne'
    refine IntegrableOn.continuousOn_mul hc.continuousOn ?_ hs
    exact (Complex.ofRealCLM.integrable_comp hf).integrableOn
  · intro x hx
    by_contra hx'
    exact hx (by simp [image_eq_zero_of_notMem_tsupport hx'])

-- The correction by the height cancels the term involving the real part of the Cauchy
-- integral in the vertical derivative.
private noncomputable def smoothPrimitive (f : ℝ → ℝ) (w : ℂ) : ℝ :=
  (∫ x, f x) + (w.im * (cauchy f w).re - (logPrimitive f w).im) / Real.pi

private noncomputable def primitiveDeriv (f : ℝ → ℝ) (w : ℂ) : ℂ →L[ℝ] ℝ :=
  Real.pi⁻¹ •
    (w.im • Complex.reCLM.comp ((ContinuousLinearMap.mul ℂ ℂ
        (cauchyDeriv f w)).restrictScalars ℝ) - (cauchy f w).im • Complex.reCLM)

private theorem primitiveDeriv_apply (f : ℝ → ℝ) (w v : ℂ) :
    primitiveDeriv f w v =
      (w.im * (cauchyDeriv f w * v).re - (cauchy f w).im * v.re) / Real.pi := by
  simp [primitiveDeriv, div_eq_mul_inv, mul_comm]

private theorem hasFDerivAt_smoothPrimitive {f : ℝ → ℝ} (hf : Integrable f)
    (hs : HasCompactSupport f) {w : ℂ} (hw : 0 < w.im) :
    HasFDerivAt (smoothPrimitive f) (primitiveDeriv f w) w := by
  have hD := (hasDerivAt_cauchy hf hw).hasFDerivAt.restrictScalars ℝ
  have hP := (hasDerivAt_logPrimitive hf hw (integrable_logKernel hf hs hw)).hasFDerivAt
  have hPr := hP.restrictScalars ℝ
  have hr := Complex.reCLM.hasFDerivAt.comp w hD
  have hi := Complex.imCLM.hasFDerivAt.comp w hPr
  have h := (Complex.imCLM.hasFDerivAt.mul hr).sub hi
  have h' := ((hasFDerivAt_const (∫ x, f x) w).add (h.const_smul Real.pi⁻¹))
  rw [show smoothPrimitive f = (fun w => (∫ x, f x) + Real.pi⁻¹ •
    (w.im * (cauchy f w).re - (logPrimitive f w).im)) by
      ext w; simp [smoothPrimitive, div_eq_mul_inv, mul_comm]]
  convert h' using 1
  · rfl
  · ext v
    rw [primitiveDeriv_apply]
    simp only [zero_add]
    change _ = Real.pi⁻¹ * (w.im * (v * cauchyDeriv f w).re +
      (cauchy f w).re * v.im - (v * cauchy f w).im)
    simp only [Complex.mul_re, Complex.mul_im, div_eq_mul_inv]
    ring

private theorem im_cauchy_le {f : ℝ → ℝ} (hf : Integrable f)
    {L x : ℝ} (hx : poissonMax f x ≤ ENNReal.ofReal L) (hL : 0 < L) {z : ℂ}
    (hz : 0 < z.im) (hcone : |z.re - x| < z.im) :
    |(cauchy f z).im| ≤ Real.pi * L := by
  have h := (poissonValue_le_max f hz hcone).trans hx
  rw [poissonValue_eq_im_cauchy hf hz, Real.eNorm_eq_ofReal_abs,
    ENNReal.ofReal_le_ofReal_iff hL.le, abs_div, abs_neg, abs_of_pos Real.pi_pos,
    div_le_iff₀ Real.pi_pos] at h
  simpa [mul_comm] using h

private theorem primitiveDeriv_le {f : ℝ → ℝ} (hf : Integrable f)
    {L x : ℝ} (hL : 0 < L) (hx : poissonMax f x ≤ ENNReal.ofReal L) {w : ℂ}
    (hw : 0 < w.im) (hcone : |w.re - x| ≤ w.im / 4) :
    ‖primitiveDeriv f w‖ ≤ (1 + 4 * Real.exp 2) * L := by
  have hC (z : ℂ) (hz : z ∈ closedBall w (w.im / 4)) :
      |(cauchy f z).im| ≤ Real.pi * L := by
    have hz' : ‖z - w‖ ≤ w.im / 4 := by simpa [dist_eq_norm] using hz
    have hr := (abs_re_le_norm (z - w)).trans hz'
    have hi := (abs_im_le_norm (z - w)).trans hz'
    rw [Complex.sub_re] at hr
    rw [Complex.sub_im] at hi
    have hb := (abs_sub_le z.re w.re x).trans (add_le_add hr hcone)
    apply im_cauchy_le hf hx hL
    · linarith [neg_abs_le (z.im - w.im)]
    · linarith [neg_abs_le (z.im - w.im)]
  have hd := cauchy_deriv_bound hf hw (by positivity : 0 < Real.pi * L) hC
  have hi := hC w (mem_closedBall_self (by positivity))
  apply ContinuousLinearMap.opNorm_le_bound _ (by positivity)
  intro v
  rw [primitiveDeriv_apply, Real.norm_eq_abs, abs_div, abs_of_pos Real.pi_pos]
  apply (div_le_iff₀ Real.pi_pos).2
  calc
    _ ≤ w.im * |(cauchyDeriv f w * v).re| + |(cauchy f w).im| * |v.re| := by
      simpa [abs_mul, abs_of_pos hw] using
        abs_sub (w.im * (cauchyDeriv f w * v).re) ((cauchy f w).im * v.re)
    _ ≤ w.im * (‖cauchyDeriv f w‖ * ‖v‖) + (Real.pi * L) * ‖v‖ := by
      gcongr
      · exact (abs_re_le_norm _).trans_eq (norm_mul _ _)
      · exact abs_re_le_norm v
    _ = (w.im * ‖cauchyDeriv f w‖ + Real.pi * L) * ‖v‖ := by ring
    _ ≤ (4 * Real.exp 2 * (Real.pi * L) + Real.pi * L) * ‖v‖ := by gcongr
    _ = _ := by ring

private noncomputable def boundaryPrimitive (f : ℝ → ℝ) (x : ℝ) : ℝ :=
  ∫ z in Iic x, f z

private theorem smoothPrimitive_tendsto {f : ℝ → ℝ} (hf : Integrable f)
    (hs : HasCompactSupport f) (x : ℝ) :
    Tendsto (fun t : ℝ => smoothPrimitive f ⟨x, t⟩) (𝓝[>] 0)
      (𝓝 (boundaryPrimitive f x)) := by
  let K : ℝ → ℝ → ℝ := fun t z =>
    (t * ((⟨x - z, t⟩ : ℂ)⁻¹).re - (⟨x - z, t⟩ : ℂ).arg) * f z
  have hK t (ht : 0 < t) : smoothPrimitive f ⟨x, t⟩ = (∫ z, f z) + (∫ z, K t z) / Real.pi := by
    let w : ℂ := ⟨x, t⟩
    have hfc := integrable_cauchyKernel (w := w) hf ht
    have hfl := integrable_logKernel (w := w) hf hs ht
    have hx (z : ℝ) : w - (z : ℂ) = ⟨x - z, t⟩  := by apply Complex.ext <;> simp [w]
    change smoothPrimitive f w = _
    rw [smoothPrimitive, cauchy, logPrimitive, ← Complex.reCLM_apply (z := ∫ z, _),
      ← Complex.imCLM_apply (z := ∫ z, _), ← Complex.reCLM.integral_comp_comm hfc,
      ← Complex.imCLM.integral_comp_comm hfl, ← integral_const_mul,
      ← integral_sub ((Complex.reCLM.integrable_comp hfc).const_mul _)
        (Complex.imCLM.integrable_comp hfl)]
    congr 2
    apply integral_congr_ae
    refine ae_of_all _ fun z => ?_
    simp only [K, hx, Complex.reCLM_apply, Complex.imCLM_apply, Complex.mul_re, Complex.mul_im,
      Complex.ofReal_re, Complex.ofReal_im, mul_zero, sub_zero, zero_add, Complex.log_im, w]
    ring
  have hlim : Tendsto (fun t => ∫ z, K t z) (𝓝[>] 0)
      (𝓝 (∫ z in Ioi x, -Real.pi * f z)) := by
    rw [← integral_indicator measurableSet_Ioi]
    apply tendsto_integral_filter_of_dominated_convergence
      (fun z => (1 + Real.pi) * ‖f z‖) ?_ ?_ (hf.norm.const_mul _) ?_
    · refine Filter.Eventually.of_forall fun t => ?_
      have hw : Measurable (fun z : ℝ => (⟨x - z, t⟩ : ℂ)) := by
        have h : ∀ z : ℝ, (⟨x - z, t⟩ : ℂ) = (↑(x - z) : ℂ) + (t : ℂ) * Complex.I :=
          fun z => by apply Complex.ext <;> simp
        simp_rw [h]
        fun_prop
      exact ((by fun_prop : Measurable fun z : ℝ =>
        t * ((⟨x - z, t⟩ : ℂ)⁻¹).re - (⟨x - z, t⟩ : ℂ).arg).aestronglyMeasurable).mul
        hf.aestronglyMeasurable
    · filter_upwards [self_mem_nhdsWithin (s := Ioi (0 : ℝ))] with t ht
      refine ae_of_all _ fun z => ?_
      let w : ℂ := ⟨x - z, t⟩
      have hw : 0 < w.im := ht
      have hN := hw.trans_le ((le_abs_self w.im).trans (abs_im_le_norm w))
      have htinv : |t * (w⁻¹).re| ≤ 1 := by
        rw [abs_mul, abs_of_pos hw]
        calc
          _ ≤ t * ‖w⁻¹‖ := mul_le_mul_of_nonneg_left (abs_re_le_norm _) hw.le
          _ = t / ‖w‖ := by rw [norm_inv, div_eq_mul_inv]
          _ ≤ 1 := (div_le_one hN).mpr ((le_abs_self w.im).trans (abs_im_le_norm w))
      rw [show K t z = (t * (w⁻¹).re - w.arg) * f z from rfl, norm_mul, Real.norm_eq_abs]
      exact mul_le_mul_of_nonneg_right
        ((abs_sub _ _).trans (add_le_add htinv (abs_arg_le_pi _))) (norm_nonneg _)
    · have hne : ∀ᵐ z : ℝ, z ≠ x := by
        simp [ae_iff]
      filter_upwards [hne] with z hz
      have hwlim : Tendsto (fun t : ℝ => (⟨x - z, t⟩ : ℂ)) (𝓝[>] 0) (𝓝 (↑(x - z))) := by
        have hw (t : ℝ) : (⟨x - z, t⟩ : ℂ) = (↑(x - z) : ℂ) + (t : ℂ) * Complex.I := by
          apply Complex.ext <;> simp
        simp_rw [hw]
        have h : Continuous fun t : ℝ => (↑(x - z) : ℂ) + (t : ℂ) * Complex.I := by fun_prop
        simpa using (h.continuousAt (x := 0)).tendsto.mono_left
          (nhdsWithin_le_nhds (s := Ioi (0 : ℝ)))
      have hinvCont := continuous_re.continuousAt.comp
        (continuousAt_inv₀ (show (↑(x - z) : ℂ) ≠ 0 by exact_mod_cast sub_ne_zero.mpr hz.symm))
      have hInv := hinvCont.tendsto.comp hwlim
      have hterm : Tendsto (fun t : ℝ => t * ((⟨x - z, t⟩ : ℂ)⁻¹).re)
          (𝓝[>] 0) (𝓝 0) := by
        have ht : Tendsto (fun t : ℝ => t) (𝓝[>] 0) (𝓝 0) :=
          tendsto_id.mono_left nhdsWithin_le_nhds
        simpa using ht.mul hInv
      rcases lt_or_gt_of_ne hz with hzx | hxz
      · have hp : 0 < x - z := sub_pos.mpr hzx
        have ha : Tendsto (fun t : ℝ => (⟨x - z, t⟩ : ℂ).arg) (𝓝[>] 0) (𝓝 0) := by
          have he := (continuousAt_arg (Or.inl (by simpa using hp) :
            (↑(x - z) : ℂ) ∈ slitPlane)).tendsto.comp hwlim
          rwa [arg_ofReal_of_nonneg hp.le] at he
        simpa [K, indicator_of_notMem (show z ∉ Ioi x from not_lt.mpr hzx.le)] using
          (hterm.sub ha).mul_const (f z)
      · have hp : x - z < 0 := sub_neg.mpr hxz
        have hwlim' : Tendsto (fun t : ℝ => (⟨x - z, t⟩ : ℂ)) (𝓝[>] 0)
            (𝓝[{v : ℂ | 0 ≤ v.im}] (↑(x - z))) := by
          refine tendsto_nhdsWithin_iff.mpr ⟨hwlim, ?_⟩
          have hpos : ∀ᶠ t : ℝ in 𝓝[>] 0, t ∈ Ioi (0 : ℝ) := self_mem_nhdsWithin
          exact hpos.mono fun t ht => show 0 ≤ t from (show 0 < t from ht).le
        have ha := (tendsto_arg_nhdsWithin_im_nonneg_of_re_neg_of_im_zero
          (z := (↑(x - z) : ℂ)) (by simpa using hp) (by simp)).comp hwlim'
        simpa [K, indicator_of_mem (show z ∈ Ioi x from hxz)] using (hterm.sub ha).mul_const (f z)
  have h := (hlim.div_const Real.pi).const_add (∫ z, f z)
  have he : (∫ z, f z) + (∫ z in Ioi x, -Real.pi * f z) / Real.pi = boundaryPrimitive f x := by
    rw [integral_const_mul, show (∫ z, f z) = (∫ z in Iic x, f z) + (∫ z in Ioi x, f z) by
      simpa [compl_Iic] using (integral_add_compl (s := Iic x) measurableSet_Iic hf).symm]
    rw [boundaryPrimitive]
    field_simp [Real.pi_ne_zero]
    ring
  rw [he] at h
  apply h.congr'
  have hpos : ∀ᶠ t : ℝ in 𝓝[>] 0, t ∈ Ioi (0 : ℝ) := self_mem_nhdsWithin
  filter_upwards [hpos] with t ht using (hK t ht).symm

-- Lipschitz approximations to the boundary primitive.
private noncomputable def goodSet (f : ℝ → ℝ) (L : ℝ) : Set ℝ :=
  {x | poissonMax f x ≤ ENNReal.ofReal L}

private theorem isClosed_goodSet (f : ℝ → ℝ) (L : ℝ) : IsClosed (goodSet f L) := by
  rw [← isOpen_compl_iff]
  change IsOpen {x | ¬poissonMax f x ≤ ENNReal.ofReal L}
  simp only [not_le]
  exact isOpen_poissonMax_gt f (ENNReal.ofReal L)

private noncomputable def lifted (S : Set ℝ) (ε x : ℝ) : ℂ :=
  ⟨x, 8 * infDist x S + ε⟩

private theorem lifted_lipschitz (S : Set ℝ) (ε : ℝ) : LipschitzWith 9 (lifted S ε) := by
  apply LipschitzWith.of_dist_le_mul
  intro x y
  let z := lifted S ε x - lifted S ε y
  have hz : ‖z‖ ≤ |z.re| + |z.im| := by
    have h : z = (z.re : ℂ) + (z.im : ℂ) * Complex.I := by apply Complex.ext <;> simp
    calc
      ‖z‖ = ‖(z.re : ℂ) + (z.im : ℂ) * Complex.I‖ := by rw [← h]
      _ ≤ _ := by
        simpa [norm_mul, Real.norm_eq_abs] using
          norm_add_le (z.re : ℂ) ((z.im : ℂ) * Complex.I)
  have hi := (lipschitz_infDist_pt S).dist_le_mul x y
  rw [NNReal.coe_one, one_mul, Real.dist_eq, Real.dist_eq] at hi
  rw [dist_eq_norm]
  change ‖z‖ ≤ _
  refine hz.trans ?_
  change |x - y| + |(8 * infDist x S + ε) - (8 * infDist y S + ε)| ≤ 9 * dist x y
  rw [show 8 * infDist x S + ε - (8 * infDist y S + ε) =
    8 * (infDist x S - infDist y S) by ring, abs_mul, abs_of_nonneg (by norm_num : 0 ≤ (8 : ℝ)),
    Real.dist_eq]
  linarith

private noncomputable def gradientConstant : ℝ≥0 :=
  ⟨1 + 4 * Real.exp 2, by positivity⟩

private theorem smooth_lifted_lipschitz {f : ℝ → ℝ} (hf : Integrable f)
    (hs : HasCompactSupport f) {L ε : ℝ} (hL : 0 < L) (hε : 0 < ε)
    (hG : (goodSet f L).Nonempty) :
    LipschitzWith (9 * gradientConstant * Real.toNNReal L)
      (fun x => smoothPrimitive f (lifted (goodSet f L) ε x)) := by
  let G := goodSet f L
  let γ := lifted G ε
  let F := smoothPrimitive f ∘ γ
  let C := gradientConstant * Real.toNNReal L
  have hγ : LipschitzWith 9 γ := lifted_lipschitz G ε
  have hγpos (x : ℝ) : 0 < (γ x).im := by
    change 0 < 8 * infDist x G + ε
    linarith [infDist_nonneg (x := x) (s := G)]
  have hloc (x : ℝ) : LipschitzOnWith C (smoothPrimitive f) (ball (γ x) ((γ x).im / 16)) := by
    let w := γ x
    obtain ⟨y, hy, hxy⟩ := exists_mem_closure_infDist_eq_dist hG x
    have hy' : y ∈ G := (isClosed_goodSet f L).closure_subset hy
    have hdist : |w.re - y| ≤ w.im / 8 := by
      have he := hxy
      rw [Real.dist_eq] at he
      change |x - y| ≤ (8 * infDist x G + ε) / 8
      linarith
    have hcone (z : ℂ) (hz : z ∈ ball w (w.im / 16)) :
        0 < z.im ∧ |z.re - y| ≤ z.im / 4 := by
      have hw := hγpos x
      have hz' : ‖z - w‖ < w.im / 16 := by simpa [dist_eq_norm] using hz
      have hr := (abs_re_le_norm (z - w)).trans_lt hz'
      have hi := (abs_im_le_norm (z - w)).trans_lt hz'
      rw [Complex.sub_re] at hr
      rw [Complex.sub_im] at hi
      have := abs_sub_le z.re w.re y
      have := neg_abs_le (z.im - w.im)
      change 0 < w.im at hw
      constructor <;> linarith
    refine (convex_ball (γ x) ((γ x).im / 16)).lipschitzOnWith_of_nnNorm_hasFDerivWithin_le
      (fun z hz => (hasFDerivAt_smoothPrimitive hf hs (hcone z hz).1).hasFDerivWithinAt) ?_
    intro z hz
    rw [← NNReal.coe_le_coe, coe_nnNorm]
    change ‖primitiveDeriv f z‖ ≤ ↑(gradientConstant * Real.toNNReal L)
    rw [NNReal.coe_mul, Real.coe_toNNReal _ hL.le]
    exact primitiveDeriv_le hf hL hy' (hcone z hz).1 (hcone z hz).2
  have hlocF : LocallyLipschitz F := by
    intro x
    refine ⟨C * 9, γ ⁻¹' ball (γ x) ((γ x).im / 16), ?_, ?_⟩
    · exact hγ.continuous.continuousAt.preimage_mem_nhds
        (ball_mem_nhds _ (div_pos (hγpos x) (by norm_num)))
    · exact (hloc x).comp hγ.lipschitzOnWith (mapsTo_preimage ..)
  have hderiv : ∀ᵐ x : ℝ, ‖deriv F x‖ ≤ (9 * C : ℝ≥0) := by
    filter_upwards [hγ.ae_differentiableAt_real] with x hD
    let w := γ x
    have hw := hγpos x
    have hcalc := (hasFDerivAt_smoothPrimitive hf hs hw).comp_hasDerivAt x hD.hasDerivAt
    rw [hcalc.deriv]
    have hl := (hloc x)
    have hnorm : ‖primitiveDeriv f w‖ ≤ C :=
      (hasFDerivAt_smoothPrimitive hf hs hw).le_of_lipschitzOn
        (ball_mem_nhds w (div_pos hw (by norm_num))) hl
    calc
      _ ≤ ‖primitiveDeriv f w‖ * ‖deriv γ x‖ := ContinuousLinearMap.le_opNorm _ _
      _ ≤ (C : ℝ) * 9 := mul_le_mul hnorm (norm_deriv_le_of_lipschitz hγ)
        (norm_nonneg _) C.coe_nonneg
      _ = _ := by simp [mul_comm]
  have he (a b : ℝ) (hab : a ≤ b) : dist (F a) (F b) ≤ (9 * C : ℝ≥0) * dist a b := by
    have hlocal : LocallyLipschitzOn (uIcc a b) F := hlocF.locallyLipschitzOn
    obtain ⟨_, hq⟩ := hlocal.exists_lipschitzOnWith_of_compact isCompact_uIcc
    have hac := hq.absolutelyContinuousOnInterval
    rw [dist_comm (F a), dist_eq_norm, ← hac.integral_deriv_eq_sub, dist_comm a b,
      Real.dist_eq, abs_of_nonneg (sub_nonneg.mpr hab)]
    simpa [abs_of_nonneg (sub_nonneg.mpr hab)] using
      intervalIntegral.norm_integral_le_of_norm_le_const_ae
        (hderiv.mono (fun _ hx _ => hx) : ∀ᵐ x, x ∈ uIoc a b → ‖deriv F x‖ ≤ ↑(9 * C))
  apply LipschitzWith.of_dist_le_mul
  intro a b
  rcases le_total a b with hab | hba
  · simpa [F, γ, C, mul_assoc] using he a b hab
  · rw [dist_comm, dist_comm a b]
    simpa [F, γ, C, mul_assoc] using he b a hba

private theorem poissonMax_le_of_bound {f : ℝ → ℝ} {M : ℝ}
    (hM : 0 ≤ M) (hb : ∀ x, |f x| ≤ M) (x : ℝ) :
    poissonMax f x ≤ ENNReal.ofReal M := by
  simp only [poissonMax, iSup_le_iff]
  intro t ht y _
  let d : ℝ≥0 := ⟨t, ht.le⟩
  let p := ProbabilityTheory.cauchyPDFReal y d
  have hp : ∀ z, t / (Real.pi * (t ^ 2 + (y - z) ^ 2)) = p z := by
    intro z
    rw [show p = ProbabilityTheory.cauchyPDFReal y d by rfl, ProbabilityTheory.cauchyPDFReal_def]
    change _ = _ * t * ((z - y) ^ 2 + t ^ 2)⁻¹
    rw [div_eq_mul_inv, mul_inv_rev, show t ^ 2 + (y - z) ^ 2 = (z - y) ^ 2 + t ^ 2 by ring]
    ring
  have hd : d ≠ 0 := fun h => ht.ne' (congrArg NNReal.toReal h)
  have hint : Integrable p := ProbabilityTheory.integrable_cauchyPDFReal y
  have hp₀ : ∀ z, 0 ≤ p z :=
    fun z => (ProbabilityTheory.cauchyPDF_pos y hd z).le
  rw [poissonValue, Real.eNorm_eq_ofReal_abs, ENNReal.ofReal_le_ofReal_iff hM]
  simp_rw [hp]
  calc
    |∫ z, p z * f z| ≤ ∫ z, |p z * f z| := by
      simpa only [Real.norm_eq_abs] using norm_integral_le_integral_norm (fun z => p z * f z)
    _ ≤ ∫ z, p z * M := by
      apply integral_mono_of_nonneg (ae_of_all _ fun z => abs_nonneg _) (hint.mul_const M)
      exact ae_of_all _ fun z => by
        change |p z * f z| ≤ p z * M
        rw [abs_mul, abs_of_nonneg (hp₀ z)]
        exact mul_le_mul_of_nonneg_left (hb z) (hp₀ z)
    _ = M := by
      rw [integral_mul_const, ProbabilityTheory.integral_cauchyPDFReal_eq_one _
        hd, one_mul]

private theorem measure_bad_ne_top {f : ℝ → ℝ} (hfin : (∫⁻ x, poissonMax f x) ≠ ∞)
    {L : ℝ} (hL : 0 < L) : volume (goodSet f L)ᶜ ≠ ∞ := by
  have h := mul_meas_ge_le_lintegral (measurable_poissonMax f) (ENNReal.ofReal L)
    (μ := (volume : Measure ℝ))
  have hsub : (goodSet f L)ᶜ ⊆ {x | ENNReal.ofReal L ≤ poissonMax f x} :=
    fun x hx => show ENNReal.ofReal L ≤ poissonMax f x from (lt_of_not_ge (show
      ¬poissonMax f x ≤ ENNReal.ofReal L from hx)).le
  intro hbad
  have he : volume {x | ENNReal.ofReal L ≤ poissonMax f x} = ∞ :=
    top_unique (hbad ▸ measure_mono hsub)
  rw [he, ENNReal.mul_top (ENNReal.ofReal_ne_zero_iff.mpr hL)] at h
  exact hfin (top_unique h)

private theorem goodSet_nonempty {f : ℝ → ℝ} (hfin : (∫⁻ x, poissonMax f x) ≠ ∞)
    {L : ℝ} (hL : 0 < L) : (goodSet f L).Nonempty := by
  by_contra! h
  exact measure_bad_ne_top hfin hL (by rw [h, compl_empty, Real.volume_univ])

private noncomputable def stoppedPrimitive (f : ℝ → ℝ) (L x : ℝ) : ℝ := by
  classical
  exact if x ∈ goodSet f L then boundaryPrimitive f x
    else smoothPrimitive f (lifted (goodSet f L) 0 x)

private theorem stoppedPrimitive_lipschitz {f : ℝ → ℝ} (hf : Integrable f)
    (hs : HasCompactSupport f) {L : ℝ} (hL : 0 < L) (hG : (goodSet f L).Nonempty) :
    LipschitzWith (9 * gradientConstant * Real.toNNReal L) (stoppedPrimitive f L) := by
  classical
  have hpoint (x : ℝ) : Tendsto (fun ε => smoothPrimitive f (lifted (goodSet f L) ε x))
      (𝓝[>] (0 : ℝ)) (𝓝 (stoppedPrimitive f L x)) := by
    by_cases hx : x ∈ goodSet f L
    · simpa [stoppedPrimitive, ite_eq_left hx, lifted, infDist_zero_of_mem hx] using
        smoothPrimitive_tendsto hf hs x
    · have hi := ((isClosed_goodSet f L).notMem_iff_infDist_pos hG).mp hx
      have hw : 0 < (lifted (goodSet f L) 0 x).im := by
        change 0 < 8 * infDist x (goodSet f L) + 0
        positivity
      have hc : Continuous fun ε => lifted (goodSet f L) ε x := by
        have he (ε : ℝ) : lifted (goodSet f L) ε x =
            (x : ℂ) + (↑(8 * infDist x (goodSet f L) + ε) : ℂ) * Complex.I := by
          apply Complex.ext <;> simp [lifted]
        simp_rw [he]
        fun_prop
      have hAt : ContinuousAt (fun ε => smoothPrimitive f (lifted (goodSet f L) ε x)) 0 :=
        ContinuousAt.comp (f := fun ε => lifted (goodSet f L) ε x)
          (hasFDerivAt_smoothPrimitive hf hs hw).continuousAt hc.continuousAt
      rw [stoppedPrimitive, ite_eq_right hx]
      exact hAt.continuousWithinAt
  apply LipschitzWith.of_dist_le_mul
  intro x y
  apply le_of_tendsto ((hpoint x).dist (hpoint y))
  have hpos : ∀ᶠ ε : ℝ in 𝓝[>] 0, ε ∈ Ioi (0 : ℝ) := self_mem_nhdsWithin
  filter_upwards [hpos] with ε hε
  exact (smooth_lifted_lipschitz hf hs hL hε hG).dist_le_mul x y

-- Cancellation on the component intervals.
private theorem exists_disjoint_interval_components {U : Set ℝ} (ho : IsOpen U)
    (hfin : volume U ≠ ∞) :
    ∃ (ι : Type) (_ : Countable ι) (a b : ι → ℝ),
      (∀ i, a i < b i ∧ a i ∉ U ∧ b i ∉ U) ∧
      Pairwise (Disjoint on fun i => Ioo (a i) (b i)) ∧ (⋃ i, Ioo (a i) (b i)) = U := by
  classical
  let ι := Set.range (fun x : U => connectedComponentIn U (x : ℝ))
  have hrepr (i : ι) : ∃ x ∈ U, (i : Set ℝ) = connectedComponentIn U x := by
    obtain ⟨x, hx⟩ := i.property
    exact ⟨x, x.property, hx.symm⟩
  have hOpen (i : ι) : IsOpen (i : Set ℝ) := by
    obtain ⟨x, _, hx⟩ := hrepr i
    rw [hx]
    exact ho.connectedComponentIn
  have hNe (i : ι) : (i : Set ℝ).Nonempty := by
    obtain ⟨x, hx, he⟩ := hrepr i
    exact ⟨x, he ▸ mem_connectedComponentIn hx⟩
  have hdisj : Pairwise (Disjoint on fun i : ι => (i : Set ℝ)) := by
    intro i j hne
    obtain ⟨x, _, hx⟩ := hrepr i
    obtain ⟨y, _, hy⟩ := hrepr j
    apply disjoint_left.mpr
    intro z hz hz'
    change z ∈ (i : Set ℝ) at hz
    change z ∈ (j : Set ℝ) at hz'
    rw [hx] at hz
    rw [hy] at hz'
    exact hne (Subtype.ext (hx.trans ((connectedComponentIn_eq hz).trans
      (connectedComponentIn_eq hz').symm) |>.trans hy.symm))
  have hiUnion : (⋃ i : ι, (i : Set ℝ)) = U := by
    ext x
    constructor
    · rintro hx
      rcases mem_iUnion.mp hx with ⟨i, hi⟩
      obtain ⟨y, _, hy⟩ := hrepr i
      exact connectedComponentIn_subset U y (hy ▸ hi)
    · intro hx
      exact mem_iUnion.mpr ⟨⟨_, ⟨⟨x, hx⟩, rfl⟩⟩, mem_connectedComponentIn hx⟩
  let : Countable ι := hdisj.countable_of_isOpen_disjoint hOpen hNe
  let a := fun i : ι => sInf (i : Set ℝ)
  let b := fun i : ι => sSup (i : Set ℝ)
  have hI (i : ι) : Ioo (a i) (b i) = (i : Set ℝ) ∧ a i < b i ∧ a i ∉ U ∧ b i ∉ U := by
    obtain ⟨x, hxU, hx⟩ := hrepr i
    have hxI : x ∈ (i : Set ℝ) := hx ▸ mem_connectedComponentIn hxU
    have hcon : IsPreconnected (i : Set ℝ) := hx.symm ▸ isPreconnected_connectedComponentIn
    have hs : (i : Set ℝ) ⊆ U := hx.symm ▸ connectedComponentIn_subset U x
    have hu : BddAbove (i : Set ℝ) := by
      by_contra hn
      have hsub : Ioi x ⊆ (i : Set ℝ) := by
        intro y hy
        obtain ⟨z, hz, hyz⟩ := not_bddAbove_iff.mp hn y
        exact hcon.ordConnected.out hxI hz ⟨le_of_lt hy, hyz.le⟩
      have h := measure_mono (hsub.trans hs) (μ := (volume : Measure ℝ))
      rw [Real.volume_Ioi] at h
      exact hfin (top_unique h)
    have hl : BddBelow (i : Set ℝ) := by
      by_contra hn
      have hsub : Iio x ⊆ (i : Set ℝ) := by
        intro y hy
        obtain ⟨z, hz, hzy⟩ := not_bddBelow_iff.mp hn y
        exact hcon.ordConnected.out hz hxI ⟨hzy.le, le_of_lt hy⟩
      have h := measure_mono (hsub.trans hs) (μ := (volume : Measure ℝ))
      rw [Real.volume_Iio] at h
      exact hfin (top_unique h)
    have hInt : Ioo (a i) (b i) = (i : Set ℝ) := by
      refine ((show IsConnected (i : Set ℝ) from ⟨hNe i, hcon⟩).Ioo_csInf_csSup_subset
        hl hu).antisymm ?_
      intro y hy
      obtain ⟨r, hr, hb⟩ := Metric.isOpen_iff.mp (hOpen i) y hy
      have hlo : y - r / 2 ∈ (i : Set ℝ) := hb (by
        rw [Real.ball_eq_Ioo]
        exact ⟨by linarith, by linarith⟩)
      have hhi : y + r / 2 ∈ (i : Set ℝ) := hb (by
        rw [Real.ball_eq_Ioo]
        exact ⟨by linarith, by linarith⟩)
      exact ⟨(csInf_le hl hlo).trans_lt (by linarith),
        (show y < y + r / 2 by linarith).trans_le (le_csSup hu hhi)⟩
    have hab := (mem_Ioo.mp (hInt.symm ▸ hxI)).1.trans (mem_Ioo.mp (hInt.symm ▸ hxI)).2
    have hclosure : closure (i : Set ℝ) = Icc (a i) (b i) := by
      rw [← hInt, closure_Ioo hab.ne]
    have hend (z : ℝ) (hz : z ∈ closure (i : Set ℝ)) (hn : z ∉ (i : Set ℝ)) : z ∉ U := by
      intro hzu
      apply hn
      rw [hx]
      have hpre := hcon.subset_closure (subset_insert z _) (insert_subset hz subset_closure)
      exact (hpre.subset_connectedComponentIn (mem_insert_of_mem z hxI)
        (insert_subset hzu hs)) (mem_insert z _)
    refine ⟨hInt, hab, hend _ ?_ ?_, hend _ ?_ ?_⟩
    · rw [hclosure]
      exact ⟨le_rfl, hab.le⟩
    · rw [← hInt]
      simp
    · rw [hclosure]
      exact ⟨hab.le, le_rfl⟩
    · rw [← hInt]
      simp
  refine ⟨ι, inferInstance, a, b, fun i => (hI i).2, ?_, ?_⟩
  · intro i j hne
    change Disjoint (Ioo (a i) (b i)) (Ioo (a j) (b j))
    rw [(hI i).1, (hI j).1]
    exact hdisj hne
  · simpa only [(hI _).1] using hiUnion

private theorem ae_deriv_eq_of_eqOn {F G : ℝ → ℝ} {S : Set ℝ} {A B : ℝ≥0}
    (hF : LipschitzWith A F) (hG : LipschitzWith B G) (h : EqOn F G S) :
    ∀ᵐ x, x ∈ S → deriv F x = deriv G x := by
  have hn := (countable_ofPred_isolated_within (s := S)).measure_zero (μ := (volume : Measure ℝ))
  have hIso : ∀ᵐ x : ℝ, x ∉ {x ∈ S | 𝓝[S \ {x}] x = ⊥} := ae_iff.mpr (by simpa using hn)
  filter_upwards [hF.ae_differentiableAt_real, hG.ae_differentiableAt_real, hIso]
    with x hxF hxG hx hxS
  have hU : UniqueDiffWithinAt ℝ S x := by
    rw [uniqueDiffWithinAt_iff_accPt, accPt_principal_iff_nhdsWithin]
    exact neBot_iff.mpr (fun he => hx ⟨hxS, he⟩)
  exact ((hxF.hasDerivAt.hasDerivWithinAt.congr h.symm (h hxS).symm).derivWithin hU).symm.trans
    (hxG.hasDerivAt.hasDerivWithinAt.derivWithin hU)

private theorem pairing_on_components {F b : ℝ → ℝ} {U : Set ℝ} {A : ℝ≥0} {B D : ℝ}
    (hU : IsOpen U) (hfin : volume U ≠ ∞) (hF : LipschitzWith A F) (hzero : EqOn F 0 Uᶜ)
    (hb : AEStronglyMeasurable b) (hbound : ∀ᵐ x, ‖b x‖ ≤ D)
    (hosc : ∀ a c : ℝ, a < c → ⨍ x in Icc a c, |b x - ⨍ y in Icc a c, b y| ≤ B) :
    ‖∫ x, deriv F x * b x‖ ≤ (A : ℝ) * B * volume.real U := by
  obtain ⟨ι, hcount, a, c, hEnds, hDisj, hUnion⟩ :=
    exists_disjoint_interval_components hU hfin
  let : Countable ι := hcount
  let d := deriv F
  have hda : ∀ x, ‖d x‖ ≤ A := fun x => norm_deriv_le_of_lipschitz hF
  have hdm : AEStronglyMeasurable d := (measurable_deriv _).aestronglyMeasurable
  have hdi (s : Set ℝ) (hs : volume s ≠ ∞) : IntegrableOn d s :=
    Measure.integrableOn_of_bounded hs hdm (ae_of_all _ hda)
  have hbi (s : Set ℝ) (hs : volume s ≠ ∞) : IntegrableOn b s :=
    Measure.integrableOn_of_bounded hs hb (ae_restrict_of_ae hbound)
  have hint : IntegrableOn (fun x => d x * b x) U :=
    (hbi U hfin).bdd_mul hdm.restrict (ae_of_all _ hda)
  have hz := ae_deriv_eq_of_eqOn hF (LipschitzWith.const (0 : ℝ)) hzero
  have hp : (∫ x, d x * b x) = ∫ x in U, d x * b x := by
    rw [← integral_indicator hU.measurableSet]
    apply integral_congr_ae
    filter_upwards [hz] with x hx
    by_cases hxU : x ∈ U
    · simp [hxU]
    · have hd : d x = 0 := by simpa [d] using hx hxU
      simp [hxU, hd]
  have hI (i : ι) : ‖∫ x in Ioo (a i) (c i), d x * b x‖ ≤
      ∫ _ in Ioo (a i) (c i), (A : ℝ) * B := by
    have hab := (hEnds i).1
    have hrestrict : (volume : Measure ℝ).restrict (Ioo (a i) (c i)) =
        volume.restrict (Icc (a i) (c i)) := Measure.restrict_congr_set Ioo_ae_eq_Icc
    simp only [hrestrict]
    let s := Icc (a i) (c i)
    let m := ⨍ x in s, b x
    have ht : volume s ≠ ∞ := isCompact_Icc.measure_lt_top.ne
    have hB := hbi s ht
    have hmean : (∫ x in s, |b x - m|) ≤ B * volume.real s := by
      have hm := hosc (a i) (c i) hab
      change (⨍ x in s, |b x - m|) ≤ B at hm
      rw [setAverage_eq, smul_eq_mul, ← div_eq_inv_mul] at hm
      have hpos : 0 < (volume : Measure ℝ).real s := by
        rw [show s = Icc (a i) (c i) by rfl, Real.volume_real_Icc_of_le hab.le]
        exact sub_pos.mpr hab
      exact (div_le_iff₀ hpos).mp hm
    have hdz : (∫ x in s, d x) = 0 := by
      have h := hF.lipschitzOnWith.absolutelyContinuousOnInterval
        (a := a i) (b := c i)
      change (∫ x in Icc (a i) (c i), deriv F x) = _
      rw [integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le hab.le,
        h.integral_deriv_eq_sub, hzero (hEnds i).2.1, hzero (hEnds i).2.2]
      change (0 : ℝ) - 0 = 0
      exact sub_self _
    have hb' : IntegrableOn (fun x => b x - m) s :=
      hB.sub (integrableOn_const ht)
    have he : (∫ x in s, d x * b x) = ∫ x in s, d x * (b x - m) := by
      simp_rw [mul_sub]
      rw [integral_sub (hB.bdd_mul hdm.restrict (ae_of_all _ hda)) ((hdi s ht).mul_const m),
        integral_mul_const, hdz, zero_mul, sub_zero]
    rw [he]
    change _ ≤ ∫ _ in s, (A : ℝ) * B
    rw [setIntegral_const, smul_eq_mul]
    calc
      _ ≤ ∫ x in s, ‖d x * (b x - m)‖ := norm_integral_le_integral_norm _
      _ ≤ ∫ x in s, (A : ℝ) * |b x - m| := by
        apply integral_mono_of_nonneg (ae_of_all _ fun _ => norm_nonneg _) (hb'.norm.const_mul _)
        exact ae_of_all _ fun x => by
          change ‖d x * (b x - m)‖ ≤ (A : ℝ) * ‖b x - m‖
          rw [norm_mul]
          exact mul_le_mul_of_nonneg_right (hda x) (norm_nonneg _)
      _ ≤ volume.real s * ((A : ℝ) * B) := by
        rw [integral_const_mul]
        exact (mul_le_mul_of_nonneg_left hmean A.coe_nonneg).trans_eq (by ring)
  have hConst : IntegrableOn (fun _ : ℝ => (A : ℝ) * B) U := integrableOn_const hfin
  rw [← hUnion] at hint hConst
  have hsum := hasSum_integral_iUnion (fun i => measurableSet_Ioo (a := a i) (b := c i))
    hDisj hint
  have hsum' := hasSum_integral_iUnion (fun i => measurableSet_Ioo (a := a i) (b := c i))
    hDisj hConst
  rw [hUnion] at hsum hsum'
  have hreal : (∫ _ in U, (A : ℝ) * B) = (A : ℝ) * B * volume.real U := by
    rw [setIntegral_const, smul_eq_mul, mul_comm]
  rw [hp, ← hreal]
  apply le_of_tendsto_of_tendsto' hsum.norm hsum'
  intro s
  exact (norm_sum_le s _).trans (Finset.sum_le_sum fun i _ => hI i)

private noncomputable def stopConstant : ℝ≥0 := 9 * gradientConstant

-- Summing the bounds at successive levels.
private theorem bounded_bmo_pairing {f b : ℝ → ℝ} {T B D : ℝ}
    (hf : Integrable f) (hs : HasCompactSupport f) (hT : 0 < T)
    (hfb : ∀ x, |f x| ≤ T) (hB : 0 ≤ B)
    (hb : AEStronglyMeasurable b) (hbb : ∀ᵐ x, ‖b x‖ ≤ D)
    (hosc : ∀ a c : ℝ, a < c → ⨍ x in Icc a c, |b x - ⨍ y in Icc a c, b y| ≤ B)
    (hfin : (∫⁻ x, poissonMax f x) ≠ ∞) :
    ‖∫ x, f x * b x‖ ≤ 6 * (stopConstant : ℝ) * B * (∫⁻ x, poissonMax f x).toReal := by
  let N := fun x => (poissonMax f x).toReal
  have hm x : poissonMax f x ≤ ENNReal.ofReal T := poissonMax_le_of_bound hT.le hfb x
  have hNtop x : poissonMax f x ≠ ∞ := ne_top_of_le_ne_top ENNReal.ofReal_ne_top (hm x)
  have hN x : ENNReal.ofReal (N x) = poissonMax f x := ENNReal.ofReal_toReal (hNtop x)
  have hN₀ x : 0 ≤ N x := ENNReal.toReal_nonneg
  have hNm : Measurable N := (measurable_poissonMax f).ennreal_toReal
  have hNi : Integrable N :=
    integrable_toReal_of_lintegral_ne_top (measurable_poissonMax f).aemeasurable hfin
  have hNint : (∫ x, N x) = (∫⁻ x, poissonMax f x).toReal := by
    rw [integral_eq_lintegral_of_nonneg_ae (ae_of_all _ hN₀) hNi.aestronglyMeasurable]
    simp_rw [hN]
  let L := fun n : ℕ => T * (1 / 2 : ℝ) ^ n
  have hL (n : ℕ) : 0 < L n := by dsimp [L]; positivity
  have hstep n : L (n + 1) = L n / 2 := by
    simp only [L, pow_succ]
    ring
  have hLlim : Tendsto L atTop (𝓝 0) := by
    simpa only [mul_zero] using (tendsto_pow_atTop_nhds_zero_of_lt_one
      (by norm_num : 0 ≤ (1 / 2 : ℝ)) (by norm_num)).const_mul T
  let F := fun n => stoppedPrimitive f (L n)
  let G := fun n => goodSet f (L n)
  let U := fun n => (G n)ᶜ
  let A := fun n => stopConstant * Real.toNNReal (L n)
  let K := (stopConstant : ℝ)
  have hK : 0 ≤ K := stopConstant.coe_nonneg
  have hA n : (A n : ℝ) = K * L n := by
    simp [A, K, NNReal.coe_mul, Real.coe_toNNReal _ (hL n).le]
  have hLip (n : ℕ) : LipschitzWith (A n) (F n) :=
    stoppedPrimitive_lipschitz hf hs (hL n) (goodSet_nonempty hfin (hL n))
  have hGood n x : x ∈ G n ↔ N x ≤ L n := by
    change poissonMax f x ≤ ENNReal.ofReal (L n) ↔ _
    rw [← hN x, ENNReal.ofReal_le_ofReal_iff (hL n).le]
  have hBad n x : x ∈ U n ↔ L n < N x := by
    change x ∉ G n ↔ _
    rw [hGood, not_le]
  have heq n : EqOn (F n) (boundaryPrimitive f) (G n) := fun x hx => by
    change stoppedPrimitive f (L n) x = _
    rw [stoppedPrimitive, ite_eq_left hx]
  have hF₀ : F 0 = boundaryPrimitive f := by
    funext x
    exact heq 0 (show poissonMax f x ≤ ENNReal.ofReal (L 0) by simpa [L] using hm x)
  have hderiv₀ : ∀ᵐ x, deriv (F 0) x = f x := by
    have hEq : boundaryPrimitive f =
        fun x => (∫ z in Iic (0 : ℝ), f z) + ∫ z in (0 : ℝ)..x, f z := by
      funext x
      rw [← intervalIntegral.integral_Iic_sub_Iic hf.integrableOn hf.integrableOn]
      simp [boundaryPrimitive]
    filter_upwards [LocallyIntegrable.ae_hasDerivAt_integral hf.locallyIntegrable] with x hx
    rw [hF₀, hEq]
    exact ((hx 0).const_add _).deriv
  let P := fun n => ∫ x, deriv (F n) x * b x
  have hd n x : ‖deriv (F n) x‖ ≤ K * L n := hA n ▸ norm_deriv_le_of_lipschitz (hLip n)
  have hdom n : ∀ᵐ x, ‖deriv (F n) x * b x‖ ≤ (K * N x + ‖f x‖) * D := by
    filter_upwards [ae_deriv_eq_of_eqOn (hLip n) (hLip 0) (hF₀.symm ▸ heq n),
      hderiv₀, hbb] with x hdx hf₀ hbx
    rw [norm_mul]
    have hdn : ‖deriv (F n) x‖ ≤ K * N x + ‖f x‖ := by
      by_cases hx : x ∈ G n
      · rw [hdx hx, hf₀]
        linarith [mul_nonneg hK (hN₀ x)]
      · have hlt : L n < N x := (hBad n x).mp hx
        exact (hd n x).trans (by
          linarith [mul_le_mul_of_nonneg_left hlt.le hK, norm_nonneg (f x)])
    exact mul_le_mul hdn hbx (norm_nonneg _) (by positivity)
  have hdomi : Integrable (fun x => (K * N x + ‖f x‖) * D) :=
    ((hNi.const_mul K).add hf.norm).mul_const D
  have hPm (n : ℕ) : AEStronglyMeasurable (fun x => deriv (F n) x * b x) :=
    (measurable_deriv _).aestronglyMeasurable.mul hb
  have hPi (n : ℕ) : Integrable (fun x => deriv (F n) x * b x) :=
    hdomi.mono' (hPm n) (hdom n)
  have hPlim : Tendsto P atTop (𝓝 0) := by
    simpa [P] using (tendsto_integral_filter_of_dominated_convergence
      (f := fun _ : ℝ => (0 : ℝ)) _ (Eventually.of_forall hPm) (Eventually.of_forall hdom) hdomi
      (ae_of_all _ fun x => by
        have hlim : Tendsto (fun n => deriv (F n) x) atTop (𝓝 0) :=
          squeeze_zero_norm (fun n => hd n x) (by simpa using hLlim.const_mul K)
        simpa using hlim.mul_const (b x)))
  let J := fun n => ∫ x, min (N x) (L n)
  have hJi n : Integrable (fun x => min (N x) (L n)) := by
    apply hNi.mono ((hNm.min measurable_const).aestronglyMeasurable)
    exact ae_of_all _ fun x => by
      rw [Real.norm_of_nonneg (le_min (hN₀ x) (hL n).le), Real.norm_of_nonneg (hN₀ x)]
      exact min_le_left _ _
  have hcost n : L n * volume.real (U n) ≤ 2 * (J n - J (n + 1)) := by
    have hUn : MeasurableSet (U n) := (isClosed_goodSet f _).isOpen_compl.measurableSet
    rw [← show (∫ x, (U n).indicator (fun _ => L n) x) = L n * volume.real (U n) by
      rw [integral_indicator hUn, setIntegral_const, smul_eq_mul, mul_comm]]
    dsimp only [J]
    rw [← integral_sub (hJi n) (hJi (n + 1)), ← integral_const_mul]
    apply integral_mono_of_nonneg ?_ (((hJi n).sub (hJi (n + 1))).const_mul 2)
    · exact ae_of_all _ fun x => by
        change (U n).indicator (fun _ => L n) x ≤ 2 * (min (N x) (L n) - min (N x) (L (n + 1)))
        by_cases hx : x ∈ U n
        · have hx' := (hBad n x).mp hx
          rw [indicator_of_mem hx, min_eq_right hx'.le, min_eq_right (by linarith [hstep n, hL n]),
            hstep]
          ring_nf
          exact le_rfl
        · rw [indicator_of_notMem hx]
          have h := min_le_min_left (N x) (show L (n + 1) ≤ L n by linarith [hstep n, hL n])
          linarith
    · exact ae_of_all _ fun x => indicator_nonneg (fun _ _ => (hL n).le) x
  have hJ₀ n : 0 ≤ J n := integral_nonneg fun x => le_min (hN₀ x) (hL n).le
  have hJ_le n : J n ≤ ∫ x, N x :=
    integral_mono (hJi n) hNi fun x => min_le_left _ _
  have hp n : ‖P n - P (n + 1)‖ ≤ 6 * K * B * (J (n + 1) - J (n + 2)) := by
    have hmono : G (n + 1) ⊆ G n := by
      intro x hx
      exact (hGood n x).mpr (((hGood (n + 1) x).mp hx).trans (by linarith [hstep n, hL n]))
    have hzero : EqOn (F n - F (n + 1)) 0 (U (n + 1))ᶜ := by
      intro x hx
      have hmem : x ∈ G (n + 1) := by simpa [U] using hx
      change F n x - F (n + 1) x = 0
      rw [heq n (hmono hmem), heq (n + 1) hmem, sub_self]
    have hpair := pairing_on_components (isClosed_goodSet f _).isOpen_compl
      (measure_bad_ne_top hfin (hL (n + 1))) ((hLip n).sub (hLip (n + 1))) hzero hb hbb hosc
    have he : P n - P (n + 1) = ∫ x, deriv (F n - F (n + 1)) x * b x := by
      dsimp only [P]
      rw [← integral_sub (hPi n) (hPi (n + 1))]
      apply integral_congr_ae
      filter_upwards [(hLip n).ae_differentiableAt_real, (hLip (n + 1)).ae_differentiableAt_real]
        with x hx₁ hx₂
      rw [(hx₁.hasDerivAt.sub hx₂.hasDerivAt).deriv, sub_mul]
    rw [he]
    refine hpair.trans ?_
    rw [NNReal.coe_add, hA, hA, show K * L n + K * L (n + 1) = 3 * K * L (n + 1) by
      rw [hstep]; ring]
    calc
      _ = (3 * K * B) * (L (n + 1) * volume.real (U (n + 1))) := by ring
      _ ≤ (3 * K * B) * (2 * (J (n + 1) - J (n + 2))) :=
        mul_le_mul_of_nonneg_left (hcost (n + 1)) (by positivity)
      _ = _ := by ring
  have htel n : ‖P 0 - P n‖ ≤ 6 * K * B * (J 1 - J (n + 1)) := by
    induction n with
    | zero => simp
    | succ n ih =>
      calc
        _ ≤ ‖P 0 - P n‖ + ‖P n - P (n + 1)‖ := by
          simpa only [dist_eq_norm] using dist_triangle (P 0) (P n) (P (n + 1))
        _ ≤ _ := (add_le_add ih (hp n)).trans_eq (by ring)
  have hlim : ‖P 0‖ ≤ 6 * K * B * (∫ x, N x) := by
    apply le_of_tendsto (by simpa using (tendsto_const_nhds.sub hPlim).norm)
    exact Eventually.of_forall fun n => (htel n).trans (mul_le_mul_of_nonneg_left
      (by linarith [hJ₀ (n + 1), hJ_le 1]) (by positivity))
  rw [hNint] at hlim
  have he : P 0 = ∫ x, f x * b x :=
    integral_congr_ae (hderiv₀.mono fun x hx => congrArg (· * b x) hx)
  rwa [he] at hlim

-- Pass from bounded functions to locally integrable BMO functions.
private noncomputable def clip (m x : ℝ) := max (-m) (min m x)

private theorem clip_lipschitz (m : ℝ) : LipschitzWith 1 (clip m) :=
  (LipschitzWith.id.const_min m).const_max (-m)

private theorem clip_abs_le {m : ℝ} (hm : 0 ≤ m) (x : ℝ) : |clip m x| ≤ |x| := by
  have hzero : clip m 0 = 0 := by simp [clip, hm]
  simpa only [Real.dist_eq, NNReal.coe_one, one_mul, hzero, sub_zero] using
    (clip_lipschitz m).dist_le_mul x 0

private theorem clip_abs_le_bound {m : ℝ} (hm : 0 ≤ m) (x : ℝ) : |clip m x| ≤ m := by
  apply abs_le.mpr
  exact ⟨le_max_left _ _, max_le (by linarith) (min_le_left _ _)⟩

private theorem clip_tendsto (x : ℝ) : Tendsto (fun n : ℕ => clip n x) atTop (𝓝 x) := by
  apply tendsto_const_nhds.congr'
  obtain ⟨n, hn⟩ := exists_nat_ge |x|
  filter_upwards [eventually_ge_atTop n] with m hm
  have hl : |x| ≤ (m : ℝ) := hn.trans (by exact_mod_cast hm)
  have := abs_le.mp hl
  simp [clip, min_eq_right this.2, max_eq_right this.1]

private theorem clip_meanOscillation {b : ℝ → ℝ} {B m : ℝ} (hb : LocallyIntegrable b)
    (hm : 0 ≤ m)
    (hosc : ∀ a c : ℝ, a < c → ⨍ x in Icc a c, |b x - ⨍ y in Icc a c, b y| ≤ B)
    (a c : ℝ) (hac : a < c) :
    (⨍ x in Icc a c, |clip m (b x) - ⨍ y in Icc a c, clip m (b y)|) ≤ 2 * B := by
  let s := Icc a c
  let μ := (volume : Measure ℝ).restrict s
  let ν := (μ univ)⁻¹ • μ
  let g := clip m ∘ b
  let b₀ := ⨍ x in s, b x
  let g₀ := ⨍ x in s, g x
  let z := clip m b₀
  have hμ : μ univ ≠ ∞ := by
    rw [Measure.restrict_apply_univ]
    exact isCompact_Icc.measure_lt_top.ne
  have hpos : μ univ ≠ 0 := by
    rw [Measure.restrict_apply_univ, Real.volume_Icc, ENNReal.ofReal_ne_zero_iff]
    exact sub_pos.mpr hac
  have : IsProbabilityMeasure ν := by
    constructor
    rw [show ν = (μ univ)⁻¹ • μ by rfl, smul_apply, smul_eq_mul,
      ENNReal.inv_mul_cancel hpos hμ]
  have hbi : Integrable b μ := hb.integrableOn_isCompact isCompact_Icc
  have hbn : Integrable b ν := hbi.smul_measure (ENNReal.inv_ne_top.mpr hpos)
  have hgi : Integrable g ν := by
    have hg := (clip_lipschitz m).continuous.comp_aestronglyMeasurable hbn.aestronglyMeasurable
    apply (integrable_const m).mono' hg
    exact ae_of_all _ fun x => clip_abs_le_bound hm (b x)
  have hdist x : |g x - z| ≤ |b x - b₀| := by
    simpa [g, z, Real.dist_eq] using (clip_lipschitz m).dist_le_mul (b x) b₀
  have hgi' : Integrable (fun x => g x - z) ν := hgi.sub (integrable_const z)
  have hInner : |g₀ - z| ≤ ∫ x, |g x - z| ∂ν := by
    change |(∫ x, g x ∂ν) - z| ≤ _
    have h : (∫ x, g x ∂ν) - z = ∫ x, (g x - z) ∂ν := by
      rw [integral_sub hgi (integrable_const _)]
      simp
    rw [h]
    simpa [Real.norm_eq_abs] using norm_integral_le_integral_norm (μ := ν) fun x => g x - z
  have hNet : (∫ x, |g x - z| ∂ν) ≤ B := by
    apply le_trans (integral_mono hgi'.abs (hbn.sub (integrable_const b₀)).abs hdist)
    exact hosc a c hac
  change (∫ x, |g x - g₀| ∂ν) ≤ _
  calc
    _ ≤ ∫ x, (|g x - z| + |g₀ - z|) ∂ν := by
      apply integral_mono (hgi.sub (integrable_const g₀)).abs (hgi'.abs.add (integrable_const _))
      intro x
      simpa [abs_sub_comm z g₀] using abs_sub_le (g x) z g₀
    _ = (∫ x, |g x - z| ∂ν) + |g₀ - z| := by
      rw [integral_add hgi'.abs (integrable_const _)]
      simp
    _ ≤ 2 * B := by linarith

private theorem integrable_mul_of_bounded_compact {f b : ℝ → ℝ} {M : ℝ}
    (hf : Measurable f) (hs : HasCompactSupport f) (habs : ∀ x, |f x| ≤ M)
    (hb : LocallyIntegrable b) : Integrable (fun x => f x * b x) := by
  apply (integrableOn_iff_integrable_of_support_subset (s := tsupport f) ?_).mp
  · exact (hb.integrableOn_isCompact hs).bdd_mul hf.aestronglyMeasurable
      (ae_of_all _ fun x => by simpa only [Real.norm_eq_abs] using habs x)
  · intro x hx
    by_contra hx'
    exact hx (by simp [image_eq_zero_of_notMem_tsupport hx'])

private theorem pairing_via_poissonMax {f b : ℝ → ℝ} {T B : ℝ}
    (hf : Measurable f) (hs : HasCompactSupport f) (hT : 0 < T)
    (hfb : ∀ x, |f x| ≤ T) (hB : 0 ≤ B) (hb : LocallyIntegrable b)
    (hosc : ∀ a c : ℝ, a < c → ⨍ x in Icc a c, |b x - ⨍ y in Icc a c, b y| ≤ B)
    (hfin : (∫⁻ x, poissonMax f x) ≠ ∞) :
    ‖∫ x, f x * b x‖ ≤ 12 * (stopConstant : ℝ) * B * (∫⁻ x, poissonMax f x).toReal := by
  have hfi : Integrable f := by
    simpa only [mul_one] using
      integrable_mul_of_bounded_compact hf hs hfb
        (locallyIntegrable_const (1 : ℝ) (μ := (volume : Measure ℝ)))
  have hi := integrable_mul_of_bounded_compact hf hs hfb hb
  have hmeas (n : ℕ) : AEStronglyMeasurable (fun x => clip n (b x)) :=
    (clip_lipschitz n).continuous.comp_aestronglyMeasurable hb.aestronglyMeasurable
  have hbound (n : ℕ) : ‖∫ x, f x * clip n (b x)‖ ≤
      12 * (stopConstant : ℝ) * B * (∫⁻ x, poissonMax f x).toReal := by
    have h := bounded_bmo_pairing hfi hs hT hfb (by positivity : 0 ≤ 2 * B)
      (hmeas n)
      (ae_of_all _ fun x => clip_abs_le_bound (Nat.cast_nonneg _) (b x))
      (clip_meanOscillation hb (Nat.cast_nonneg _) hosc) hfin
    convert h using 1
    ring
  have hlim : Tendsto (fun n : ℕ => ∫ x, f x * clip n (b x)) atTop (𝓝 (∫ x, f x * b x)) := by
    refine tendsto_integral_filter_of_dominated_convergence (fun x => ‖f x * b x‖) ?_ ?_ hi.norm ?_
    · exact Eventually.of_forall fun n => hf.aestronglyMeasurable.mul (hmeas n)
    · exact Eventually.of_forall fun n => ae_of_all _ fun x => by
        rw [norm_mul, norm_mul, Real.norm_eq_abs (clip n (b x)), Real.norm_eq_abs (b x)]
        exact mul_le_mul_of_nonneg_left (clip_abs_le (Nat.cast_nonneg _) (b x)) (norm_nonneg _)
    · exact ae_of_all _ fun x => (clip_tendsto (b x)).const_mul (f x)
  exact le_of_tendsto hlim.norm (Eventually.of_forall hbound)

/-- **Fefferman's `H¹`–`BMO` inequality.** There is an absolute constant `C > 0` such that for
every locally integrable `b : ℝ → ℝ` whose mean oscillation over every bounded interval is at
most `B > 0`, and every bounded, measurable, compactly supported `f : ℝ → ℝ`,
`|∫ f b| ≤ C B ‖f‖_{H¹}`, where `‖f‖_{H¹} = ∫ sup_{|y - x| ≤ t} |P_t * f (y)| dx` is the `L¹`
norm of the non-tangential maximal function of the Poisson integral,
`P_t(x) = t / (π (t² + x²))`; this norm characterizes `H¹(ℝ)` (P. Auscher and E. Russ,
*Hardy spaces and divergence operators on strongly Lipschitz domains of ℝⁿ*,
arXiv:math/0201301v1, §1, display (1), citing Fefferman–Stein 1972, Theorem 11). This is the
inclusion `BMO ⊆ (H¹)*` of the duality theorem `(H¹)* = BMO`
(C. Fefferman, *Characterizations of bounded mean oscillation*, Bull. Amer. Math. Soc. 77
(1971), 587–588; C. Fefferman and E. M. Stein, *H^p spaces of several variables*, Acta Math.
129 (1972), 137–193; the duality is stated in A. K. Lerner, *A "local mean oscillation"
decomposition and some its applications*, lecture notes, §3.1). When `∫ f ≠ 0` the right-hand
side is infinite, so the content is the case `∫ f = 0`. -/
public theorem exists_enorm_integral_mul_le_poissonMaximal :
    ∃ C : ℝ, 0 < C ∧ ∀ b : ℝ → ℝ, LocallyIntegrable b → ∀ B : ℝ, 0 < B →
      (∀ a c : ℝ, a < c → ⨍ x in Icc a c, |b x - ⨍ y in Icc a c, b y| ≤ B) →
      ∀ f : ℝ → ℝ, Measurable f → (∃ M : ℝ, ∀ x, |f x| ≤ M) → HasCompactSupport f →
        ‖∫ x, f x * b x‖ₑ ≤ ENNReal.ofReal (C * B) *
          ∫⁻ x, ⨆ t : ℝ, ⨆ (_ : 0 < t), ⨆ y : ℝ, ⨆ (_ : |y - x| ≤ t),
            ‖∫ z, t / (Real.pi * (t ^ 2 + (y - z) ^ 2)) * f z‖ₑ := by
  refine ⟨12 * (stopConstant : ℝ), ?_, ?_⟩
  · change 0 < (12 : ℝ) * (9 * (1 + 4 * Real.exp 2))
    positivity
  intro b hb B hB hosc f hf hfb hs
  obtain ⟨M, hM⟩ := hfb
  have hM₀ := (abs_nonneg (f 0)).trans (hM 0)
  have hpos : 0 < 12 * (stopConstant : ℝ) * B := by
    change 0 < (12 : ℝ) * (9 * (1 + 4 * Real.exp 2)) * B
    positivity
  have hle : (∫⁻ x, poissonMax f x) ≤
      ∫⁻ x, ⨆ t : ℝ, ⨆ (_ : 0 < t), ⨆ y : ℝ, ⨆ (_ : |y - x| ≤ t),
        ‖poissonValue f t y‖ₑ := by
    apply lintegral_mono
    intro x
    simp only [poissonMax, iSup_le_iff]
    intro t ht y hy
    exact le_iSup_of_le t (le_iSup_of_le ht (le_iSup_of_le y
      (le_iSup (fun _ : |y - x| ≤ t => ‖poissonValue f t y‖ₑ) hy.le)))
  have hpair : ‖∫ x, f x * b x‖ₑ ≤
      ENNReal.ofReal (12 * (stopConstant : ℝ) * B) * ∫⁻ x, poissonMax f x := by
    by_cases h : (∫⁻ x, poissonMax f x) = ∞
    · rw [h, ENNReal.mul_top (ENNReal.ofReal_ne_zero_iff.mpr hpos)]
      exact le_top
    · have hp := pairing_via_poissonMax hf hs (T := M + 1) (by positivity)
        (fun x => (hM x).trans (by linarith)) hB.le hb hosc h
      have hh := ENNReal.ofReal_le_ofReal hp
      rw [Real.eNorm_eq_ofReal_abs, ← Real.norm_eq_abs]
      rwa [ENNReal.ofReal_mul hpos.le, ENNReal.ofReal_toReal h] at hh
  exact hpair.trans (mul_le_mul_right hle _)

end MathlibExt.Analysis.HarmonicAnalysis.BoundedMeanOscillationWanted
