/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Analysis.SpecialFunctions.ExponentialIntegral.E1.Basic
public import MathlibExt.Analysis.SpecialFunctions.Gamma.RegularizedIntegral
public import Mathlib.Analysis.Complex.RealDeriv

open Filter Set Topology MeasureTheory

noncomputable section

@[expose] public section

namespace Complex

private lemma ein_one_eq_regularized_integral :
    ein 1 = ∫ t : ℝ in 0..1, (((1 - Real.exp (-t)) / t : ℝ) : ℂ) := by
  let A : ℝ → ℂ := fun t => (((1 - Real.exp (-t)) / t : ℝ) : ℂ)
  let F : ℝ → ℂ := fun t => ein t
  have hA : IntervalIntegrable A volume 0 1 := by
    have hq := Real.intervalIntegrable_exp_neg_sub_one_div.neg
    rw [show A = -fun t : ℝ => (((Real.exp (-t) - 1) / t : ℝ) : ℂ) by
      funext t
      dsimp only [A, Pi.neg_apply]
      rw [← Complex.ofReal_neg]
      congr 1
      ring]
    exact hq
  have hderiv : ∀ x ∈ Ioo (0 : ℝ) 1, HasDerivAt F (A x) x := by
    intro x hx
    have hx0 : x ≠ 0 := hx.1.ne'
    have hd := (differentiable_ein (x : ℂ)).hasDerivAt.comp_ofReal
    apply hd.congr_deriv
    have hm := mul_deriv_ein (x : ℂ)
    dsimp only [A]
    rw [← Complex.ofReal_neg, ← Complex.ofReal_exp] at hm
    rw [Complex.ofReal_div]
    apply (eq_div_iff (Complex.ofReal_ne_zero.mpr hx0)).2
    simpa only [Complex.ofReal_sub, Complex.ofReal_one, mul_comm] using hm
  have hzero : ein (0 : ℂ) = 0 := by simp [ein, einTerm]
  have hF0 : Tendsto F (𝓝[>] 0) (𝓝 0) := by
    change Tendsto (ein ∘ Complex.ofReal) (𝓝[>] 0) (𝓝 0)
    have hc := (differentiable_ein 0).continuousAt.tendsto.comp
      Complex.continuous_ofReal.continuousAt.tendsto
    convert hc.mono_left (show 𝓝[>] (0 : ℝ) ≤ 𝓝 0 from inf_le_left) using 1
    simp only [hzero]
  have hF1 : Tendsto F (𝓝[<] 1) (𝓝 (ein 1)) := by
    change Tendsto (ein ∘ Complex.ofReal) (𝓝[<] 1) (𝓝 (ein 1))
    have hc := (differentiable_ein 1).continuousAt.tendsto.comp
      Complex.continuous_ofReal.continuousAt.tendsto
    convert hc.mono_left (show 𝓝[<] (1 : ℝ) ≤ 𝓝 1 from inf_le_left) using 1
  have hFTC := intervalIntegral.integral_eq_sub_of_hasDerivAt_of_tendsto
    (f := F) (f' := A) (fa := 0) (fb := ein 1) (by norm_num : (0 : ℝ) < 1)
    hderiv hA hF0 hF1
  dsimp only [F, A] at hFTC ⊢
  linear_combination -hFTC

private lemma integrableOn_exp_neg_div_Ioi {x : ℝ} (hx : 0 < x) :
    IntegrableOn (fun t : ℝ => Real.exp (-t) / t) (Ioi x) := by
  have he : IntegrableOn (fun t : ℝ => Real.exp (-t)) (Ioi x) :=
    integrableOn_exp_neg_Ioi x
  have hdom : IntegrableOn (fun t : ℝ => x⁻¹ * Real.exp (-t)) (Ioi x) :=
    he.const_mul x⁻¹
  refine hdom.mono' ?_ ?_
  · exact ((Real.continuous_exp.comp continuous_neg).continuousOn.div continuousOn_id
      (fun t ht => (hx.trans ht).ne')).aestronglyMeasurable measurableSet_Ioi
  · filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    have ht0 : 0 < t := hx.trans ht
    simpa [Real.norm_eq_abs, abs_div, abs_of_pos (Real.exp_pos _), abs_of_pos ht0,
      abs_mul, abs_of_pos (inv_pos.mpr hx), div_eq_mul_inv,
      mul_comm (x⁻¹) (Real.exp (-t))] using
      (div_le_div_of_nonneg_left (Real.exp_pos (-t)).le hx ht.le)

private lemma hasDerivAt_expIntegralTail {x : ℝ} (hx : 0 < x) :
    HasDerivAt
      (fun y : ℝ => ∫ t : ℝ in Ioi y, ((Real.exp (-t) / t : ℝ) : ℂ))
      (-((Real.exp (-x) / x : ℝ) : ℂ)) x := by
  let f : ℝ → ℂ := fun t => ((Real.exp (-t) / t : ℝ) : ℂ)
  let T : ℝ → ℂ := fun y => ∫ t : ℝ in Ioi y, f t
  have hfx : ContinuousAt f x := by
    change ContinuousAt (Complex.ofReal ∘ fun t : ℝ => Real.exp (-t) / t) x
    have hr := (Real.continuous_exp.comp continuous_neg).continuousAt.div
      continuousAt_id hx.ne'
    exact Complex.continuous_ofReal.continuousAt.comp hr
  have hfm : StronglyMeasurable f := by
    dsimp only [f]
    exact Complex.continuous_ofReal.measurable.comp
      ((Real.continuous_exp.comp continuous_neg).measurable.div measurable_id) |>.stronglyMeasurable
  have hbase : HasDerivAt (fun y => ∫ t : ℝ in x..y, f t) (f x) x :=
    intervalIntegral.integral_hasDerivAt_right (by simp)
      hfm.stronglyMeasurableAtFilter hfx
  have hG : HasDerivAt (fun y => T x - ∫ t : ℝ in x..y, f t) (-f x) x := by
    simpa only [zero_sub] using hbase.const_sub (T x)
  have heq : (fun y => T x - ∫ t : ℝ in x..y, f t) =ᶠ[𝓝 x] T := by
    filter_upwards [Ioi_mem_nhds hx] with y hy
    have hix : IntegrableOn f (Ioi x) := by
      change Integrable (fun t : ℝ => ((Real.exp (-t) / t : ℝ) : ℂ))
        (volume.restrict (Ioi x))
      exact (integrableOn_exp_neg_div_Ioi hx).ofReal
    have hiy : IntegrableOn f (Ioi y) := by
      change Integrable (fun t : ℝ => ((Real.exp (-t) / t : ℝ) : ℂ))
        (volume.restrict (Ioi y))
      exact (integrableOn_exp_neg_div_Ioi hy).ofReal
    have hrel := intervalIntegral.integral_Ioi_sub_Ioi'
      hix hiy
    change T x - T y = ∫ t : ℝ in x..y, f t at hrel
    linear_combination hrel
  simpa only [T, f] using hG.congr_of_eventuallyEq heq.symm

private lemma hasDerivAt_principalE1Raw_ofReal {x : ℝ} (hx : 0 < x) :
    HasDerivAt (fun y : ℝ => principalExponentialIntegralE1Raw y)
      (-((Real.exp (-x) / x : ℝ) : ℂ)) x := by
  let P' : ℝ → ℂ := fun y =>
    ein y - (Real.log y : ℂ) - (Real.eulerMascheroniConstant : ℂ)
  have hein0 := (differentiable_ein (x : ℂ)).hasDerivAt.comp_ofReal
  have hm := mul_deriv_ein (x : ℂ)
  rw [← Complex.ofReal_neg, ← Complex.ofReal_exp] at hm
  have hein : HasDerivAt (fun y : ℝ => ein y)
      (((1 - Real.exp (-x)) / x : ℝ) : ℂ) x := by
    apply hein0.congr_deriv
    rw [Complex.ofReal_div]
    apply (eq_div_iff (Complex.ofReal_ne_zero.mpr hx.ne')).2
    simpa only [Complex.ofReal_sub, Complex.ofReal_one, mul_comm] using hm
  have hlog := (Real.hasDerivAt_log hx.ne').ofReal_comp
  have hP' : HasDerivAt P' (-((Real.exp (-x) / x : ℝ) : ℂ)) x := by
    have hd := (hein.sub hlog).sub_const (Real.eulerMascheroniConstant : ℂ)
    apply hd.congr_deriv
    rw [← Complex.ofReal_sub, ← Complex.ofReal_neg]
    congr 1
    field_simp [hx.ne']
    ring
  have heq : P' =ᶠ[𝓝 x] fun y : ℝ => principalExponentialIntegralE1Raw y := by
    filter_upwards [Ioi_mem_nhds hx] with y hy
    dsimp only [P', principalExponentialIntegralE1Raw]
    rw [← Complex.ofReal_log hy.le]
  exact hP'.congr_of_eventuallyEq heq.symm

private lemma principalE1Raw_one_eq_expIntegralTail :
    principalExponentialIntegralE1Raw 1 =
      ∫ t : ℝ in Ioi 1, ((Real.exp (-t) / t : ℝ) : ℂ) := by
  have hein := ein_one_eq_regularized_integral
  have hgamma := Real.eulerMascheroniConstant_eq_regularized_integrals
  rw [principalExponentialIntegralE1Raw, Complex.log_one]
  linear_combination hein - hgamma

private lemma principalE1Raw_eq_expIntegralTail {x : ℝ} (hx : 0 < x) :
    principalExponentialIntegralE1Raw x =
      ∫ t : ℝ in Ioi x, ((Real.exp (-t) / t : ℝ) : ℂ) := by
  let P : ℝ → ℂ := fun y => principalExponentialIntegralE1Raw y
  let T : ℝ → ℂ := fun y => ∫ t : ℝ in Ioi y, ((Real.exp (-t) / t : ℝ) : ℂ)
  have hP : DifferentiableOn ℝ P (Ioi 0) := by
    intro y hy
    exact (hasDerivAt_principalE1Raw_ofReal hy).differentiableAt.differentiableWithinAt
  have hT : DifferentiableOn ℝ T (Ioi 0) := by
    intro y hy
    exact (hasDerivAt_expIntegralTail hy).differentiableAt.differentiableWithinAt
  have hderiv : EqOn (deriv P) (deriv T) (Ioi 0) := by
    intro y hy
    rw [(hasDerivAt_principalE1Raw_ofReal hy).deriv,
      (hasDerivAt_expIntegralTail hy).deriv]
  have heq := IsOpen.eqOn_of_deriv_eq isOpen_Ioi isPreconnected_Ioi hP hT hderiv
    (show (1 : ℝ) ∈ Ioi 0 by norm_num) principalE1Raw_one_eq_expIntegralTail
  exact heq hx

private lemma exp_mul_kernel_integral_eq_tail {x : ℝ} (hx : 0 < x) :
    (Real.exp (-x) : ℂ) *
        ∫ t : ℝ in Ioi 0, (Real.exp (-t) : ℂ) / ((t : ℂ) + x) =
      ∫ u : ℝ in Ioi x, ((Real.exp (-u) / u : ℝ) : ℂ) := by
  let f : ℝ → ℂ := fun u => ((Real.exp (-u) / u : ℝ) : ℂ)
  let g : ℝ → ℂ := fun t => ((Real.exp (-t) / (t + x) : ℝ) : ℂ)
  have hgR : IntegrableOn (fun t : ℝ => Real.exp (-t) / (t + x)) (Ioi 0) := by
    have he : IntegrableOn (fun t : ℝ => Real.exp (-t)) (Ioi 0) :=
      integrableOn_exp_neg_Ioi 0
    have hdom : IntegrableOn (fun t : ℝ => x⁻¹ * Real.exp (-t)) (Ioi 0) :=
      he.const_mul x⁻¹
    refine hdom.mono' ?_ ?_
    · exact
        ((Real.continuous_exp.comp continuous_neg).continuousOn.div
          (continuousOn_id.add continuousOn_const)
          (fun t (ht : t ∈ Ioi 0) => (hx.trans_le (le_add_of_nonneg_left ht.le)).ne'))
            |>.aestronglyMeasurable measurableSet_Ioi
    · filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
      have htx : 0 < t + x := add_pos ht hx
      simpa [Real.norm_eq_abs, abs_div, abs_of_pos (Real.exp_pos _), abs_of_pos htx,
        abs_mul, abs_of_pos (inv_pos.mpr hx), div_eq_mul_inv,
        mul_comm (x⁻¹) (Real.exp (-t))] using
          (div_le_div_of_nonneg_left (Real.exp_pos (-t)).le hx (le_add_of_nonneg_left ht.le))
  have hg : IntegrableOn g (Ioi 0) := by
    change Integrable (fun t : ℝ => ((Real.exp (-t) / (t + x) : ℝ) : ℂ))
      (volume.restrict (Ioi 0))
    exact hgR.ofReal
  have hf : IntegrableOn f (Ioi x) := by
    change Integrable (fun u : ℝ => ((Real.exp (-u) / u : ℝ) : ℂ))
      (volume.restrict (Ioi x))
    exact (integrableOn_exp_neg_div_Ioi hx).ofReal
  have hfinite (b : ℝ) :
      (Real.exp (-x) : ℂ) * ∫ t : ℝ in 0..b, g t =
        ∫ u : ℝ in x..b + x, f u := by
    calc
      (Real.exp (-x) : ℂ) * ∫ t : ℝ in 0..b, g t =
          ∫ t : ℝ in 0..b, (Real.exp (-x) : ℂ) * g t := by
            rw [intervalIntegral.integral_const_mul]
      _ = ∫ t : ℝ in 0..b, f (t + x) := by
        apply intervalIntegral.integral_congr
        intro t _
        dsimp only [f, g]
        rw [← Complex.ofReal_mul]
        congr 1
        rw [show -(t + x) = -x + -t by ring, Real.exp_add]
        ring
      _ = ∫ u : ℝ in 0 + x..b + x, f u :=
        intervalIntegral.integral_comp_add_right f x
      _ = ∫ u : ℝ in x..b + x, f u := by rw [zero_add]
  have hg_tend := intervalIntegral_tendsto_integral_Ioi 0 hg tendsto_id
  have hleft : Tendsto
      (fun b : ℝ => (Real.exp (-x) : ℂ) * ∫ t : ℝ in 0..b, g t) atTop
      (𝓝 ((Real.exp (-x) : ℂ) * ∫ t : ℝ in Ioi 0, g t)) :=
    tendsto_const_nhds.mul hg_tend
  have hb : Tendsto (fun b : ℝ => b + x) atTop atTop :=
    tendsto_atTop_add_const_right atTop x tendsto_id
  have hright := intervalIntegral_tendsto_integral_Ioi x hf hb
  have hright' : Tendsto
      (fun b : ℝ => (Real.exp (-x) : ℂ) * ∫ t : ℝ in 0..b, g t) atTop
      (𝓝 (∫ u : ℝ in Ioi x, f u)) := by
    apply hright.congr'
    exact Eventually.of_forall fun b => (hfinite b).symm
  have hlim := tendsto_nhds_unique hleft hright'
  have hkernel :
      (fun t : ℝ => (Real.exp (-t) : ℂ) / ((t : ℂ) + x)) = g := by
    funext t
    dsimp only [g]
    rw [← Complex.ofReal_add, ← Complex.ofReal_div]
  rw [hkernel]
  simpa only [f] using hlim

theorem euler_constant_normalization (x : ℝ) (hx : 0 < x) :
    principalExponentialIntegralE1 (x : ℂ)
        (Complex.ofReal_ne_zero.mpr hx.ne') =
      Complex.exp (-(x : ℂ)) *
        ∫ t : ℝ in Ioi 0, (Real.exp (-t) : ℂ) / ((t : ℂ) + x) := by
  rw [principalExponentialIntegralE1_eq_raw]
  rw [← Complex.ofReal_neg, ← Complex.ofReal_exp]
  rw [exp_mul_kernel_integral_eq_tail hx]
  exact principalE1Raw_eq_expIntegralTail hx

end Complex
