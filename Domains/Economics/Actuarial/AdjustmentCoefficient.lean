/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Probability.Moments.Basic
import Mathlib.Probability.Moments.MGFAnalytic
import Mathlib.Analysis.Convex.Deriv
import Mathlib.Analysis.Convex.Slope

/-!
# The adjustment coefficient

For a claim size `X`, arrival rate `λ` and premium rate `c`, the adjustment equation is
`λ (M(R) - 1) = c R`, where `M` is the moment-generating function of `X`. Zero always solves
this equation. The adjustment coefficient is the **positive** solution.

Kaas, Goovaerts, Dhaene and Denuit, *Modern Actuarial Risk Theory*, recap of chapters 1–6,
“Ruin theory” (sheet 2), give the equation in terms of the premium loading. Here we locate
the root using an integrable exponential moment at a single positive endpoint: below it the
second derivative of `M` is `E[X² exp(rX)]`, while continuity at the endpoint itself follows
by domination, not differentiation.
-/

open MeasureTheory ProbabilityTheory Real Set Filter
open scoped Topology

namespace Actuarial

variable {Ω : Type*} [MeasurableSpace Ω] {X : Ω → ℝ} {μ : Measure Ω} {rate c r₀ : ℝ}

/-- The left side minus the right side of the adjustment equation at exponent `r`.
Its interpretation as an expectation requires an integrable exponential moment at `r`. -/
@[expose] public noncomputable def adjustmentGap (X : Ω → ℝ) (μ : Measure Ω) (rate c r : ℝ) : ℝ :=
  rate * (mgf X μ r - 1) - c * r

/-- For a nonnegative claim the endpoint exponential dominates all earlier exponentials,
including those with negative exponents. -/
private theorem mgf_on_Iic_of_nonneg (hr₀ : 0 < r₀) (hn : ∀ᵐ ω ∂μ, 0 ≤ X ω)
    (hint : Integrable (fun ω ↦ exp (r₀ * X ω)) μ) :
    Iic r₀ ⊆ integrableExpSet X μ ∧ ContinuousOn (mgf X μ) (Iic r₀) := by
  have hX := aemeasurable_of_aemeasurable_exp_mul hr₀.ne' hint.aemeasurable
  have hm (r : ℝ) : AEStronglyMeasurable (fun ω ↦ exp (r * X ω)) μ := by fun_prop
  have hb (r : ℝ) (hr : r ∈ Iic r₀) : ∀ᵐ ω ∂μ, ‖exp (r * X ω)‖ ≤ exp (r₀ * X ω) := by
    filter_upwards [hn] with ω hω
    rw [Real.norm_of_nonneg (exp_pos _).le, exp_le_exp]
    exact mul_le_mul_of_nonneg_right hr hω
  exact ⟨fun r hr ↦ hint.mono' (hm r) (hb r hr),
    continuousOn_of_dominated (fun r _ ↦ hm r) hb hint (.of_forall fun ω ↦ by fun_prop)⟩

private theorem strictConvexOn_adjustmentGap (hrate : 0 < rate) (hp : 0 < μ {ω | 0 < X ω})
    (hdom : Iic r₀ ⊆ integrableExpSet X μ) (hc : ContinuousOn (mgf X μ) (Iic r₀)) :
    StrictConvexOn ℝ (Iic r₀) (adjustmentGap X μ rate c) := by
  have hM : StrictConvexOn ℝ (Iic r₀) (mgf X μ) := by
    apply strictConvexOn_of_deriv2_pos (convex_Iic _) hc
    intro r hr
    have hri := interior_mono hdom hr
    rw [← iteratedDeriv_eq_iterate, iteratedDeriv_mgf hri]
    apply (integral_pos_iff_support_of_nonneg (fun ω ↦ mul_nonneg (sq_nonneg _) (exp_pos _).le)
      (integrable_pow_mul_exp_of_mem_interior_integrableExpSet hri 2)).2
    apply hp.trans_le (measure_mono ?_)
    intro ω hω
    exact mul_ne_zero (pow_ne_zero _ (ne_of_gt hω)) (exp_pos _).ne'
  refine ⟨hM.1, ?_⟩
  intro x hx y hy hxy a b ha hb hab
  have hlt := mul_lt_mul_of_pos_left (hM.2 hx hy hxy ha hb hab) hrate
  simp only [smul_eq_mul, adjustmentGap] at hlt ⊢
  linear_combination hlt + rate * hab

/-- For nonnegative claims with positive probability of a positive claim, suppose `rate > 0`
and the premium rate `c` exceeds `rate * E[X]`. If the exponential moment is integrable at
`r₀ > 0` and the adjustment gap there is positive, the equation has exactly one root `R` in
`(0, r₀)`. The gap is negative on `(0, R)` and positive on `(R, r₀]`. -/
public theorem exists_adjustmentCoefficient [IsProbabilityMeasure μ]
    (hn : ∀ᵐ ω ∂μ, 0 ≤ X ω) (hp : 0 < μ {ω | 0 < X ω}) (hrate : 0 < rate)
    (hprofit : rate * (∫ ω, X ω ∂μ) < c) (hr₀ : 0 < r₀)
    (hint : Integrable (fun ω ↦ exp (r₀ * X ω)) μ) (hcross : 0 < adjustmentGap X μ rate c r₀) :
    ∃ R ∈ Ioo 0 r₀, adjustmentGap X μ rate c R = 0 ∧
      (∀ s ∈ Ioo 0 r₀, adjustmentGap X μ rate c s = 0 → s = R) ∧
      (∀ s ∈ Ioo 0 R, adjustmentGap X μ rate c s < 0) ∧
      (∀ s ∈ Ioc R r₀, 0 < adjustmentGap X μ rate c s) := by
  let h := adjustmentGap X μ rate c
  obtain ⟨hdom, hM⟩ := mgf_on_Iic_of_nonneg hr₀ hn hint
  have hzero : h 0 = 0 := by simp [h, adjustmentGap]
  have h₀ : 0 ∈ interior (integrableExpSet X μ) :=
    interior_mono hdom (by simpa only [interior_Iic, mem_Iio] using hr₀)
  have hM' : HasDerivAt (mgf X μ) (∫ ω, X ω ∂μ) 0 := by simpa using hasDerivAt_mgf h₀
  have hd : HasDerivAt h (rate * (∫ ω, X ω ∂μ) - c) 0 := by
    change HasDerivAt (fun r ↦ rate * (mgf X μ r - 1) - c * r) _ _
    simpa using (((hM'.sub_const 1).const_mul rate).fun_sub ((hasDerivAt_id (0 : ℝ)).const_mul c))
  -- Find a point strictly to the right of zero with negative gap.
  have hneg : ∀ᶠ r in 𝓝[>] (0 : ℝ), h r < 0 := by
    filter_upwards [hd.tendsto_slope_zero_right.eventually_lt_const (sub_neg.mpr hprofit),
      self_mem_nhdsWithin] with r hs (hr : 0 < r)
    simp only [zero_add, hzero, sub_zero, smul_eq_mul] at hs
    exact lt_of_not_ge fun hnn ↦ hs.not_ge (mul_nonneg (inv_pos.mpr hr).le hnn)
  have hnear : ∀ᶠ r in 𝓝[>] (0 : ℝ), r ∈ Ioo 0 r₀ := Ioo_mem_nhdsGT hr₀
  obtain ⟨a, ⟨ha, har⟩, han⟩ := (hnear.and hneg).exists
  have hcont : ContinuousOn h (Iic r₀) :=
    (continuousOn_const.mul (hM.sub continuousOn_const)).sub
      (continuousOn_const.mul continuous_id.continuousOn)
  obtain ⟨R, haR, hR⟩ := intermediate_value_Ioo har.le
    (hcont.mono (Icc_subset_Iic_self : Icc a r₀ ⊆ Iic r₀)) ⟨han, hcross⟩
  have hRpos : 0 < R := ha.trans haR.1
  have hconv : StrictConvexOn ℝ (Iic r₀) h := strictConvexOn_adjustmentGap hrate hp hdom hM
  -- Secants from zero have strictly increasing slope; the secant to R has slope zero.
  have left (s : ℝ) (hs : s ∈ Ioo 0 R) : h s < 0 := by
    have hlt := hconv.secant_strict_mono_aux2 hr₀.le haR.2.le hs.1 hs.2
    have hslope : h s / s < 0 := by simpa [hzero, hR] using hlt
    simpa using (div_lt_iff₀ hs.1).mp hslope
  have right (s : ℝ) (hs : s ∈ Ioc R r₀) : 0 < h s := by
    have hlt := hconv.secant_strict_mono_aux2 hr₀.le hs.2 hRpos hs.1
    simpa [hzero, hR, div_pos_iff_of_pos_right (hRpos.trans hs.1)] using hlt
  refine ⟨R, ⟨hRpos, haR.2⟩, hR, ?_, left, right⟩
  intro s hs hz
  rcases lt_trichotomy s R with hlt | heq | hgt
  · exact ((left s ⟨hs.1, hlt⟩).ne hz).elim
  · exact heq
  · exact ((right s ⟨hgt, hs.2.le⟩).ne' hz).elim

end Actuarial
