/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Author: @toskua
-/
module

public import Mathlib.Analysis.Complex.MeanValue
public import Mathlib.Analysis.Calculus.FDeriv.Analytic
public import Mathlib.Analysis.SpecialFunctions.PolarCoord
public import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
public import Mathlib.MeasureTheory.Integral.Prod
public import Mathlib.MeasureTheory.Function.LocallyIntegrable

/-!
# Circle and disk area means at zero

For a scalar complex function analytic on the closed disk centered at zero
with positive radius `r`, integrating its circle values over the open angle
interval `(-π,π)` gives `2π • f(0)`. Integrating over the open disk with
planar Lebesgue volume gives `π r² • f(0)`. The disk is open in the area
integral and closed in the analyticity hypothesis; no normalization of the
Lebesgue measure is inserted.
-/

@[expose] public section
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open MeasureTheory Complex Metric Real Set
open scoped Topology

namespace AnalyticL2

/-- The analytic circle mean over the open angle interval `(-π,π)` is `2π` times the value at zero.

```lean
theorem circle_integral_symmetric (f : ℂ → ℂ) (r : ℝ) (hr : 0 < r)
    (hf : AnalyticOn ℂ f (closedBall 0 r)) :
    (∫ θ in Ioo (-Real.pi) Real.pi, f (circleMap 0 r θ)) =
      (2 * Real.pi) • f 0
``` -/
theorem circle_integral_symmetric (f : ℂ → ℂ) (r : ℝ) (hr : 0 < r)
    (hf : AnalyticOn ℂ f (closedBall 0 r)) :
    (∫ θ in Ioo (-Real.pi) Real.pi, f (circleMap 0 r θ)) =
      (2 * Real.pi) • f 0 := by
  have hd : DifferentiableOn ℂ f (closure (ball 0 |r|)) := by
    simpa only [abs_of_pos hr, closure_ball (0 : ℂ) hr.ne'] using hf.differentiableOn
  have hm : circleAverage f 0 r = f 0 := hd.diffContOnCl.circleAverage
  rw [circleAverage_eq_integral_add (-Real.pi)] at hm
  rw [intervalIntegral.integral_comp_add_right (fun θ => f (circleMap 0 r θ))] at hm
  have hs := congrArg (fun z : ℂ => (2 * Real.pi) • z) hm
  have ha : 2 * Real.pi + -Real.pi = Real.pi := by ring
  simpa only [zero_add, ha, smul_smul,
    mul_inv_cancel₀ (by positivity : (2 * Real.pi : ℝ) ≠ 0), one_smul,
    intervalIntegral.integral_of_le (by linarith [Real.pi_pos] : -Real.pi ≤ Real.pi),
    integral_Ioc_eq_integral_Ioo] using hs

/-- The planar volume integral over the open zero-centered disk is its area `πr²` times the
analytic center value.

```lean
theorem integral_ball_zero (f : ℂ → ℂ) (r : ℝ) (hr : 0 < r)
    (hf : AnalyticOn ℂ f (closedBall 0 r)) :
    (∫ z in ball (0 : ℂ) r, f z) = (Real.pi * r ^ 2) • f 0
``` -/
theorem integral_ball_zero (f : ℂ → ℂ) (r : ℝ) (hr : 0 < r)
    (hf : AnalyticOn ℂ f (closedBall 0 r)) :
    (∫ z in ball (0 : ℂ) r, f z) = (Real.pi * r ^ 2) • f 0 := by
  let rectangle : Set (ℝ × ℝ) := Ioo 0 r ×ˢ Ioo (-Real.pi) Real.pi
  let h : ℝ × ℝ → ℂ := fun p => p.1 • f (Complex.polarCoord.symm p)
  have hp : Continuous (Complex.polarCoord.symm : ℝ × ℝ → ℂ) := by
    have hfun : (Complex.polarCoord.symm : ℝ × ℝ → ℂ) =
        (fun p => p.1 * (Real.cos p.2 + Real.sin p.2 * Complex.I)) := by
      funext p
      exact Complex.polarCoord_symm_apply p
    rw [hfun]
    fun_prop
  have hfrect : ContinuousOn h (Icc 0 r ×ˢ Icc (-Real.pi) Real.pi) := by
    apply continuous_fst.continuousOn.smul
    apply hf.continuousOn.comp hp.continuousOn
    intro p hpRect
    rw [mem_closedBall_zero_iff, Complex.norm_polarCoord_symm, abs_of_nonneg hpRect.1.1]
    exact hpRect.1.2
  have hint : IntegrableOn h rectangle := by
    exact (hfrect.integrableOn_compact (isCompact_Icc.prod isCompact_Icc)).mono_set
      (prod_mono Ioo_subset_Icc_self Ioo_subset_Icc_self)
  have hpolar : (∫ z in ball (0 : ℂ) r, f z) = ∫ p in rectangle, h p := by
    rw [← integral_indicator isOpen_ball.measurableSet,
      ← Complex.integral_comp_polarCoord_symm]
    change (∫ p in Ioi (0 : ℝ) ×ˢ Ioo (-Real.pi) Real.pi,
        p.1 • (ball (0 : ℂ) r).indicator f (Complex.polarCoord.symm p)) =
      ∫ p in Ioo (0 : ℝ) r ×ˢ Ioo (-Real.pi) Real.pi, h p
    rw [← integral_indicator (isOpen_Ioi.prod isOpen_Ioo).measurableSet,
      ← integral_indicator (isOpen_Ioo.prod isOpen_Ioo).measurableSet]
    apply integral_congr_ae
    filter_upwards with p
    by_cases hp0 : 0 < p.1
    · by_cases hpr : p.1 < r
      · by_cases hpθ : p.2 ∈ Ioo (-Real.pi) Real.pi
        · simp [rectangle, h, Complex.polarCoord_target, hp0, hpr, hpθ,
            mem_ball_zero_iff, Complex.norm_polarCoord_symm, abs_of_pos hp0]
        · simp [rectangle, h, Complex.polarCoord_target, hpθ]
      · simp [rectangle, h, Complex.polarCoord_target, hp0, hpr,
          mem_ball_zero_iff, Complex.norm_polarCoord_symm, abs_of_pos hp0]
    · simp [rectangle, h, Complex.polarCoord_target, hp0]
  rw [hpolar]
  have hintProd : IntegrableOn h rectangle (volume.prod volume) := by
    simpa only [Measure.volume_eq_prod] using hint
  change (∫ p in Ioo (0 : ℝ) r ×ˢ Ioo (-Real.pi) Real.pi, h p) =
    (Real.pi * r ^ 2) • f 0
  rw [Measure.volume_eq_prod, setIntegral_prod _ hintProd]
  have hs (ρ : ℝ) (hρ : ρ ∈ Ioo 0 r) :
      (∫ θ in Ioo (-Real.pi) Real.pi, h (ρ, θ)) = ρ • ((2 * Real.pi) • f 0) := by
    rw [show (fun θ => h (ρ, θ)) = (fun θ => ρ • f (circleMap 0 ρ θ)) by
      funext θ; simp [h, circleMap_zero, Complex.polarCoord_symm_apply,
        Complex.exp_mul_I, mul_add]]
    rw [integral_smul]
    exact congrArg (fun z : ℂ => ρ • z) <| circle_integral_symmetric f ρ hρ.1
      (hf.mono (closedBall_subset_closedBall hρ.2.le))
  rw [setIntegral_congr_fun measurableSet_Ioo hs, integral_smul_const]
  have hi : (∫ ρ in Ioo (0 : ℝ) r, ρ) = r ^ 2 / 2 := by
    rw [← integral_Ioc_eq_integral_Ioo, ← intervalIntegral.integral_of_le hr.le,
      integral_id, zero_pow (by norm_num : 2 ≠ 0), sub_zero]
  rw [hi, smul_smul]
  congr 1
  ring

end AnalyticL2

end
