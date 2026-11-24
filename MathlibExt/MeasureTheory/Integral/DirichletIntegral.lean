/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.MeasureTheory.Integral.IntervalIntegral.IntegrationByParts
import Mathlib.Tactic.FunProp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

public section

open Filter Set MeasureTheory
open scoped Topology Interval

namespace MathlibExt.MeasureTheory.Integral.ImproperIntegralAbsoluteConditionalWanted

/-!
Conditional convergence of an improper integral on `[a, ∞)`: every finite
truncation is interval-integrable and the proper integrals over `[a, b]`
converge as `b → ∞`, but `f` is not Lebesgue integrable on `(a, ∞)`.

Sources:
- Mathlib `docs/undergrad.yaml`, section "Single Variable Real Analysis / Integration",
  entry "absolute vs conditional convergence of improper integrals"
  (linked there to the Wikipedia article below).
- T. Apostol, *Mathematical Analysis*, 2nd ed., Exercise 10.9(b) with $p=1$
  (improper convergence without Lebesgue integrability).
- https://en.wikipedia.org/wiki/Conditional_convergence
-/

private theorem tendsto_integral_div_of_bounded_primitive {v d : ℝ → ℝ}
    (hv : ∀ x, HasDerivAt v (d x) x) (hd : Continuous d) (hbound : ∀ x, ‖v x‖ ≤ 1) :
    ∃ L : ℝ, Tendsto (fun b ↦ ∫ x in (1 : ℝ)..b, d x / x) atTop (𝓝 L) := by
  let r (x : ℝ) := -(x ^ 2)⁻¹ * v x
  have hint : IntegrableOn (fun x : ℝ ↦ (x ^ 2)⁻¹) (Ioi 1) := by
    refine (integrableOn_Ioi_rpow_of_lt (a := -2) (by norm_num) zero_lt_one).congr_fun ?_
      measurableSet_Ioi
    intro x hx
    have hxp : 0 ≤ x := zero_le_one.trans hx.le
    change x ^ (-(2 : ℝ)) = (x ^ (2 : ℕ))⁻¹
    rw [Real.rpow_neg hxp]
    simpa only [Nat.cast_ofNat] using congrArg Inv.inv (Real.rpow_natCast x 2)
  have hvc : Continuous v := continuous_iff_continuousAt.mpr fun x ↦ (hv x).continuousAt
  have hr : IntegrableOn r (Ioi 1) := by
    apply hint.mono'
    · exact ((measurable_id.pow_const _).inv.neg.mul hvc.measurable).aestronglyMeasurable
    · filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
      change ‖-(x ^ 2)⁻¹ * v x‖ ≤ (x ^ 2)⁻¹
      have hnonneg : 0 ≤ (x ^ 2)⁻¹ := by positivity
      rw [norm_mul, norm_neg, Real.norm_of_nonneg hnonneg]
      simpa only [mul_one] using mul_le_mul_of_nonneg_left (hbound x) hnonneg
  have hbdy : Tendsto (fun b : ℝ ↦ b⁻¹ * v b) atTop (𝓝 0) := by
    refine squeeze_zero_norm' ?_ (tendsto_inv_atTop_zero (𝕜 := ℝ))
    filter_upwards [eventually_ge_atTop (1 : ℝ)] with b hb
    have hb0 : 0 ≤ b⁻¹ := inv_nonneg.mpr (zero_le_one.trans hb)
    rw [norm_mul, Real.norm_of_nonneg hb0]
    simpa only [mul_one] using mul_le_mul_of_nonneg_left (hbound b) hb0
  have hparts (b : ℝ) (hb : 1 ≤ b) :
      (∫ x in (1 : ℝ)..b, d x / x) = b⁻¹ * v b - (1 : ℝ)⁻¹ * v 1 -
        ∫ x in (1 : ℝ)..b, r x := by
    have hxpos (x : ℝ) (hx : x ∈ [[(1 : ℝ), b]]) : 0 < x := by
      rw [uIcc_of_le hb] at hx
      exact zero_lt_one.trans_le hx.1
    have hpowc : ContinuousOn (fun x : ℝ ↦ -(x ^ 2)⁻¹) [[(1 : ℝ), b]] := by
      apply ContinuousOn.neg
      exact ((continuous_id.pow 2).continuousOn.inv₀ fun x hx ↦
        pow_ne_zero _ (hxpos x hx).ne')
    simpa only [div_eq_mul_inv, mul_comm (d _) (_⁻¹), r] using
      intervalIntegral.integral_mul_deriv_eq_deriv_mul
        (fun x hx ↦ hasDerivAt_inv (hxpos x hx).ne') (fun x _ ↦ hv x)
        hpowc.intervalIntegrable (hd.intervalIntegrable (1 : ℝ) b)
  refine ⟨0 - (1 : ℝ)⁻¹ * v 1 - ∫ x in Ioi (1 : ℝ), r x, ?_⟩
  have hlim := (hbdy.sub_const ((1 : ℝ)⁻¹ * v 1)).sub
    (intervalIntegral_tendsto_integral_Ioi 1 hr tendsto_id)
  apply hlim.congr'
  filter_upwards [eventually_ge_atTop (1 : ℝ)] with b hb
  exact (hparts b hb).symm

/-- **Conditional convergence of the Dirichlet integral on $[1, \infty)$.** The function
$x \mapsto \sin x / x$ is interval integrable on $[1, b]$ for every real $b \ge 1$, the integrals
$\int_1^b \frac{\sin x}{x}\,dx$ converge to a real limit as $b \to \infty$, and $\sin x / x$ is
not Lebesgue integrable on $(1, \infty)$.

Sources:
- Mathlib `docs/undergrad.yaml`, section "Single Variable Real Analysis / Integration",
  entry "absolute vs conditional convergence of improper integrals"
  (linked there to an exposition).
- W. Rudin, *Principles of Mathematical Analysis*, 3rd ed., Ch. 6, Exercise 9
  (integration by parts and conditional convergence).
- T. Apostol, *Mathematical Analysis*, 2nd ed., Exercise 10.9(b) with $p=1$
  (improper convergence without Lebesgue integrability).
-/
theorem dirichlet_integral_conditionally_convergent :
    (∀ b : ℝ, 1 ≤ b → IntervalIntegrable (fun x ↦ Real.sin x / x) volume 1 b) ∧
      (∃ L : ℝ, Tendsto (fun b ↦ ∫ x in (1 : ℝ)..b, Real.sin x / x) atTop (nhds L)) ∧
      ¬ Integrable (fun x ↦ Real.sin x / x) (volume.restrict (Ioi 1)) := by
  refine ⟨?_, ?_, ?_⟩
  · intro b hb
    apply ContinuousOn.intervalIntegrable
    apply Real.continuous_sin.continuousOn.div continuous_id.continuousOn
    intro x hx
    rw [uIcc_of_le hb] at hx
    exact (zero_lt_one.trans_le hx.1).ne'
  · refine tendsto_integral_div_of_bounded_primitive (v := fun x ↦ -Real.cos x)
      (fun x ↦ ?_) Real.continuous_sin (fun x ↦ ?_)
    · simpa only [neg_neg] using (Real.hasDerivAt_cos x).fun_neg
    · simpa only [norm_neg, Real.norm_eq_abs] using Real.abs_cos_le_one x
  · -- Absolute integrability would also give integrability of the squared sine weight.
    intro habs
    have hsq : IntegrableOn (fun x : ℝ ↦ Real.sin x ^ 2 / x) (Ioi 1) := by
      refine habs.mono ?_ ?_
      · exact ((Real.continuous_sin.measurable.pow_const _).div measurable_id).aestronglyMeasurable
      · filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
        have hx0 : 0 < x := zero_lt_one.trans hx
        rw [Real.norm_of_nonneg (div_nonneg (sq_nonneg _) hx0.le), Real.norm_eq_abs,
          abs_div, abs_of_pos hx0]
        apply div_le_div_of_nonneg_right _ hx0.le
        calc
          Real.sin x ^ 2 = |Real.sin x| ^ 2 := (sq_abs _).symm
          _ ≤ |Real.sin x| := by nlinarith [abs_nonneg (Real.sin x), Real.abs_sin_le_one x]
    obtain ⟨L, hcos⟩ := tendsto_integral_div_of_bounded_primitive
      (v := fun x : ℝ ↦ Real.sin (2 * x) / 2) (d := fun x : ℝ ↦ Real.cos (2 * x))
      (fun x ↦ by
        have hlin : HasDerivAt (fun y : ℝ ↦ 2 * y) 2 x := by
          simpa using (hasDerivAt_id x).const_mul 2
        convert (((Real.hasDerivAt_sin (2 * x)).comp x hlin).div_const 2) using 1
        · rfl
        · ring) (by fun_prop) (fun x ↦ by
        rw [Real.norm_eq_abs, abs_div, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2)]
        linarith [Real.abs_sin_le_one (2 * x)])
    -- Adding the double-angle oscillation isolates the divergent logarithmic integral.
    have hsqLim := intervalIntegral_tendsto_integral_Ioi 1 hsq tendsto_id
    have hlim := (hsqLim.const_mul (2 : ℝ)).add hcos
    have hlog : Tendsto Real.log atTop
        (𝓝 (2 * (∫ x in Ioi (1 : ℝ), Real.sin x ^ 2 / x) + L)) := by
      apply hlim.congr'
      filter_upwards [eventually_ge_atTop (1 : ℝ)] with b hb
      have hxpos (x : ℝ) (hx : x ∈ [[(1 : ℝ), b]]) : 0 < x := by
        rw [uIcc_of_le hb] at hx
        exact zero_lt_one.trans_le hx.1
      have hsinI : IntervalIntegrable (fun x : ℝ ↦ 2 * (Real.sin x ^ 2 / x)) volume 1 b := by
        apply ContinuousOn.intervalIntegrable
        exact continuousOn_const.mul ((Real.continuous_sin.pow 2).continuousOn.div
          continuous_id.continuousOn (fun x hx ↦ (hxpos x hx).ne'))
      have hcosI : IntervalIntegrable (fun x : ℝ ↦ Real.cos (2 * x) / x) volume 1 b := by
        apply ContinuousOn.intervalIntegrable
        exact (show Continuous (fun x : ℝ ↦ Real.cos (2 * x)) by fun_prop).continuousOn.div
          continuous_id.continuousOn (fun x hx ↦ (hxpos x hx).ne')
      calc
        _ = ∫ x in (1 : ℝ)..b, 2 * (Real.sin x ^ 2 / x) + Real.cos (2 * x) / x := by
          rw [intervalIntegral.integral_add hsinI hcosI, intervalIntegral.integral_const_mul]
          rfl
        _ = ∫ x in (1 : ℝ)..b, x⁻¹ := by
          apply intervalIntegral.integral_congr
          intro x _
          change 2 * (Real.sin x ^ 2 / x) + Real.cos (2 * x) / x = x⁻¹
          rw [Real.cos_two_mul_eq_one_sub]
          ring
        _ = Real.log b := by
          rw [integral_inv_of_pos zero_lt_one (zero_lt_one.trans_le hb), div_one]
    exact not_tendsto_atTop_of_tendsto_nhds hlog Real.tendsto_log_atTop

end MathlibExt.MeasureTheory.Integral.ImproperIntegralAbsoluteConditionalWanted
