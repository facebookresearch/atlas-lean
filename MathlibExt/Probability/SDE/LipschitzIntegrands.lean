/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import MathlibExt.Probability.ItoIntegralProperties
import Mathlib.Tactic.Finiteness

/-!
# Lipschitz composition of square-integrable stochastic integrands

A globally Lipschitz scalar map contracts the existing squared integrand distance
by the square of its Lipschitz constant. On a finite measure space its nonzero
constant offset also preserves finite energy. Progressive inputs therefore give
actual Itô-approximable composed integrands, and the difference isometry yields
the corresponding estimate for actual stochastic integrals.

These are the composition estimates used in the classical Lipschitz SDE proof:
Le Gall, *Brownian Motion, Martingales, and Stochastic Calculus* (2016), Theorem 8.3.
No completeness or continuity assumption on a filtration is needed here.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Set
open scoped NNReal ENNReal

namespace ProbabilityTheory

/-- Lipschitz composition bounds squared integrand distance by the squared
Lipschitz constant, without measurability or finiteness assumptions on the inputs. -/
theorem integrandDist_comp_lipschitz_le {Ω : Type*} [MeasurableSpace Ω]
    {f : ℝ → ℝ} {K : ℝ≥0} (hf : LipschitzWith K f) (P : Measure Ω)
    (X Y : ℝ≥0 → Ω → ℝ) (t : ℝ≥0) :
    integrandDist P (fun s ω ↦ f (X s ω)) (fun s ω ↦ f (Y s ω)) t ≤
      (K : ℝ≥0∞)^2 * integrandDist P X Y t := by
  have hp (x y : ℝ) : ‖f x - f y‖ₑ^2 ≤ (K : ℝ≥0∞)^2 * ‖x-y‖ₑ^2 := by
    have hd : ‖f x-f y‖ₑ ≤ (K : ℝ≥0∞) * ‖x-y‖ₑ := by
      simpa only [Real.eNorm_eq_ofReal_abs, edist_dist, Real.dist_eq] using hf.edist_le_mul x y
    simpa only [mul_pow] using pow_le_pow_left' hd 2
  unfold integrandDist
  calc
    _ ≤ ∫⁻ ω, (∫⁻ s in Ioc (0 : ℝ) t,
        (K : ℝ≥0∞)^2 * ‖X s.toNNReal ω-Y s.toNNReal ω‖ₑ^2) ∂P :=
      lintegral_mono fun ω ↦ lintegral_mono fun s ↦ hp _ _
    _ = _ := by
      simp_rw [lintegral_const_mul' _ _ (by simp : (K : ℝ≥0∞)^2 ≠ ∞)]

/-- On a finite measure space, Lipschitz composition preserves finite integrand
energy, including scalar maps which do not vanish at zero. -/
theorem integrandDist_comp_zero_ne_top {Ω : Type*} {mΩ : MeasurableSpace Ω}
    {P : Measure Ω} [IsFiniteMeasure P] {F : Filtration ℝ≥0 mΩ}
    {X : ℝ≥0 → Ω → ℝ} (hX : IsProgressive F X)
    {f : ℝ → ℝ} {K : ℝ≥0} (hf : LipschitzWith K f) (t : ℝ≥0)
    (hX2 : integrandDist P X (fun _ _ ↦ 0) t ≠ ∞) :
    integrandDist P (fun s ω ↦ f (X s ω)) (fun _ _ ↦ 0) t ≠ ∞ := by
  have hfirst : integrandDist P (fun s ω ↦ f (X s ω)) (fun _ _ ↦ f 0) t ≠ ∞ :=
    ne_top_of_le_ne_top (ENNReal.mul_ne_top (by simp) hX2)
      (integrandDist_comp_lipschitz_le hf P X (fun _ _ ↦ 0) t)
  have hconst : integrandDist P (fun _ _ ↦ 0) (fun _ _ ↦ f 0) t ≠ ∞ := by
    simp only [integrandDist, zero_sub, eNorm_neg, lintegral_const,
      Measure.restrict_apply_univ, Real.volume_Ioc]
    finiteness
  exact ne_top_of_le_ne_top
    (ENNReal.add_ne_top.mpr ⟨ENNReal.mul_ne_top (by norm_num) hfirst,
      ENNReal.mul_ne_top (by norm_num) hconst⟩)
    (integrandDist_le (P := P) (X := fun s ω ↦ f (X s ω)) (Y := fun _ _ ↦ 0)
      (Z := fun _ _ ↦ f 0)
      (hf.continuous.measurable.comp (IsProgressive.measurable_toNNReal hX))
      measurable_const measurable_const t)

/-- A progressive finite-energy process remains Itô-approximable after a
globally Lipschitz scalar composition, without assuming the scalar map fixes zero. -/
theorem isItoApproximable_comp_lipschitz {Ω : Type*} {mΩ : MeasurableSpace Ω}
    {P : Measure Ω} [IsFiniteMeasure P] {F : Filtration ℝ≥0 mΩ}
    {X : ℝ≥0 → Ω → ℝ} (hX : IsProgressive F X)
    {f : ℝ → ℝ} {K : ℝ≥0} (hf : LipschitzWith K f) (t : ℝ≥0)
    (hX2 : integrandDist P X (fun _ _ ↦ 0) t ≠ ∞) :
    IsItoApproximable P F (fun s ω ↦ f (X s ω)) t := by
  apply isItoApproximable_of_isProgressive (fun s ↦ hf.continuous.measurable.comp (hX s)) t
  simpa only [integrandDist, sub_zero] using integrandDist_comp_zero_ne_top hX hf t hX2

/-- The actual stochastic integrals of two Lipschitz-composed progressive
finite-energy processes satisfy the squared Lipschitz difference bound.
Only pre-Brownian laws and independence from the past are needed. -/
theorem lintegral_itoIntegral_sub_comp_lipschitz_le
    {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω}
    {F : Filtration ℝ≥0 mΩ} {B : ℝ≥0 → Ω → ℝ}
    (hB : IsPreBrownianReal B P) (hBF : Adapted F B)
    (hInd : ∀ s t, s ≤ t →
      Indep (MeasurableSpace.comap (fun ω ↦ B t ω - B s ω) inferInstance) (F s) P)
    {X Y : ℝ≥0 → Ω → ℝ} (hX : IsProgressive F X) (hY : IsProgressive F Y)
    {f : ℝ → ℝ} {K : ℝ≥0} (hf : LipschitzWith K f) (t : ℝ≥0)
    (hX2 : integrandDist P X (fun _ _ ↦ 0) t ≠ ∞)
    (hY2 : integrandDist P Y (fun _ _ ↦ 0) t ≠ ∞) :
    ∫⁻ ω, ‖itoIntegral P F B (fun s ω ↦ f (X s ω)) t ω -
      itoIntegral P F B (fun s ω ↦ f (Y s ω)) t ω‖ₑ^2 ∂P ≤
        (K : ℝ≥0∞)^2 * integrandDist P X Y t := by
  have := hB.isGaussianProcess.isProbabilityMeasure
  have hfx : IsProgressive F (fun s ω ↦ f (X s ω)) :=
    fun s ↦ hf.continuous.measurable.comp (hX s)
  have hfy : IsProgressive F (fun s ω ↦ f (Y s ω)) :=
    fun s ↦ hf.continuous.measurable.comp (hY s)
  have hx : ∫⁻ ω, (∫⁻ s in Ioc (0 : ℝ) t, ‖f (X s.toNNReal ω)‖ₑ^2) ∂P ≠ ∞ := by
    simpa only [integrandDist, sub_zero] using integrandDist_comp_zero_ne_top hX hf t hX2
  have hy : ∫⁻ ω, (∫⁻ s in Ioc (0 : ℝ) t, ‖f (Y s.toNNReal ω)‖ₑ^2) ∂P ≠ ∞ := by
    simpa only [integrandDist, sub_zero] using integrandDist_comp_zero_ne_top hY hf t hY2
  rw [(itoIntegral_isometry_sub_of_isPreBrownianReal hB hBF hInd hfx hfy t hx hy).2]
  exact integrandDist_comp_lipschitz_le hf P X Y t

end ProbabilityTheory
