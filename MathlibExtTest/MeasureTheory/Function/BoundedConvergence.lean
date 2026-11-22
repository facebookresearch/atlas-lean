/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.MeasureTheory.Function.BoundedConvergence
public import Mathlib.Analysis.SpecificLimits.Basic
public import Mathlib.MeasureTheory.Measure.Dirac.Def
public import Mathlib.MeasureTheory.Measure.Dirac.Basic

@[expose] public section

open MeasureTheory Filter Topology

namespace MathlibExtTest.MeasureTheory.Function.BoundedConvergence

/-- The bounded convergence theorem restates with the exact public signature. -/
example {α : Type*} {m : MeasurableSpace α} {μ : Measure α} [IsFiniteMeasure μ]
    {G : Type*} [NormedAddCommGroup G] [NormedSpace ℝ G]
    {F : ℕ → α → G} {f : α → G} {C : ℝ}
    (hF_meas : ∀ n, AEStronglyMeasurable (F n) μ)
    (h_bound : ∀ n, ∀ᵐ a ∂μ, ‖F n a‖ ≤ C)
    (h_lim : TendstoInMeasure μ F atTop f) :
    Tendsto (fun n ↦ ∫ a, F n a ∂μ) atTop (𝓝 (∫ a, f a ∂μ)) :=
  tendsto_integral_of_bounded_convergence hF_meas h_bound h_lim

/-- The `L¹` form restates with the exact public signature. -/
example {α : Type*} {m : MeasurableSpace α} {μ : Measure α} [IsFiniteMeasure μ]
    {G : Type*} [NormedAddCommGroup G] [NormedSpace ℝ G]
    {F : ℕ → α → G} {f : α → G} {C : ℝ}
    (hF_meas : ∀ n, AEStronglyMeasurable (F n) μ)
    (h_bound : ∀ n, ∀ᵐ a ∂μ, ‖F n a‖ ≤ C)
    (h_lim : TendstoInMeasure μ F atTop f) :
    Tendsto (fun n ↦ ∫ a, ‖F n a - f a‖ ∂μ) atTop (𝓝 0) :=
  tendsto_integral_norm_sub_of_bounded_convergence hF_meas h_bound h_lim

/-- Constant sequence: integrals of a constant function are constant. -/
example {α : Type*} {m : MeasurableSpace α} {μ : Measure α} [IsProbabilityMeasure μ] :
    Tendsto (fun _n : ℕ ↦ ∫ _a, (2 : ℝ) ∂μ) atTop (𝓝 (∫ _a, (2 : ℝ) ∂μ)) := by
  apply tendsto_integral_of_bounded_convergence (C := (2 : ℝ))
    (fun _ ↦ aestronglyMeasurable_const)
    (fun _ ↦ ae_of_all _ fun _ ↦ by norm_num [Real.norm_eq_abs])
  exact tendstoInMeasure_of_tendsto_ae (fun _ ↦ aestronglyMeasurable_const)
    (ae_of_all _ fun _ ↦ tendsto_const_nhds)

/-- A genuine convergence-in-measure example: on `ℝ` with the Dirac measure at `1`,
`F n a = (1 - 1 / (n + 1)) * a` converges a.e. (hence in measure) to `f a = a`,
and every `F n` is bounded by `1` a.e., so both the integral and the `L¹` form
of bounded convergence apply. -/
example : Tendsto (fun (n : ℕ) ↦ ∫ a, (1 - 1 / (n + 1 : ℝ)) * a ∂(Measure.dirac (1 : ℝ)))
    atTop (𝓝 (∫ a, a ∂(Measure.dirac (1 : ℝ)))) := by
  apply tendsto_integral_of_bounded_convergence (C := (1 : ℝ))
  · intro n
    exact (measurable_const.mul measurable_id).aestronglyMeasurable
  · intro n
    rw [ae_dirac_eq, eventually_pure, mul_one]
    rw [Real.norm_eq_abs, abs_of_nonneg]
    · have h : (0 : ℝ) ≤ 1 / (n + 1) := by positivity
      linarith
    · have h : (1 : ℝ) / (n + 1) ≤ 1 := by
        rw [div_le_one (by positivity)]
        exact_mod_cast Nat.le_add_left 1 n
      linarith
  · apply tendstoInMeasure_of_tendsto_ae
      (fun n ↦ (measurable_const.mul measurable_id).aestronglyMeasurable)
    rw [ae_dirac_eq, eventually_pure]
    have hconv : Tendsto (fun n : ℕ ↦ (1 : ℝ) - 1 / (n + 1 : ℝ)) atTop (𝓝 1) := by
      simpa using (tendsto_const_nhds (x := (1 : ℝ))).sub
        tendsto_one_div_add_atTop_nhds_zero_nat
    simpa using hconv

/-- The same example in `L¹` form: `∫ ‖F n - f‖ → 0`. -/
example : Tendsto
    (fun (n : ℕ) ↦ ∫ a, ‖(1 - 1 / (n + 1 : ℝ)) * a - a‖ ∂(Measure.dirac (1 : ℝ)))
    atTop (𝓝 0) := by
  apply tendsto_integral_norm_sub_of_bounded_convergence (C := (1 : ℝ))
  · intro n
    exact (measurable_const.mul measurable_id).aestronglyMeasurable
  · intro n
    rw [ae_dirac_eq, eventually_pure, mul_one]
    rw [Real.norm_eq_abs, abs_of_nonneg]
    · have h : (0 : ℝ) ≤ 1 / (n + 1) := by positivity
      linarith
    · have h : (1 : ℝ) / (n + 1) ≤ 1 := by
        rw [div_le_one (by positivity)]
        exact_mod_cast Nat.le_add_left 1 n
      linarith
  · apply tendstoInMeasure_of_tendsto_ae
      (fun n ↦ (measurable_const.mul measurable_id).aestronglyMeasurable)
    rw [ae_dirac_eq, eventually_pure]
    have hconv : Tendsto (fun n : ℕ ↦ (1 : ℝ) - 1 / (n + 1 : ℝ)) atTop (𝓝 1) := by
      simpa using (tendsto_const_nhds (x := (1 : ℝ))).sub
        tendsto_one_div_add_atTop_nhds_zero_nat
    simpa using hconv

-- `#print axioms` for the public declarations: only the standard triple.
#print axioms MeasureTheory.tendsto_integral_of_bounded_convergence
#print axioms MeasureTheory.tendsto_integral_norm_sub_of_bounded_convergence

end MathlibExtTest.MeasureTheory.Function.BoundedConvergence
