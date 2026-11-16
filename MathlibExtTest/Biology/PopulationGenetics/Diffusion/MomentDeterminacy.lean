/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Biology.PopulationGenetics.Diffusion.MomentDeterminacy
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic

@[expose] public section

namespace MathlibExtTest.Biology.PopulationGenetics.Diffusion

open MeasureTheory
open scoped unitInterval
open MathlibExt.Biology.PopulationGenetics.Diffusion

/-- The determinacy theorem applied with definitionally equal moments. -/
example (μ : Measure I) [IsFiniteMeasure μ] : μ = μ :=
  measure_eq_of_forall_integral_pow_eq μ μ fun _ => rfl

/-- The second moment of the Dirac measure at `1 / 2` is `1 / 4`. -/
theorem integral_sq_dirac_half :
    (∫ x, (x : ℝ) ^ 2 ∂Measure.dirac (⟨1 / 2, by norm_num⟩ : I)) = 1 / 4 := by
  rw [integral_dirac' _ _ (by fun_prop)]
  norm_num

/-- The second moment of the uniform measure on `[0, 1]` is `1 / 3`. -/
theorem integral_sq_volume : (∫ x, (x : ℝ) ^ 2 ∂(volume : Measure I)) = 1 / 3 := by
  have h := unitInterval.measurePreserving_coe.integral_comp
    unitInterval.measurableEmbedding_coe (fun y : ℝ => y ^ 2)
  rw [h, integral_Icc_eq_integral_Ioo, ← integral_Ioc_eq_integral_Ioo,
    ← intervalIntegral.integral_of_le (by norm_num)]
  rw [integral_pow]
  norm_num

/-- Acceptance probe: Dirac at `1 / 2` and the uniform measure differ in the
second moment, so they are different measures. -/
example : Measure.dirac (⟨1 / 2, by norm_num⟩ : I) ≠ (volume : Measure I) := by
  intro h
  have h2 := congrArg (fun m : Measure I => ∫ x, (x : ℝ) ^ 2 ∂m) h
  rw [integral_sq_dirac_half, integral_sq_volume] at h2
  norm_num at h2

end MathlibExtTest.Biology.PopulationGenetics.Diffusion
