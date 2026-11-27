/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import Domains.Biology.PopulationGenetics.Diffusion.OccupationMoments
import Mathlib.Basic.NNReal.Defs
import Mathlib.MeasureTheory.Function.L1Space.Integrable
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.MeasureTheory.Measure.Typeclasses.Probability
import Mathlib.Order.Interval.Set.Defs
import Mathlib.Probability.Process.Filtration
import Mathlib.Tactic
import Mathlib.Topology.UnitInterval

open MeasureTheory Filter
open scoped NNReal unitInterval

open MathlibExt.Biology.PopulationGenetics.Diffusion (generator
  generator_zero_heterozygositySqPotential
  integral_sq_two_mul_one_sub_absorptionTime
  integral_sq_two_mul_one_sub_absorptionTime_modifiedProcess)
open MathlibExt.Biology.PopulationGenetics.Diffusion.KimuraFixationProcess
  (IsWrightFisherSolution absorptionTime)
open MathlibExt.Biology.PopulationGenetics.Diffusion.NeutralWrightFisherRaw
  (modifiedProcess rawMeasure)

namespace MathlibExtTest.Biology.PopulationGenetics.Diffusion.OccupationMoments

example : generator 0 (fun z => (2 / 3) * z * (1 - z) * (1 + z - z ^ 2)) 0 = 0 := by
  rw [generator_zero_heterozygositySqPotential]
  norm_num

example : generator 0 (fun z => (2 / 3) * z * (1 - z) * (1 + z - z ^ 2)) 1 = 0 := by
  rw [generator_zero_heterozygositySqPotential]
  norm_num

example : generator 0 (fun z => (2 / 3) * z * (1 - z) * (1 + z - z ^ 2)) (1 / 2) =
    -(1 / 4) := by
  rw [generator_zero_heterozygositySqPotential]
  norm_num

example : ∫ ω, (∫ s in (0 : ℝ)..(absorptionTime (modifiedProcess (0 : I)) ω : ℝ),
      (2 * modifiedProcess (0 : I) (Real.toNNReal s) ω *
        (1 - modifiedProcess (0 : I) (Real.toNNReal s) ω)) ^ 2)
      ∂(rawMeasure (0 : I)) = 0 := by
  have h := (integral_sq_two_mul_one_sub_absorptionTime_modifiedProcess (0 : I)).2
  rw [h]
  norm_num

example : ∫ ω, (∫ s in (0 : ℝ)..(absorptionTime
        (modifiedProcess ⟨1 / 2, by norm_num [Set.mem_Icc]⟩) ω : ℝ),
      (2 * modifiedProcess ⟨1 / 2, by norm_num [Set.mem_Icc]⟩ (Real.toNNReal s) ω *
        (1 - modifiedProcess ⟨1 / 2, by norm_num [Set.mem_Icc]⟩
          (Real.toNNReal s) ω)) ^ 2)
      ∂(rawMeasure ⟨1 / 2, by norm_num [Set.mem_Icc]⟩) = 5 / 24 := by
  have h := (integral_sq_two_mul_one_sub_absorptionTime_modifiedProcess
    (⟨1 / 2, by norm_num [Set.mem_Icc]⟩ : I)).2
  rw [h]
  norm_num

example : ∫ ω, (∫ s in (0 : ℝ)..(absorptionTime (modifiedProcess (1 : I)) ω : ℝ),
      (2 * modifiedProcess (1 : I) (Real.toNNReal s) ω *
        (1 - modifiedProcess (1 : I) (Real.toNNReal s) ω)) ^ 2)
      ∂(rawMeasure (1 : I)) = 0 := by
  have h := (integral_sq_two_mul_one_sub_absorptionTime_modifiedProcess (1 : I)).2
  rw [h]
  norm_num

example (x : I) :
    Integrable (fun ω => ∫ s in (0 : ℝ)..(absorptionTime (modifiedProcess x) ω : ℝ),
      (2 * modifiedProcess x (Real.toNNReal s) ω *
        (1 - modifiedProcess x (Real.toNNReal s) ω)) ^ 2) (rawMeasure x) :=
  (integral_sq_two_mul_one_sub_absorptionTime_modifiedProcess x).1

example {Ω : Type*} {mΩ : MeasurableSpace Ω} {x : ℝ} {ℱ : Filtration ℝ≥0 mΩ}
    {μ : Measure Ω} [IsProbabilityMeasure μ] {X : ℝ≥0 → Ω → ℝ}
    (hX : IsWrightFisherSolution 0 ℱ μ X) (hX0 : ∀ᵐ ω ∂μ, X 0 ω = x) :
    ∫ ω, (∫ s in (0 : ℝ)..(absorptionTime X ω : ℝ),
      (2 * X (Real.toNNReal s) ω * (1 - X (Real.toNNReal s) ω)) ^ 2) ∂μ =
      (2 / 3) * x * (1 - x) * (1 + x - x ^ 2) :=
  (integral_sq_two_mul_one_sub_absorptionTime hX hX0).2

end MathlibExtTest.Biology.PopulationGenetics.Diffusion.OccupationMoments

#print axioms generator_zero_heterozygositySqPotential
#print axioms integral_sq_two_mul_one_sub_absorptionTime
#print axioms integral_sq_two_mul_one_sub_absorptionTime_modifiedProcess
