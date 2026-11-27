/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import Domains.Biology.PopulationGenetics.Diffusion.PathFunctionals
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.MeasureTheory.Function.L1Space.Integrable
import Mathlib.MeasureTheory.Function.StronglyMeasurable.AEStronglyMeasurable
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.MeasureTheory.Measure.Restrict
import Mathlib.Probability.Process.Filtration
import Mathlib.Tactic
import Mathlib.Topology.UnitInterval

/-!
# Boundary tests for neutral heterozygosity path functionals

Endpoint and interior readings of the neutral generator identity for `2y(1-y)` and of
the stopped heterozygosity integral for the constructed neutral realization, in diffusion
time units.
-/

open MeasureTheory Filter Set
open scoped NNReal unitInterval

open MathlibExt.Biology.PopulationGenetics.Diffusion
  (generator generator_heterozygosity integral_two_mul_one_sub_absorptionTime
    integral_two_mul_one_sub_absorptionTime_modifiedProcess)
open MathlibExt.Biology.PopulationGenetics.Diffusion.KimuraFixationProcess
  (IsWrightFisherSolution absorptionTime)
open MathlibExt.Biology.PopulationGenetics.Diffusion.NeutralWrightFisherRaw
  (modifiedProcess rawMeasure)

namespace MathlibExtTest.Biology.PopulationGenetics.Diffusion.PathFunctionals

example : generator 0 (fun z => 2 * z * (1 - z)) 0 = 0 := by
  rw [generator_heterozygosity]
  norm_num

example : generator 0 (fun z => 2 * z * (1 - z)) 1 = 0 := by
  rw [generator_heterozygosity]
  norm_num

example : generator 0 (fun z => 2 * z * (1 - z)) (1 / 2) = -(1 / 2) := by
  rw [generator_heterozygosity]
  norm_num

example : ∫ ω, (∫ s in (0 : ℝ)..(absorptionTime
      (modifiedProcess ⟨0, unitInterval.zero_mem⟩) ω : ℝ),
    2 * modifiedProcess ⟨0, unitInterval.zero_mem⟩ (Real.toNNReal s) ω *
      (1 - modifiedProcess ⟨0, unitInterval.zero_mem⟩ (Real.toNNReal s) ω))
    ∂(rawMeasure ⟨0, unitInterval.zero_mem⟩) = 0 := by
  have h : ∫ ω, (∫ s in (0 : ℝ)..(absorptionTime
      (modifiedProcess ⟨0, unitInterval.zero_mem⟩) ω : ℝ),
    2 * modifiedProcess ⟨0, unitInterval.zero_mem⟩ (Real.toNNReal s) ω *
      (1 - modifiedProcess ⟨0, unitInterval.zero_mem⟩ (Real.toNNReal s) ω))
    ∂(rawMeasure ⟨0, unitInterval.zero_mem⟩) = 2 * (0 : ℝ) * (1 - 0) :=
    (integral_two_mul_one_sub_absorptionTime_modifiedProcess
      ⟨0, unitInterval.zero_mem⟩).2
  norm_num at h
  exact h

example : ∫ ω, (∫ s in (0 : ℝ)..(absorptionTime
      (modifiedProcess ⟨1 / 2, by exact ⟨by norm_num, by norm_num⟩⟩) ω : ℝ),
    2 * modifiedProcess ⟨1 / 2, by exact ⟨by norm_num, by norm_num⟩⟩ (Real.toNNReal s) ω *
      (1 - modifiedProcess ⟨1 / 2, by exact ⟨by norm_num, by norm_num⟩⟩
        (Real.toNNReal s) ω))
    ∂(rawMeasure ⟨1 / 2, by exact ⟨by norm_num, by norm_num⟩⟩) = 1 / 2 := by
  have h : ∫ ω, (∫ s in (0 : ℝ)..(absorptionTime
      (modifiedProcess ⟨1 / 2, by exact ⟨by norm_num, by norm_num⟩⟩) ω : ℝ),
    2 * modifiedProcess ⟨1 / 2, by exact ⟨by norm_num, by norm_num⟩⟩ (Real.toNNReal s) ω *
      (1 - modifiedProcess ⟨1 / 2, by exact ⟨by norm_num, by norm_num⟩⟩
        (Real.toNNReal s) ω))
    ∂(rawMeasure ⟨1 / 2, by exact ⟨by norm_num, by norm_num⟩⟩)
      = 2 * (1 / 2 : ℝ) * (1 - 1 / 2) :=
    (integral_two_mul_one_sub_absorptionTime_modifiedProcess
      ⟨1 / 2, by exact ⟨by norm_num, by norm_num⟩⟩).2
  norm_num at h
  exact h

example : ∫ ω, (∫ s in (0 : ℝ)..(absorptionTime
      (modifiedProcess ⟨1, unitInterval.one_mem⟩) ω : ℝ),
    2 * modifiedProcess ⟨1, unitInterval.one_mem⟩ (Real.toNNReal s) ω *
      (1 - modifiedProcess ⟨1, unitInterval.one_mem⟩ (Real.toNNReal s) ω))
    ∂(rawMeasure ⟨1, unitInterval.one_mem⟩) = 0 := by
  have h : ∫ ω, (∫ s in (0 : ℝ)..(absorptionTime
      (modifiedProcess ⟨1, unitInterval.one_mem⟩) ω : ℝ),
    2 * modifiedProcess ⟨1, unitInterval.one_mem⟩ (Real.toNNReal s) ω *
      (1 - modifiedProcess ⟨1, unitInterval.one_mem⟩ (Real.toNNReal s) ω))
    ∂(rawMeasure ⟨1, unitInterval.one_mem⟩) = 2 * (1 : ℝ) * (1 - 1) :=
    (integral_two_mul_one_sub_absorptionTime_modifiedProcess
      ⟨1, unitInterval.one_mem⟩).2
  norm_num at h
  exact h

example (x : I) : Integrable
    (fun ω => ∫ s in (0 : ℝ)..(absorptionTime (modifiedProcess x) ω : ℝ),
      2 * modifiedProcess x (Real.toNNReal s) ω *
        (1 - modifiedProcess x (Real.toNNReal s) ω)) (rawMeasure x) :=
  (integral_two_mul_one_sub_absorptionTime_modifiedProcess x).1

example {Ω : Type*} {mΩ : MeasurableSpace Ω} {x : ℝ} {ℱ : Filtration ℝ≥0 mΩ}
    {μ : Measure Ω} [IsProbabilityMeasure μ] {X : ℝ≥0 → Ω → ℝ}
    (hX : IsWrightFisherSolution 0 ℱ μ X) (hX0 : ∀ᵐ ω ∂μ, X 0 ω = x) :
    ∫ ω, (∫ s in (0 : ℝ)..(absorptionTime X ω : ℝ),
      2 * X (Real.toNNReal s) ω * (1 - X (Real.toNNReal s) ω)) ∂μ
      = 2 * x * (1 - x) :=
  (integral_two_mul_one_sub_absorptionTime hX hX0).2

#print axioms integral_two_mul_one_sub_absorptionTime
#print axioms integral_two_mul_one_sub_absorptionTime_modifiedProcess

end MathlibExtTest.Biology.PopulationGenetics.Diffusion.PathFunctionals
