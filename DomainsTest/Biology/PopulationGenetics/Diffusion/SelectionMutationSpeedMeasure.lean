/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Domains.Biology.PopulationGenetics.Diffusion.SelectionMutationSpeedMeasure
public import Mathlib.Analysis.Calculus.ContDiff.Basic
public import Mathlib.Analysis.Calculus.ContDiff.Defs
public import Mathlib.Analysis.Calculus.ContDiff.Operations
public import Mathlib.Analysis.Calculus.Deriv.Basic
public import Mathlib.Analysis.SpecialFunctions.Exp
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Basic.ENNReal.Basic
public import Mathlib.Data.Set.Defs
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
public import Mathlib.Order.Filter.Defs
public import Mathlib.Order.Interval.Set.Defs
public import Mathlib.Topology.Defs.Filter

@[expose] public section

open Real Set Filter MeasureTheory
open scoped Topology

namespace MathlibExtTest.Biology.PopulationGenetics.Diffusion.SelectionMutationSpeedMeasure

open MathlibExt.Biology.PopulationGenetics.Diffusion

example : selectionMutationScaleDensity 0 1 1 (1 / 2) = 4 := by
  have h12 : ((1 : ℝ) - 1 / 2) = 1 / 2 := by norm_num
  have hpow : ((1 / 2 : ℝ) ^ (-(1 : ℝ))) = 2 := by
    have hle : (0 : ℝ) ≤ 1 / 2 := by norm_num
    rw [Real.rpow_neg hle, Real.rpow_one]
    norm_num
  simp only [selectionMutationScaleDensity, mutationScaleDensity]
  rw [h12, hpow]
  norm_num [Real.exp_zero]

example : ∀ y : ℝ, selectionMutationSpeedDensity 0 1 1 y = 2 := by
  intro y
  have h10 : ((1 : ℝ) - 1) = 0 := by norm_num
  simp only [selectionMutationSpeedDensity, mutationSpeedDensity, h10,
    Real.rpow_zero]
  norm_num [Real.exp_zero]

example : scaleDensityFrom
    (fun x => ((1 : ℝ) * (1 - x) - 1 * x) / 2 + 0 * (x * (1 - x)))
    (fun x => x * (1 - x)) (1 / 2) (1 / 2) = 1 := by
  have hc : ((1 / 2 : ℝ)) ∈ Ioo 0 1 := by norm_num [Set.mem_Ioo]
  have h12 : ((1 : ℝ) - 1 / 2) = 1 / 2 := by norm_num
  have hpow : ((1 / 2 : ℝ) ^ (-(1 : ℝ))) = 2 := by
    have hle : (0 : ℝ) ≤ 1 / 2 := by norm_num
    rw [Real.rpow_neg hle, Real.rpow_one]
    norm_num
  have hK : ((1 / 2 : ℝ) ^ ((1 : ℝ)) * (1 - 1 / 2) ^ (1 : ℝ) *
      Real.exp (2 * 0 * (1 / 2))) = 1 / 4 := by
    rw [h12]
    norm_num [Real.exp_zero, Real.rpow_one]
  have hval : selectionMutationScaleDensity 0 1 1 (1 / 2) = 4 := by
    simp only [selectionMutationScaleDensity, mutationScaleDensity]
    rw [h12, hpow]
    norm_num [Real.exp_zero]
  rw [scaleDensityFrom_selectionMutation 0 1 1 (1 / 2) (1 / 2) hc hc]
  rw [hK, hval]
  norm_num

example : speedDensityFrom
    (fun x => ((1 : ℝ) * (1 - x) - 1 * x) / 2 + 0 * (x * (1 - x)))
    (fun x => x * (1 - x)) (1 / 2) (1 / 2) = 8 := by
  have hc : ((1 / 2 : ℝ)) ∈ Ioo 0 1 := by norm_num [Set.mem_Ioo]
  have h12 : ((1 : ℝ) - 1 / 2) = 1 / 2 := by norm_num
  have hpow : ((1 / 2 : ℝ) ^ (-(1 : ℝ))) = 2 := by
    have hle : (0 : ℝ) ≤ 1 / 2 := by norm_num
    rw [Real.rpow_neg hle, Real.rpow_one]
    norm_num
  have hK : ((1 / 2 : ℝ) ^ (-(1 : ℝ)) * (1 - 1 / 2) ^ (-(1 : ℝ)) *
      Real.exp (-2 * 0 * (1 / 2))) = 4 := by
    rw [h12, hpow]
    norm_num [Real.exp_zero]
  have h10 : ((1 : ℝ) - 1) = 0 := by norm_num
  have hs : selectionMutationSpeedDensity 0 1 1 (1 / 2) = 2 := by
    simp only [selectionMutationSpeedDensity, mutationSpeedDensity, h10,
      Real.rpow_zero]
    norm_num [Real.exp_zero]
  rw [speedDensityFrom_selectionMutation 0 1 1 (1 / 2) (1 / 2) hc hc]
  rw [hK, hs]
  norm_num

example : speedMeasureFrom
    (fun x => ((1 : ℝ) * (1 - x) - 1 * x) / 2 + 0 * (x * (1 - x)))
    (fun x => x * (1 - x)) (1 / 2) Set.univ = ENNReal.ofReal 8 := by
  have hc : ((1 / 2 : ℝ)) ∈ Ioo 0 1 := by norm_num [Set.mem_Ioo]
  have hθ : (0 : ℝ) < 1 := one_pos
  have h12 : ((1 : ℝ) - 1 / 2) = 1 / 2 := by norm_num
  have hpow : ((1 / 2 : ℝ) ^ (-(1 : ℝ))) = 2 := by
    have hle : (0 : ℝ) ≤ 1 / 2 := by norm_num
    rw [Real.rpow_neg hle, Real.rpow_one]
    norm_num
  have hK : ((1 / 2 : ℝ) ^ (-(1 : ℝ)) * (1 - 1 / 2) ^ (-(1 : ℝ)) *
      Real.exp (-2 * 0 * (1 / 2))) = 4 := by
    rw [h12, hpow]
    norm_num [Real.exp_zero]
  have h10 : ((1 : ℝ) - 1) = 0 := by norm_num
  have hpart : selectionMutationPartition 0 1 1 = 2 := by
    rw [selectionMutationPartition]
    have hfun : (fun x : ℝ => selectionMutationSpeedDensity 0 1 1 x) =
        fun _ => 2 := by
      funext x
      simp only [selectionMutationSpeedDensity, mutationSpeedDensity, h10,
        Real.rpow_zero]
      norm_num [Real.exp_zero]
    rw [hfun, intervalIntegral.integral_const]
    simp
  rw [speedMeasureFrom_selectionMutation_univ 0 1 1 (1 / 2) hθ hθ hc]
  rw [hK, hpart]
  congr 1
  norm_num

example : Tendsto
    (fun y => deriv (fun x : ℝ => x) y / scaleDensityFrom
      (fun x => ((1 : ℝ) * (1 - x) - 1 * x) / 2 + 0 * (x * (1 - x)))
      (fun x => x * (1 - x)) (1 / 2) y) (𝓝[>] 0) (𝓝 0) :=
  tendsto_deriv_div_scaleDensityFrom_selectionMutation_zero 0 1 1 (1 / 2)
    (fun x : ℝ => x) one_pos one_pos (by norm_num [Set.mem_Ioo])
    contDiffOn_id

example : Tendsto
    (fun y => deriv (fun x : ℝ => x) y / scaleDensityFrom
      (fun x => ((1 : ℝ) * (1 - x) - 1 * x) / 2 + 0 * (x * (1 - x)))
      (fun x => x * (1 - x)) (1 / 2) y) (𝓝[<] 1) (𝓝 0) :=
  tendsto_deriv_div_scaleDensityFrom_selectionMutation_one 0 1 1 (1 / 2)
    (fun x : ℝ => x) one_pos one_pos (by norm_num [Set.mem_Ioo])
    contDiffOn_id

example : Integrable
      (diffusionGenerator
        (fun x => ((1 : ℝ) * (1 - x) - 1 * x) / 2 + 0 * (x * (1 - x)))
        (fun x => x * (1 - x)) (fun x : ℝ => x ^ 2))
      (speedMeasureFrom
        (fun x => ((1 : ℝ) * (1 - x) - 1 * x) / 2 + 0 * (x * (1 - x)))
        (fun x => x * (1 - x)) (1 / 2)) →
    ∫ x, diffusionGenerator
      (fun x => ((1 : ℝ) * (1 - x) - 1 * x) / 2 + 0 * (x * (1 - x)))
      (fun x => x * (1 - x)) (fun x : ℝ => x ^ 2) x ∂(speedMeasureFrom
      (fun x => ((1 : ℝ) * (1 - x) - 1 * x) / 2 + 0 * (x * (1 - x)))
      (fun x => x * (1 - x)) (1 / 2)) = 0 :=
  fun hint => integral_diffusionGenerator_selectionMutation_speedMeasureFrom
    0 1 1 (1 / 2) (fun x : ℝ => x ^ 2) one_pos one_pos
    (by norm_num [Set.mem_Ioo]) (contDiffOn_id.pow 2) hint

#print axioms scaleDensityFrom_selectionMutation
#print axioms speedDensityFrom_selectionMutation
#print axioms tendsto_deriv_div_scaleDensityFrom_selectionMutation_zero
#print axioms tendsto_deriv_div_scaleDensityFrom_selectionMutation_one
#print axioms integral_diffusionGenerator_selectionMutation_speedMeasureFrom
#print axioms speedMeasureFrom_selectionMutation_univ

end MathlibExtTest.Biology.PopulationGenetics.Diffusion.SelectionMutationSpeedMeasure

end
