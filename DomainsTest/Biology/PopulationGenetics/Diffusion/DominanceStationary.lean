/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Domains.Biology.PopulationGenetics.Diffusion.DominanceStationary
public import Mathlib.Analysis.Calculus.ContDiff.Defs
public import Mathlib.Analysis.Calculus.Deriv.Basic
public import Mathlib.Analysis.Complex.Exponential
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Basic.ENNReal.Basic
public import Mathlib.Data.Set.Defs
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
public import Mathlib.Order.Filter.Defs
public import Mathlib.Order.Interval.Set.Defs
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.Ring
public import Mathlib.Topology.Defs.Filter

@[expose] public section

namespace MathlibExtTest.Biology.PopulationGenetics.Diffusion.DominanceStationary

open Filter
open scoped Topology
open MathlibExt.Biology.PopulationGenetics.Diffusion

example : dominanceStationaryDensity 1 (1 / 2) 1 1 (1 / 2) = Real.exp 1 * 2 := by
  have h1 : (4 : ℝ) * 1 * (1 / 2) * (1 / 2) + 2 * 1 * (1 - 2 * (1 / 2)) *
      (1 / 2) ^ 2 = 1 := by
    norm_num
  have h2 : mutationSpeedDensity (1 : ℝ) 1 (1 / 2) = 2 := by
    have e0 : (1 : ℝ) - 1 = 0 := by norm_num
    simp only [mutationSpeedDensity, e0, Real.rpow_zero]
    norm_num
  simp only [dominanceStationaryDensity, h1, h2]

example : dominanceStationaryDensity 1 (1 / 2) 1 1 (1 / 2) =
    selectionMutationSpeedDensity 1 1 1 (1 / 2) :=
  dominanceStationaryDensity_half 1 1 1 (1 / 2)

example : selectionMutationSpeedDensity 1 1 1 (1 / 2) = Real.exp 1 * 2 := by
  have hB : dominanceStationaryDensity (1 : ℝ) (1 / 2) 1 1 (1 / 2) =
      Real.exp 1 * 2 := by
    have h1 : (4 : ℝ) * 1 * (1 / 2) * (1 / 2) + 2 * 1 * (1 - 2 * (1 / 2)) *
        (1 / 2) ^ 2 = 1 := by
      norm_num
    have h2 : mutationSpeedDensity (1 : ℝ) 1 (1 / 2) = 2 := by
      have e0 : (1 : ℝ) - 1 = 0 := by norm_num
      simp only [mutationSpeedDensity, e0, Real.rpow_zero]
      norm_num
    simp only [dominanceStationaryDensity, h1, h2]
  have hH := dominanceStationaryDensity_half (1 : ℝ) 1 1 (1 / 2)
  rw [← hH]
  exact hB

example (h θ₁ θ₂ x : ℝ) :
    dominanceStationaryDensity 0 h θ₁ θ₂ x = mutationSpeedDensity θ₁ θ₂ x := by
  have e : (4 : ℝ) * 0 * h * x + 2 * 0 * (1 - 2 * h) * x ^ 2 = 0 := by ring
  simp only [dominanceStationaryDensity, e, Real.exp_zero, one_mul]

example (h : ℝ) : scaleDensityFrom
    (fun x => (1 * (1 - x) - 1 * x) / 2 + dominanceDrift 0 h x)
    (fun x => x * (1 - x)) (1 / 2) (1 / 2) = 1 := by
  have hc0 : (1 / 2 : ℝ) ∈ Set.Ioo (0 : ℝ) 1 := ⟨by norm_num, by norm_num⟩
  have hS := scaleDensityFrom_dominance (0 : ℝ) h 1 1 (1 / 2) (1 / 2) hc0 hc0
  rw [hS]
  have e0 : (4 : ℝ) * 0 * h * (1 / 2) + 2 * 0 * (1 - 2 * h) * (1 / 2) ^ 2 =
      0 := by
    ring
  rw [e0, neg_zero, Real.exp_zero]
  have r1 : ((1 / 2 : ℝ)) ^ ((1 : ℝ)) = 1 / 2 := Real.rpow_one _
  have r2 : ((1 : ℝ) - 1 / 2) ^ ((1 : ℝ)) = 1 / 2 := by
    have hbase : ((1 : ℝ) - 1 / 2) = 1 / 2 := by norm_num
    rw [hbase, Real.rpow_one]
  have mS : mutationScaleDensity (1 : ℝ) 1 (1 / 2) = 4 := by
    have n1 : ((1 / 2 : ℝ)) ^ (-(1 : ℝ)) = 2 := by
      rw [Real.rpow_neg_one]
      norm_num
    have n2 : ((1 : ℝ) - 1 / 2) ^ (-(1 : ℝ)) = 2 := by
      have hbase : ((1 : ℝ) - 1 / 2) = 1 / 2 := by norm_num
      rw [hbase, Real.rpow_neg_one]
      norm_num
    simp only [mutationScaleDensity, n1, n2]
    norm_num
  rw [r1, r2, mS]
  norm_num

example (h : ℝ) :
    speedMeasureFrom
      (fun x => (1 * (1 - x) - 1 * x) / 2 + dominanceDrift 0 h x)
      (fun x => x * (1 - x)) (1 / 2) Set.univ =
      ENNReal.ofReal (((1 / 2 : ℝ) ^ (-(1 : ℝ)) * (1 - 1 / 2) ^ (-(1 : ℝ)) *
        Real.exp (-(4 * 0 * h * (1 / 2) + 2 * 0 * (1 - 2 * h) * (1 / 2) ^ 2))) *
        ∫ x in (0 : ℝ)..1, dominanceStationaryDensity 0 h 1 1 x) := by
  have hc0 : (1 / 2 : ℝ) ∈ Set.Ioo (0 : ℝ) 1 := ⟨by norm_num, by norm_num⟩
  exact speedMeasureFrom_dominance_univ 0 h 1 1 (1 / 2) hc0 zero_lt_one zero_lt_one

example (c h θ₁ θ₂ c0 : ℝ) (hc0 : c0 ∈ Set.Ioo (0 : ℝ) 1) (hθ₁ : 0 < θ₁)
    (hθ₂ : 0 < θ₂) (hf : ContDiffOn ℝ 2 (fun x : ℝ => x) (Set.Icc (0 : ℝ) 1)) :
    Tendsto (fun y => deriv (fun x : ℝ => x) y /
      scaleDensityFrom (fun x => (θ₁ * (1 - x) - θ₂ * x) / 2 + dominanceDrift c h x)
        (fun x => x * (1 - x)) c0 y) (𝓝[>] (0 : ℝ)) (𝓝 0) :=
  tendsto_deriv_div_scaleDensityFrom_dominance_zero c h θ₁ θ₂ c0 _
    hc0 hθ₁ hθ₂ hf

example (c h θ₁ θ₂ c0 : ℝ) (hc0 : c0 ∈ Set.Ioo (0 : ℝ) 1) (hθ₁ : 0 < θ₁)
    (hθ₂ : 0 < θ₂) (hf : ContDiffOn ℝ 2 (fun x : ℝ => x) (Set.Icc (0 : ℝ) 1)) :
    Tendsto (fun y => deriv (fun x : ℝ => x) y /
      scaleDensityFrom (fun x => (θ₁ * (1 - x) - θ₂ * x) / 2 + dominanceDrift c h x)
        (fun x => x * (1 - x)) c0 y) (𝓝[<] (1 : ℝ)) (𝓝 0) :=
  tendsto_deriv_div_scaleDensityFrom_dominance_one c h θ₁ θ₂ c0 _
    hc0 hθ₁ hθ₂ hf

#print axioms dominanceStationaryDensity_half
#print axioms scaleDensityFrom_dominance
#print axioms speedDensityFrom_dominance
#print axioms tendsto_deriv_div_scaleDensityFrom_dominance_zero
#print axioms tendsto_deriv_div_scaleDensityFrom_dominance_one
#print axioms integral_diffusionGenerator_dominance_speedMeasureFrom
#print axioms speedMeasureFrom_dominance_univ

example : dominanceStationaryDensity 1 0 1 1 (1 / 2) =
    Real.exp (1 / 2) * 2 := by
  have h1 : (4 : ℝ) * 1 * 0 * (1 / 2) + 2 * 1 * (1 - 2 * 0) *
      (1 / 2) ^ 2 = 1 / 2 := by
    norm_num
  have h2 : mutationSpeedDensity (1 : ℝ) 1 (1 / 2) = 2 := by
    have e0 : (1 : ℝ) - 1 = 0 := by norm_num
    simp only [mutationSpeedDensity, e0, Real.rpow_zero]
    norm_num
  simp only [dominanceStationaryDensity, h1, h2]

example : scaleDensityFrom
    (fun x => (1 * (1 - x) - 1 * x) / 2 + dominanceDrift 1 0 x)
    (fun x => x * (1 - x)) (1 / 2) (1 / 4) =
    (4 / 3) * Real.exp (3 / 8) := by
  have hc0 : (1 / 2 : ℝ) ∈ Set.Ioo (0 : ℝ) 1 := ⟨by norm_num, by norm_num⟩
  have hy : (1 / 4 : ℝ) ∈ Set.Ioo (0 : ℝ) 1 := ⟨by norm_num, by norm_num⟩
  have hS := scaleDensityFrom_dominance (1 : ℝ) 0 1 1 (1 / 2) (1 / 4) hc0 hy
  rw [hS]
  have e0 : (4 : ℝ) * 1 * 0 * (1 / 2) + 2 * 1 * (1 - 2 * 0) * (1 / 2) ^ 2 =
      1 / 2 := by
    norm_num
  have e1 : (4 : ℝ) * 1 * 0 * (1 / 4) + 2 * 1 * (1 - 2 * 0) * (1 / 4) ^ 2 =
      1 / 8 := by
    norm_num
  rw [e0, e1]
  have r1 : ((1 / 2 : ℝ)) ^ ((1 : ℝ)) = 1 / 2 := Real.rpow_one _
  have r2 : ((1 : ℝ) - 1 / 2) ^ ((1 : ℝ)) = 1 / 2 := by
    have hbase : ((1 : ℝ) - 1 / 2) = 1 / 2 := by norm_num
    rw [hbase, Real.rpow_one]
  have mS : mutationScaleDensity (1 : ℝ) 1 (1 / 4) = 16 / 3 := by
    have n1 : ((1 / 4 : ℝ)) ^ (-(1 : ℝ)) = 4 := by
      rw [Real.rpow_neg_one]
      norm_num
    have n2 : ((1 : ℝ) - 1 / 4) ^ (-(1 : ℝ)) = 4 / 3 := by
      have hbase : ((1 : ℝ) - 1 / 4) = 3 / 4 := by norm_num
      rw [hbase, Real.rpow_neg_one]
      norm_num
    simp only [mutationScaleDensity, n1, n2]
    norm_num
  rw [r1, r2, mS]
  have hexp : Real.exp (1 / 2 : ℝ) * Real.exp (-(1 / 8 : ℝ)) =
      Real.exp (3 / 8 : ℝ) := by
    rw [← Real.exp_add]
    congr 1
    norm_num
  trans (4 / 3 : ℝ) * (Real.exp (1 / 2) * Real.exp (-(1 / 8)))
  · ring
  · rw [hexp]

example : speedDensityFrom
    (fun x => (1 * (1 - x) - 1 * x) / 2 + dominanceDrift 1 0 x)
    (fun x => x * (1 - x)) (1 / 2) (1 / 4) =
    8 * Real.exp (-(3 / 8)) := by
  have hc0 : (1 / 2 : ℝ) ∈ Set.Ioo (0 : ℝ) 1 := ⟨by norm_num, by norm_num⟩
  have hy : (1 / 4 : ℝ) ∈ Set.Ioo (0 : ℝ) 1 := ⟨by norm_num, by norm_num⟩
  have hS := speedDensityFrom_dominance (1 : ℝ) 0 1 1 (1 / 2) (1 / 4) hc0 hy
  rw [hS]
  have e0 : (4 : ℝ) * 1 * 0 * (1 / 2) + 2 * 1 * (1 - 2 * 0) * (1 / 2) ^ 2 =
      1 / 2 := by
    norm_num
  rw [e0]
  have r1 : ((1 / 2 : ℝ)) ^ (-(1 : ℝ)) = 2 := by
    rw [Real.rpow_neg_one]
    norm_num
  have r2 : ((1 : ℝ) - 1 / 2) ^ (-(1 : ℝ)) = 2 := by
    have hbase : ((1 : ℝ) - 1 / 2) = 1 / 2 := by norm_num
    rw [hbase, Real.rpow_neg_one]
    norm_num
  have dS : dominanceStationaryDensity (1 : ℝ) 0 1 1 (1 / 4) =
      Real.exp (1 / 8) * 2 := by
    have g1 : (4 : ℝ) * 1 * 0 * (1 / 4) + 2 * 1 * (1 - 2 * 0) * (1 / 4) ^ 2 =
        1 / 8 := by
      norm_num
    have g2 : mutationSpeedDensity (1 : ℝ) 1 (1 / 4) = 2 := by
      have e0 : (1 : ℝ) - 1 = 0 := by norm_num
      simp only [mutationSpeedDensity, e0, Real.rpow_zero]
      norm_num
    simp only [dominanceStationaryDensity, g1, g2]
  rw [r1, r2, dS]
  have hexp : Real.exp (-(1 / 2 : ℝ)) * Real.exp (1 / 8 : ℝ) =
      Real.exp (-(3 / 8 : ℝ)) := by
    rw [← Real.exp_add]
    congr 1
    norm_num
  trans (8 : ℝ) * (Real.exp (-(1 / 2)) * Real.exp (1 / 8))
  · ring
  · rw [hexp]

end MathlibExtTest.Biology.PopulationGenetics.Diffusion.DominanceStationary
