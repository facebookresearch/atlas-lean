/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Probability.Quantile
public import Mathlib.MeasureTheory.Measure.Dirac.Basic
public import Mathlib.MeasureTheory.Measure.Dirac.Def
public import Mathlib.MeasureTheory.Measure.Real
public import Mathlib.Probability.Distributions.Gaussian.Real

/-!
# Tests for cdf-at-quantile at continuity points

Gaussian use-case, the discontinuous one-atom Dirac counterexample, and the
`u = 1` boundary convention.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory

namespace ProbabilityTheory

/-- Use: with Gaussian cdf continuity, `Φ` of the `0.95` quantile is `0.95`. -/
example (u : ℝ) (hu : u ∈ Set.Ioo (0 : ℝ) 1)
    (hc : ContinuousAt (cdf (gaussianReal 0 1)) (cdfQuantile (gaussianReal 0 1) u)) :
    cdf (gaussianReal 0 1) (cdfQuantile (gaussianReal 0 1) u) = u := by
  exact cdf_cdfQuantile_eq_of_continuousAt _ hu hc

/-- Counterexample: the Dirac jump breaks the identity — at `ν = dirac 0`,
`u = 1 / 4`, the cdf at the quantile equals `1`, not `u`; continuity `hc`
fails at the quantile point. -/
example : ∃ (ν : Measure ℝ) (_ : IsProbabilityMeasure ν) (u : ℝ),
    u ∈ Set.Ioo (0 : ℝ) 1 ∧ cdf ν (cdfQuantile ν u) ≠ u := by
  refine ⟨Measure.dirac 0, inferInstance, (1 / 4 : ℝ), by norm_num [Set.mem_Ioo], ?_⟩
  have hu : (1 / 4 : ℝ) ∈ Set.Ioo (0 : ℝ) 1 := by norm_num [Set.mem_Ioo]
  have hmem : (1 / 4 : ℝ)
      ≤ cdf (Measure.dirac (0 : ℝ)) (cdfQuantile (Measure.dirac (0 : ℝ)) (1 / 4)) :=
    cdfQuantile_mem _ hu
  have hcdf : cdf (Measure.dirac (0 : ℝ))
      (cdfQuantile (Measure.dirac (0 : ℝ)) (1 / 4)) = 1 := by
    have h := cdf_eq_real (Measure.dirac (0 : ℝ))
      (cdfQuantile (Measure.dirac (0 : ℝ)) (1 / 4))
    rw [Measure.dirac_real_apply] at h
    rw [Set.indicator_apply] at h
    by_cases h0 : (0 : ℝ) ∈ Set.Iic (cdfQuantile (Measure.dirac (0 : ℝ)) (1 / 4))
    · simp only [h0, ↓reduceIte, Pi.one_apply] at h
      exact h
    · simp only [h0, ↓reduceIte] at h
      rw [h] at hmem
      norm_num at hmem
  rw [hcdf]
  norm_num

/-- Boundary: `u = 1` is excluded (the quantile is `0` by convention). -/
example (μ : Measure ℝ) [IsProbabilityMeasure μ] :
    cdfQuantile μ 1 = 0 := by
  simp [cdfQuantile]

end ProbabilityTheory
