/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Probability.Distributions.GaussianCdf
public import MathlibExt.Probability.Quantile
public import Mathlib.MeasureTheory.Measure.Dirac.Basic
public import Mathlib.MeasureTheory.Measure.Dirac.Def
public import Mathlib.MeasureTheory.Measure.Real
public import Mathlib.Probability.Distributions.Gaussian.Real

/-!
# Tests for cdf-at-quantile at continuity points

Gaussian use-case, the discontinuous one-atom Dirac counterexample, and the
`u = 1` boundary convention.

# Tests for quantile inversion of strictly increasing cdfs

Gaussian median use-case and the flat-cdf counterexample.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Set

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

/-- Use: with Gaussian strict monotonicity, the median quantile is `0`. -/
example : cdfQuantile (gaussianReal 0 1) (cdf (gaussianReal 0 1) 0) = 0 := by
  exact cdfQuantile_cdf_of_strictMono (gaussianReal 0 1)
    (strictMono_cdf_gaussianReal 0 one_ne_zero) 0

/-- Counterexample: a flat cdf (Bernoulli atoms on `ℝ`) breaks the inversion. -/
example : ∃ (ν : Measure ℝ) (_hν : IsProbabilityMeasure ν) (x : ℝ),
    cdf ν x ∈ Set.Ioo (0 : ℝ) 1 ∧ cdfQuantile ν (cdf ν x) ≠ x := by
  classical
  set ν : Measure ℝ := (1 / 2 : ENNReal) • Measure.dirac (0 : ℝ)
    + (1 / 2 : ENNReal) • Measure.dirac (1 : ℝ) with hνdef
  have hval : (1 / 2 : ENNReal).toReal = (1 / 2 : ℝ) := by
    rw [ENNReal.toReal_div, ENNReal.toReal_one, ENNReal.toReal_ofNat]
  have hIic_half : ν (Set.Iic (1 / 2 : ℝ)) = (1 / 2 : ENNReal) := by
    rw [hνdef, Measure.add_apply, Measure.smul_apply, Measure.smul_apply,
      Measure.dirac_apply_of_mem
        (Set.mem_Iic.mpr (show (0 : ℝ) ≤ 1 / 2 by norm_num)),
      (dirac_eq_zero_iff_notMem (s := Set.Iic (1 / 2 : ℝ)) measurableSet_Iic).mpr
        (show (1 : ℝ) ∉ Set.Iic (1 / 2 : ℝ) by norm_num [Set.mem_Iic])]
    simp
  have hIic_zero : ν (Set.Iic (0 : ℝ)) = (1 / 2 : ENNReal) := by
    rw [hνdef, Measure.add_apply, Measure.smul_apply, Measure.smul_apply,
      Measure.dirac_apply_of_mem (Set.mem_Iic.mpr le_rfl),
      (dirac_eq_zero_iff_notMem (s := Set.Iic (0 : ℝ)) measurableSet_Iic).mpr
        (show (1 : ℝ) ∉ Set.Iic (0 : ℝ) by norm_num [Set.mem_Iic])]
    simp
  have hprob : ν Set.univ = 1 := by
    rw [hνdef, Measure.add_apply, Measure.smul_apply, Measure.smul_apply,
      Measure.dirac_apply_of_mem (mem_univ (0 : ℝ)),
      Measure.dirac_apply_of_mem (mem_univ (1 : ℝ)),
      smul_eq_mul, mul_one]
    exact ENNReal.add_halves 1
  have : IsProbabilityMeasure ν := ⟨hprob⟩
  have hmem : cdf ν (1 / 2 : ℝ) ∈ Set.Ioo (0 : ℝ) 1 := by
    have h_eq : cdf ν (1 / 2 : ℝ) = (1 / 2 : ℝ) := by
      rw [ProbabilityTheory.cdf_eq_real]
      show (ν (Set.Iic (1 / 2 : ℝ))).toReal = _
      rw [hIic_half, hval]
    rw [h_eq]
    exact ⟨by norm_num, by norm_num⟩
  refine ⟨ν, ⟨hprob⟩, (1 / 2 : ℝ), hmem, ?_⟩
  have hle : cdfQuantile ν (cdf ν (1 / 2 : ℝ)) ≤ 0 := by
    rw [cdfQuantile_le_iff ν hmem]
    have h1 : cdf ν (1 / 2 : ℝ) = (1 / 2 : ENNReal).toReal := by
      rw [ProbabilityTheory.cdf_eq_real]
      show (ν (Set.Iic (1 / 2 : ℝ))).toReal = _
      rw [hIic_half]
    have h0 : cdf ν (0 : ℝ) = (1 / 2 : ENNReal).toReal := by
      rw [ProbabilityTheory.cdf_eq_real]
      show (ν (Set.Iic (0 : ℝ))).toReal = _
      rw [hIic_zero]
    rw [h1, h0]
  exact ne_of_lt (lt_of_le_of_lt hle (by norm_num))

/-!
Public API client probes carried from formal-math
`MathlibExtTest/Probability/Quantile.lean`.
-/

/-- The generalized cdf inverse is available through the public
`ProbabilityTheory` API. -/
example (μ : Measure ℝ) : Measurable (cdfQuantile μ) :=
  measurable_cdfQuantile μ

/-- The public order characterization can be used by downstream clients. -/
example (μ : Measure ℝ) {u x : ℝ} (hu : u ∈ Ioo (0 : ℝ) 1) :
    cdfQuantile μ u ≤ x ↔ u ≤ cdf μ x :=
  cdfQuantile_le_iff μ hu

/-- Quantiles are monotone on the probability interval. -/
example (μ : Measure ℝ) : MonotoneOn (cdfQuantile μ) (Ioo 0 1) :=
  cdfQuantile_monoOn μ

/-- The public pushforward theorem constructs any real probability law from
the uniform law on `[0, 1]`. -/
example (μ : Measure ℝ) [IsProbabilityMeasure μ] :
    Measure.map (cdfQuantile μ) (volume.restrict (Icc (0 : ℝ) 1)) = μ :=
  map_cdfQuantile_restrict_Icc μ

end ProbabilityTheory
