/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Probability.Statistics.Resampling.BootstrapQuantile

/-!
# Tests for weak-convergence-to-quantile

The generalized inverse computes on a Dirac law (median of `dirac 0` is `0`), and the
Dirac CDF discontinuity at `0` shows why the continuity hypothesis cannot be dropped.
-/

@[expose] public section

open MeasureTheory Filter
open scoped Topology

namespace ProbabilityTheory

-- Positive/use: the generalized inverse computes on a Dirac law (median of dirac 0 is 0).
example : ProbabilityTheory.cdfQuantile (Measure.dirac (0 : ℝ)) (1 / 2) = 0 := by
  unfold cdfQuantile
  have hmem : ((1 : ℝ) / 2) ∈ Set.Ioo (0 : ℝ) 1 := by norm_num
  simp only [hmem, ↓reduceIte]
  have hset : {x : ℝ | ((1 : ℝ) / 2) ≤ cdf (Measure.dirac (0 : ℝ)) x} = Set.Ici 0 := by
    ext x
    simp only [Set.mem_Ici]
    show (((1 : ℝ) / 2) ≤ cdf (Measure.dirac (0 : ℝ)) x) ↔ _
    rw [cdf_eq_real]
    rw [Measure.dirac_real_apply]
    simp only [Set.indicator_apply, Pi.one_apply]
    by_cases hx : (0 : ℝ) ∈ Set.Iic x
    · simp only [hx, ↓reduceIte]
      have hx0 : (0 : ℝ) ≤ x := Set.mem_Iic.mp hx
      simp only [hx0, iff_true]
      norm_num
    · simp only [hx, ↓reduceIte]
      have hnx : ¬ (0 : ℝ) ≤ x := fun h => hx (Set.mem_Iic.mpr h)
      simp only [hnx, iff_false]
      norm_num
  rw [hset, csInf_Ici]

-- Degenerate: the Dirac CDF is discontinuous at 0, so the continuity hypothesis fails.
example : ¬ Continuous (fun x : ℝ => (Measure.dirac (0 : ℝ)).real (Set.Iic x)) := by
  intro hcont
  have hF0 : (Measure.dirac (0 : ℝ)).real (Set.Iic 0) = 1 := by
    simp
  have hseq : Filter.Tendsto (fun n : ℕ => (-(1 / ((n : ℝ) + 1)) : ℝ)) atTop (𝓝 0) := by
    have h1 : Filter.Tendsto (fun n : ℕ => (1 / ((n : ℝ) + 1) : ℝ)) atTop (𝓝 0) :=
      tendsto_one_div_add_atTop_nhds_zero_nat
    have h2 := h1.neg
    simpa using h2
  have hcomp : Filter.Tendsto (fun n : ℕ => (Measure.dirac (0 : ℝ)).real (Set.Iic (-(1 / ((n : ℝ) + 1)) : ℝ))) atTop (𝓝 ((Measure.dirac (0 : ℝ)).real (Set.Iic 0))) :=
    (hcont.tendsto 0).comp hseq
  have hzero : ∀ n : ℕ, (Measure.dirac (0 : ℝ)).real (Set.Iic (-(1 / ((n : ℝ) + 1)) : ℝ)) = 0 := by
    intro n
    rw [Measure.dirac_real_apply]
    simp only [Set.indicator_apply, Pi.one_apply]
    have hneg : (0 : ℝ) ∉ Set.Iic (-(1 / ((n : ℝ) + 1)) : ℝ) := by
      simp only [Set.mem_Iic, not_le]
      have hpos : (0 : ℝ) < 1 / ((n : ℝ) + 1) := by positivity
      linarith
    simp only [hneg, ↓reduceIte]
  have hconst : Filter.Tendsto (fun n : ℕ => (Measure.dirac (0 : ℝ)).real (Set.Iic (-(1 / ((n : ℝ) + 1)) : ℝ))) atTop (𝓝 0) := by
    simp only [hzero]
    exact tendsto_const_nhds
  have heq := tendsto_nhds_unique hcomp hconst
  rw [hF0] at heq
  norm_num at heq
