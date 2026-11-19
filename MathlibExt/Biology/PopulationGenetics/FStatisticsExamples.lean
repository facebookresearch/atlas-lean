/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Biology.PopulationGenetics.FStatistics
public import Mathlib.Probability.Distributions.Gaussian.Real

/-!
# A Gaussian drift model whose frequency leaves `[0, 1]`

`DriftModel` records only second-moment information: square-integrable root and increments,
pairwise uncorrelated increments, and drift lengths given by second moments. It deliberately does
not assume that the resulting population frequencies lie in `[0, 1]`.

This file gives the smallest example showing that. With one edge, one population, root frequency
`1 / 2`, and a standard Gaussian increment, the frequency is `1 / 2 + ω`. It exceeds `1` on
`(1 / 2, ∞)`, a set of positive Gaussian measure, so
`gaussianDriftModel_freq_not_mem_Icc_pos` says the frequency leaves `[0, 1]` with positive
probability.

## Main results

* `gaussianDriftModel`: the one-edge Gaussian drift model.
* `gaussianDriftModel_freq`: its frequency is `1 / 2 + ω`.
* `gaussianDriftModel_freq_not_mem_Icc_pos`: the frequency is outside `[0, 1]` with positive
  probability.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory MathlibExt.Biology.PopulationGenetics.FStatistics

namespace MathlibExt.Biology.PopulationGenetics.FStatisticsExamples

/-- A one-edge, one-population drift model with root frequency `1 / 2` and a standard Gaussian
increment. The single edge makes the uncorrelatedness condition vacuous; the point of the example
is the range of the resulting frequency. -/
noncomputable def gaussianDriftModel : DriftModel (gaussianReal 0 1) Unit Unit where
  root _ := 1 / 2
  incr _ := fun ω => ω
  len _ := 1
  weight _ _ := 1
  memLp_root := memLp_const _
  memLp_incr _ := memLp_id_gaussianReal' 2 (by simp)
  inner_incr e f h := absurd (Subsingleton.elim e f) h
  sq_incr _ := by
    have h := variance_id_gaussianReal (μ := 0) (v := 1)
    have hm : ∫ x, id x ∂gaussianReal 0 1 = 0 := integral_id_gaussianReal
    rw [variance_eq_integral measurable_id.aemeasurable, hm] at h
    simpa using h

/-- The Gaussian drift model's frequency is `1 / 2 + ω`. -/
theorem gaussianDriftModel_freq (ω : ℝ) : gaussianDriftModel.freq () ω = 1 / 2 + ω := by
  simp [DriftModel.freq, gaussianDriftModel]

/-- The Gaussian drift model's frequency lies outside `[0, 1]` on a non-null set. -/
theorem gaussianDriftModel_freq_not_mem_Icc :
    gaussianReal 0 1 {ω | gaussianDriftModel.freq () ω ∉ Set.Icc (0 : ℝ) 1} ≠ 0 := by
  have hsub : Set.Ioi (1 / 2 : ℝ) ⊆ {ω | gaussianDriftModel.freq () ω ∉ Set.Icc (0 : ℝ) 1} := by
    intro ω hω
    simp only [Set.mem_Ioi] at hω
    simp only [Set.mem_ofPred_eq]
    rw [gaussianDriftModel_freq]
    intro h
    linarith [h.2]
  intro h0
  have hvol : (volume : Measure ℝ) (Set.Ioi (1 / 2 : ℝ)) = 0 :=
    gaussianReal_absolutelyContinuous' 0 one_ne_zero (measure_mono_null hsub h0)
  simp at hvol

/-- The Gaussian drift model's frequency lies outside `[0, 1]` with positive probability. -/
theorem gaussianDriftModel_freq_not_mem_Icc_pos :
    0 < gaussianReal 0 1 {ω | gaussianDriftModel.freq () ω ∉ Set.Icc (0 : ℝ) 1} :=
  pos_iff_ne_zero.mpr gaussianDriftModel_freq_not_mem_Icc

end MathlibExt.Biology.PopulationGenetics.FStatisticsExamples
