/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import MathlibExt.Probability.Statistics.DifferenceInDifferences

/-!
# Violations of parallel trends and dependence on the outcome scale

The two examples isolate different failures of identification by difference-in-differences:
unequal untreated changes with no treatment effect, and equality of the untreated changes
in levels but not after a logarithmic transformation.
-/

open MeasureTheory
open MathlibExt.Probability.Causality

namespace MathlibExt.Probability.Statistics.DifferenceInDifferences

private theorem average_eq_of_eq_on {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} [IsFiniteMeasure μ] {s : Set Ω} (hs : MeasurableSet s) (hμs : μ s ≠ 0)
    {f : Ω → ℝ} (c : ℝ) (hf : ∀ ω ∈ s, f ω = c) :
    (⨍ ω in s, f ω ∂μ) = c := by
  calc
    (⨍ ω in s, f ω ∂μ) = ⨍ _ in s, c ∂μ := by
      apply average_congr
      filter_upwards [ae_restrict_mem hs] with ω hω
      exact hf ω hω
    _ = c := setAverage_const hμs (measure_ne_top μ s) c

private theorem observed_same {Ω : Type*} (G : Set Ω) (Y : Ω → ℝ) :
    observed G Y Y = Y := by
  funext ω
  by_cases hω : ω ∈ G
  · have hgc : ω ∉ Gᶜ := by simpa using hω
    simp [observed, Set.indicator_of_mem hω, Set.indicator_of_notMem hgc]
  · have hgc : ω ∈ Gᶜ := hω
    simp [observed, Set.indicator_of_notMem hω, Set.indicator_of_mem hgc]

@[expose] public section

/-- **Violations of parallel trends and their dependence on outcome scale.** On any probability
space with positive masses for both groups, take the treated group to be `G`. First, put all
pre-period outcomes at zero and both post-period potential outcomes at one on `G` and zero on
its complement. The observed DiD is one but the post-period ATT is zero. Second, take untreated
outcomes from two to three on `G` and from one to two on its complement. Both trends are one
in levels, so their DiD is zero. On the log scale the treated trend is strictly smaller,
so their DiD is negative. These deterministic examples illustrate the functional-form issue
studied by Roth and Sant'Anna (2023), without asserting their characterization of invariance. -/
theorem parallelTrends_counterexamples {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (G : Set Ω) (hG : MeasurableSet G)
    (hμG : μ G ≠ 0) (hμGc : μ Gᶜ ≠ 0) :
    let Z : Ω → ℝ := fun _ => 0
    let I : Ω → ℝ := G.indicator fun _ => 1
    let pre : Ω → ℝ := fun ω => 1 + I ω
    let post : Ω → ℝ := fun ω => 2 + I ω
    (didEstimand μ G (observed G Z Z) (observed G I I) = 1 ∧ attPost μ G I I = 0) ∧
      (didEstimand μ G pre post = 0 ∧
        didEstimand μ G (Real.log ∘ pre) (Real.log ∘ post) < 0) := by
  intro Z I pre post
  have hI (ω : Ω) (hω : ω ∈ G) : I ω = 1 := Set.indicator_of_mem hω _
  have hIc (ω : Ω) (hω : ω ∈ Gᶜ) : I ω = 0 := Set.indicator_of_notMem hω _
  constructor
  · rw [observed_same, observed_same]
    constructor
    · unfold didEstimand
      rw [average_eq_of_eq_on hG hμG 1 (fun ω hω => by simp [Z, hI ω hω]),
        average_eq_of_eq_on hG.compl hμGc 0 (fun ω hω => by simp [Z, hIc ω hω])]
      norm_num
    · simp [attPost]
  · constructor
    · unfold didEstimand
      rw [average_eq_of_eq_on hG hμG 1 (fun ω hω => by norm_num [pre, post, hI ω hω]),
        average_eq_of_eq_on hG.compl hμGc 1 (fun ω hω => by norm_num [pre, post, hIc ω hω])]
      exact sub_self _
    · unfold didEstimand
      rw [average_eq_of_eq_on hG hμG (Real.log 3 - Real.log 2)
          (fun ω hω => by norm_num [pre, post, hI ω hω]),
        average_eq_of_eq_on hG.compl hμGc (Real.log 2 - Real.log 1)
          (fun ω hω => by norm_num [pre, post, hIc ω hω]),
        ← Real.log_div (by norm_num : (3 : ℝ) ≠ 0) (by norm_num : (2 : ℝ) ≠ 0),
        Real.log_one, sub_zero, sub_lt_zero]
      exact Real.log_lt_log (by norm_num) (by norm_num)

end

end MathlibExt.Probability.Statistics.DifferenceInDifferences
