/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import Mathlib.Probability.Distributions.Bernoulli
import MathlibExt.Probability.Statistics.ParallelTrends

/-! # A two-group witness for the parallel-trends counterexamples -/

open MeasureTheory ProbabilityTheory unitInterval
open MathlibExt.Probability.Causality
open MathlibExt.Probability.Statistics.DifferenceInDifferences

-- A fair binary population gives each group positive mass.
example :
    let μ := bernoulliMeasure true false (⟨1 / 2, by constructor <;> norm_num⟩ : I)
    let G : Set Bool := {true}
    let post₀ : Bool → ℝ := G.indicator fun _ => 1
    let pre : Bool → ℝ := fun ω => 1 + post₀ ω
    let post : Bool → ℝ := fun ω => 2 + post₀ ω
    (didEstimand μ G (observed G (fun _ => 0) (fun _ => 0)) (observed G post₀ post₀) = 1 ∧
      attPost μ G post₀ post₀ = 0) ∧
    (didEstimand μ G pre post = 0 ∧
      didEstimand μ G (Real.log ∘ pre) (Real.log ∘ post) < 0) := by
  intro μ G post₀ pre post
  let half : I := ⟨1 / 2, by constructor <;> norm_num⟩
  have hG : MeasurableSet G := measurableSet_singleton true
  have hGmass : μ.real G = 1 / 2 := by
    change (bernoulliMeasure true false half).real G = 1 / 2
    rw [bernoulliMeasure_real_apply_of_mem_of_notMem half hG
      (by simp [G]) (by simp [G])]
  have hGcmass : μ.real Gᶜ = 1 / 2 := by
    change (bernoulliMeasure true false half).real Gᶜ = 1 / 2
    rw [bernoulliMeasure_real_apply_of_notMem_of_mem half hG.compl
      (by simp [G]) (by simp [G])]
    norm_num [half]
  have hμG : μ G ≠ 0 := by
    intro hz
    norm_num [Measure.real, hz] at hGmass
  have hμGc : μ Gᶜ ≠ 0 := by
    intro hz
    norm_num [Measure.real, hz] at hGcmass
  exact parallelTrends_counterexamples μ G hG hμG hμGc
