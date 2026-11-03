/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Probability.Statistics.CochranQ

@[expose] public section

open MeasureTheory ProbabilityTheory
open MathlibExt.Probability.Statistics.MetaAnalysis

namespace MathlibExtTest.Probability.Statistics.CochranQ

/-- Identical estimates have no heterogeneity: `Q = 0`. -/
example (v : Fin 3 → ℝ) (c : ℝ) (hv : ∀ i, 0 < v i) : cochranQ v (fun _ => c) = 0 := by
  have hw := sum_inverseVarianceWeights hv (by norm_num)
  simp [cochranQ, ← Finset.sum_mul, hw]

/-- Two unit-variance estimates `0` and `2`: the pooled mean is `1` and `Q = 1 + 1 = 2`. -/
example : cochranQ ![1, 1] ![(0 : ℝ), 2] = 2 := by
  simp [cochranQ, inverseVarianceWeights, Fin.sum_univ_two]
  norm_num

/-- Junk value outside the domain `vᵢ > 0`: a zero variance contributes `0⁻¹ = 0` both as a
weight and as a term, so the estimate `5` is silently ignored and `Q = 0`. -/
example : cochranQ ![0, 1] ![(5 : ℝ), 0] = 0 := by
  simp [cochranQ, inverseVarianceWeights, Fin.sum_univ_two]

/-- Non-vacuity of Cochran's theorem: two independent standard normal coordinates
(`θ = 0`, `v = 1`) give `Q ~ χ²₁`. -/
example : HasLaw (fun x : Fin 2 → ℝ => cochranQ (fun _ => (1 : ℝ)) fun i => x i)
    (chiSquareMeasure 1) (Measure.pi fun _ : Fin 2 => gaussianReal 0 1) := by
  have h := hasLaw_cochranQ (k := 2) le_rfl (μ := Measure.pi fun _ : Fin 2 => gaussianReal 0 1)
    (θ := 0) (v := fun _ => 1) (fun _ => one_ne_zero) (X := fun i x => x i)
    (fun i => (measurePreserving_eval (fun _ : Fin 2 => gaussianReal 0 1) i).hasLaw)
    (iIndepFun_pi (X := fun _ (y : ℝ) => y) fun _ => measurable_id.aemeasurable)
  simpa using h

end MathlibExtTest.Probability.Statistics.CochranQ
