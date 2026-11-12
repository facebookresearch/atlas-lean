/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Probability.Statistics.SampleLaw
public import MathlibExt.Probability.Distributions.CochranIndependence
public import Mathlib.MeasureTheory.Measure.Dirac.Basic

@[expose] public section

open MeasureTheory ProbabilityTheory MathlibExt.Probability.Statistics

namespace MathlibExtTest.Probability.Statistics.SampleLaw

/-- `n = 1`: the one-coordinate sample law projects back to `ν`. -/
example {S : Type*} [MeasurableSpace S] (ν : Measure S) [IsProbabilityMeasure ν] :
    (Measure.pi fun _ : Fin 1 => ν).map (fun x => x 0) = ν := by
  exact (measurePreserving_eval (fun _ : Fin 1 => ν) 0).map_eq

/-- `n = 0`: the empty sample law is a Dirac mass (no normalized average is claimed). -/
example {S : Type*} [MeasurableSpace S] (ν : Measure S) [IsProbabilityMeasure ν] :
    Measure.pi (fun _ : Fin 0 => ν) = Measure.dirac (fun i => Fin.elim0 i) := by
  exact Measure.pi_of_empty _ _

/-- Negative check: two coordinates equal to the same fair coin have the right marginals but
are not independent, so `iIndepFun.hasLaw_pi` cannot be applied to them. -/
example : ¬ iIndepFun (fun _ : Fin 2 => (id : Bool → Bool))
    ((2 : ENNReal)⁻¹ • (Measure.dirac true + Measure.dirac false)) := by
  intro h
  have key := (h.indepFun (i := 0) (j := 1) (by decide)).measure_inter_preimage_eq_mul
    {true} {false} (measurableSet_singleton _) (measurableSet_singleton _)
  simp at key

/-- **Use test: Gaussian sample mean.** For independent `Xᵢ ~ N(μ₀, v)`, `i : Fin n`, `n ≥ 1`,
`hasLaw_statistic` with the statistic `x ↦ (∑ i, x i) / n` and the Atlas theorem
`ProbabilityTheory.hasLaw_sampleMean` (provided) give `X̄ ~ N(μ₀, v / n)`. -/
example {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ] {n : ℕ}
    (hn : 0 < n) (μ₀ : ℝ) (v : NNReal) {X : Fin n → Ω → ℝ}
    (hlaw : ∀ i, HasLaw (X i) (gaussianReal μ₀ v) μ) (hind : iIndepFun X μ) :
    HasLaw (fun ω => (∑ i, X i ω) / n) (gaussianReal μ₀ (v / n)) μ := by
  have h := hasLaw_statistic hlaw hind (T := fun x : Fin n → ℝ => (∑ i, x i) / n) (by fun_prop)
  rwa [(hasLaw_sampleMean hn μ₀ v).map_eq] at h

end MathlibExtTest.Probability.Statistics.SampleLaw
