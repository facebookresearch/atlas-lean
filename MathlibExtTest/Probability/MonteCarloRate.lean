/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Probability.MonteCarloRate

open MeasureTheory ProbabilityTheory
open scoped BigOperators

/-- `n = 1`: the sample mean of a single variable is the variable.
No probability-measure hypothesis is needed. -/
example {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω}
    {X : Fin 1 → Ω → ℝ} {mu : ℝ}
    (hInt : ∀ i, Integrable (X i) μ) (hMean : ∀ i, ∫ ω, X i ω ∂μ = mu) :
    ∫ ω, (∑ i, X i ω) / (Fintype.card (Fin 1) : ℝ) ∂μ = mu :=
  MathlibExt.Probability.integral_sample_mean hInt hMean

/-- Degenerate variance: common variance `0` gives sample-mean
variance `0` for any `n`. No probability-measure hypothesis is needed. -/
example {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω}
    {ι : Type*} [Fintype ι] [Nonempty ι]
    {X : ι → Ω → ℝ}
    (hLp : ∀ i, MemLp (X i) 2 μ)
    (hIndep : iIndepFun (fun i => X i) μ)
    (hVar : ∀ i, variance (X i) μ = 0) :
    variance (fun ω => (∑ i, X i ω) / (Fintype.card ι : ℝ)) μ = 0 := by
  have h := MathlibExt.Probability.variance_sample_mean (sigma2 := 0) hLp hIndep hVar
  simpa using h

-- Only the reference sample `X 0` needs to be square-integrable.
example {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
    (X : ℕ → Ω → ℝ) (hIndep : iIndepFun X μ)
    (hIdent : ∀ i, IdentDistrib (X i) (X 0) μ μ)
    (hMemLp : MemLp (X 0) 2 μ) (n : ℕ) (hn : n ≠ 0) :
    variance (fun ω => (∑ i ∈ Finset.range n, X i ω) / (n : ℝ)) μ
      = variance (X 0) μ / (n : ℝ) := by
  exact MathlibExt.Probability.variance_sample_mean_of_iid X hIndep hIdent hMemLp n hn
