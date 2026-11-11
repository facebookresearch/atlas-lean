/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

import MathlibExt.Probability.M09SampleMean

/-!
# Sample-mean checks

Concrete consumers of `MathlibExt.Probability.M09SampleMean`: the
`n = 1` case (sample mean is the single variable), the degenerate
`sigma2 = 0` case, and the public shape of both theorems.

## i. Overview

These are elaboration and non-vacuity checks, not new results.

## ii. Key results

No new definitions or results are introduced here.

## iii. Table of contents

- A. `n = 1`
- B. Degenerate variance

## iv. References

- `MathlibExt.Probability.M09SampleMean`
-/

open MeasureTheory ProbabilityTheory

/-- `n = 1`: the sample mean of a single variable is the variable. -/
example {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω}
    [IsProbabilityMeasure μ] {X : Fin 1 → Ω → ℝ} {mu : ℝ}
    (hInt : ∀ i, Integrable (X i) μ) (hMean : ∀ i, ∫ ω, X i ω ∂μ = mu) :
    ∫ ω, (∑ i, X i ω) / (Fintype.card (Fin 1) : ℝ) ∂μ = mu :=
  EarthScience.integral_sample_mean hInt hMean

/-- Degenerate variance: common variance `0` gives sample-mean
variance `0` for any `n`. -/
example {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω}
    [IsProbabilityMeasure μ] {ι : Type*} [Fintype ι] [Nonempty ι]
    {X : ι → Ω → ℝ}
    (hLp : ∀ i, MemLp (X i) 2 μ)
    (hIndep : iIndepFun (fun i => X i) μ)
    (hVar : ∀ i, variance (X i) μ = 0) :
    variance (fun ω => (∑ i, X i ω) / (Fintype.card ι : ℝ)) μ = 0 := by
  have h := EarthScience.variance_sample_mean (sigma2 := 0) hLp hIndep hVar
  simpa using h
