/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

import PhyslibExt.EarthScience.D01Calibration

/-!
# Calibration checks

Concrete consumers of `PhyslibExt.EarthScience.D01Calibration`: a
numeric pointwise error, the unbiased case `E[ε] = 0`, a nonzero-mean
error, and the degenerate `ε = 0` case (exact recovery).

## i. Overview

These are elaboration and non-vacuity checks, not new results.

## ii. Key results

No new definitions or results are introduced here.

## iii. Table of contents

- A. Pointwise and zero-mean cases
- B. Nonzero mean and no error

## iv. References

- `PhyslibExt.EarthScience.D01Calibration`
-/

open MeasureTheory ProbabilityTheory

/-- Numeric pointwise error: `a = 2, x = 5, b = 3, ε = 0.4` gives
error `0.2 = ε / a`. -/
example : ((2 * 5 + 3 + (0.4 : ℝ) - 3) / 2) - 5 = (0.4 : ℝ) / 2 :=
  EarthScience.calibration_estimator_error (by norm_num)

/-- Unbiased case: `E[ε] = 0` gives expectation exactly `x`. -/
example {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω}
    [IsProbabilityMeasure μ] {a b x : ℝ} (ha : a ≠ 0) {ε : Ω → ℝ}
    (hInt : Integrable ε μ) (hMean : ∫ ω, ε ω ∂μ = 0) :
    ∫ ω, ((a * x + b + ε ω - b) / a) ∂μ = x := by
  have h : ∫ ω, ((a * x + b + ε ω - b) / a) ∂μ = x + (0 : ℝ) / a :=
    EarthScience.calibration_estimator_expectation (e := (0 : ℝ)) ha hInt hMean
  simpa using h

/-- Nonzero-mean error: `E[ε] = e` shifts the expectation by `e / a`. -/
example {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω}
    [IsProbabilityMeasure μ] {a b x e : ℝ} (ha : a ≠ 0) {ε : Ω → ℝ}
    (hInt : Integrable ε μ) (hMean : ∫ ω, ε ω ∂μ = e) :
    ∫ ω, ((a * x + b + ε ω - b) / a) ∂μ = x + e / a :=
  EarthScience.calibration_estimator_expectation ha hInt hMean

/-- No error: `ε = 0` recovers `x` exactly, pointwise and in
expectation. -/
example {a b x : ℝ} (ha : a ≠ 0) :
    ((a * x + b + (0 : ℝ) - b) / a) - x = (0 : ℝ) / a :=
  EarthScience.calibration_estimator_error ha
