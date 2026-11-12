/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import Mathlib.MeasureTheory.Measure.Typeclasses.Probability

/-!
# Measurements, sampling, and calibration

With known calibration `y = a * x + b + ε`, `a ≠ 0`, and `E[ε] = 0`,
the estimator `(y - b) / a` is unbiased for fixed `x`.

## i. Overview

Pointwise, the estimator differs from `x` by `ε / a`. In expectation,
with `E[ε] = e`, the estimator's expectation is `x + e / a`; in
particular it is `x` when `e = 0`. Signal/input units and offset units
are explicit in the formula; censoring is not encoded as zero. A fitted
`a` creates a different nonlinear bias problem and is out of scope.
Slope `0` is excluded: the estimator is undefined there.

## ii. Key results

- `EarthScience.calibration_estimator_error`: pointwise error `ε / a`.
- `EarthScience.calibration_estimator_expectation`: expectation
  `x + e / a`.

## iii. Table of contents

- A. Pointwise error
- B. Expectation

## iv. References

- `MeasureTheory.integral_add`, `MeasureTheory.integral_div`,
  `MeasureTheory.Integrable.div_const` (Mathlib).

## A. Pointwise error
-/

@[expose] public section

open MeasureTheory ProbabilityTheory

namespace EarthScience

/-- Pointwise calibration error: with `y = a * x + b + ε`, the
calibrated estimator `(y - b) / a` differs from `x` by `ε / a`. -/
theorem calibration_estimator_error {a b x ε : ℝ} (ha : a ≠ 0) :
    ((a * x + b + ε - b) / a) - x = ε / a := by
  field_simp
  ring

/-! ## B. Expectation -/

/-- Unbiasedness of the calibrated estimator: with known calibration
`y = a * x + b + ε`, `a ≠ 0`, integrable error `ε` whose expectation is
`e`, the expectation of the estimator `(y - b) / a` is `x + e / a`.
In particular when `E[ε] = 0` it is exactly `x`. A fitted `a` creates
a different nonlinear bias problem and is out of scope. -/
theorem calibration_estimator_expectation {Ω : Type*} {mΩ : MeasurableSpace Ω}
    {μ : Measure Ω} [IsProbabilityMeasure μ]
    {a b x e : ℝ} (ha : a ≠ 0) {ε : Ω → ℝ}
    (hInt : Integrable ε μ) (hMean : ∫ ω, ε ω ∂μ = e) :
    ∫ ω, ((a * x + b + ε ω - b) / a) ∂μ = x + e / a := by
  have hpt : ∀ ω, ((a * x + b + ε ω - b) / a) = x + ε ω / a := fun ω => by
    field_simp
    ring
  simp_rw [hpt]
  have h1 : Integrable (fun _ : Ω => x) μ := integrable_const x
  have h2 : Integrable (fun ω => ε ω / a) μ := hInt.div_const a
  rw [integral_add h1 h2]
  have hconst : ∫ _ : Ω, x ∂μ = x := by simp
  have hdiv : ∫ ω, ε ω / a ∂μ = e / a := by
    rw [integral_div, hMean]
  rw [hconst, hdiv]

end EarthScience
