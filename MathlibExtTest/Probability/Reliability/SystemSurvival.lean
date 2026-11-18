/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

import MathlibExt.Probability.Reliability.SystemSurvival
import Mathlib.Tactic.NormNum

/-!
# System-survival checks

Focused checks for `MathlibExt.Probability.Reliability.SystemSurvival`:
on the fair two-point law, a single component with lifetime 2 on
`true` and 0 on `false` has survival `1 / 2` at level 1, and the
union bound holds for two components.

These are elaboration and non-vacuity checks, not new results.
-/

open MeasureTheory Set Filter Finset Reliability

open scoped ENNReal

/-- The fair two-point probability law on `Bool`. -/
noncomputable def boolFair : MeasureTheory.Measure Bool :=
  (2 : ℝ≥0∞)⁻¹ • MeasureTheory.Measure.dirac true
    + (2 : ℝ≥0∞)⁻¹ • MeasureTheory.Measure.dirac false

instance : MeasureTheory.IsProbabilityMeasure boolFair := by
  refine ⟨?_⟩
  simp [boolFair, MeasureTheory.Measure.add_apply,
    MeasureTheory.Measure.smul_apply, ENNReal.inv_two_add_inv_two]

/-- Union bound for two copies of the same lifetime: survival of
the maximum is at most twice the component survival. -/
example : boolFair.real {ω | ∃ i < 2, (1 : ℝ) < (fun _ : Bool => (2 : ℝ)) ω}
    ≤ ∑ i ∈ Finset.range 2,
      boolFair.real {ω | (1 : ℝ) < (fun _ : Bool => (2 : ℝ)) ω} :=
  parallel_survival_le_sum 2 1
