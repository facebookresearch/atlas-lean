/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

import Mathlib.MeasureTheory.Measure.Typeclasses.Probability
import Mathlib.Tactic.NormNum

import MathlibExt.Probability.Reliability.LimitState

/-!
# Limit-state checks

Focused checks for `MathlibExt.Probability.Reliability.LimitState`:
resistance equal to load is failure; the fully dependent choice `S = R`
fails with probability one under any probability measure; and the a.e.
monotonicity applies for the zero measure even though the pointwise order
fails everywhere.

These are elaboration and non-vacuity checks, not new results.
-/

open MeasureTheory Set Reliability

/-- Equality of resistance and load is failure, at every outcome. -/
example {Ω : Type*} (R : Ω → ℝ) (ω : Ω) : ω ∈ failureEvent R R :=
  mem_failureEvent.mpr le_rfl

/-- With load identical to resistance, failure is certain under any
probability measure. -/
example {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω}
    [IsProbabilityMeasure μ] (R : Ω → ℝ) :
    μ (failureEvent R R) = 1 := by
  have h : failureEvent R R = Set.univ := by
    ext ω
    simp [mem_failureEvent]
  rw [h]
  exact measure_univ

/-- The a.e. hypothesis is genuinely weaker than pointwise: for the zero
measure it holds between `R = 1` and `R' = 0`, although the pointwise order
fails at every outcome. -/
example :
    (0 : Measure Bool) (failureEvent (fun _ => (0 : ℝ)) (fun _ => (0 : ℝ)))
      ≤ (0 : Measure Bool) (failureEvent (fun _ => (1 : ℝ)) (fun _ => (0 : ℝ)))
    ∧ ¬ ∀ _ω : Bool, (1 : ℝ) ≤ 0 := by
  refine ⟨measure_failureEvent_le_of_le_ae_resistance (μ := (0 : Measure Bool)) ?_, ?_⟩
  · simp [Filter.EventuallyLE]
  · simp
