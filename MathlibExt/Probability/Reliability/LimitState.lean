/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.MeasureTheory.Constructions.BorelSpace.Order
import Mathlib.MeasureTheory.OuterMeasure.AE

/-!
# Limit-state failure events

For a resistance variable `R` and a load-effect variable `S` on one outcome
space, the limit-state failure event is `{R - S ≤ 0}` (equality counts as
failure). This module gives its membership form and measurability, and the
two monotonicity statements: an almost-everywhere resistance increase, or
an almost-everywhere load decrease, can only decrease the failure measure.
No independence between `R` and `S` is assumed.

## Main results

* `Reliability.mem_failureEvent`: membership is `R ω ≤ S ω`.
* `Reliability.measurableSet_failureEvent`: measurability from measurability
  of `R` and `S`.
* `Reliability.measure_failureEvent_le_of_le_ae_resistance` and
  `Reliability.measure_failureEvent_le_of_le_ae_load`: a.e. monotonicity of
  the failure measure.
-/

@[expose] public section

namespace Reliability

open MeasureTheory Set Filter

/-- The limit-state failure event for resistance `R` and load effect `S`
on a common outcome space: failure is `R - S ≤ 0`, so equality `R = S`
counts as failure. No independence of `R` and `S` is assumed. -/
def failureEvent {Ω : Type*} (R S : Ω → ℝ) : Set Ω :=
  {ω | R ω - S ω ≤ 0}

/-- Membership in the failure event is the physical comparison `R ω ≤ S ω`
(failure at equality included). -/
theorem mem_failureEvent {Ω : Type*} {R S : Ω → ℝ} {ω : Ω} :
    ω ∈ failureEvent R S ↔ R ω ≤ S ω := by
  show R ω - S ω ≤ 0 ↔ R ω ≤ S ω
  exact sub_nonpos

/-- The failure event of measurable resistance and load variables is
measurable. -/
theorem measurableSet_failureEvent {Ω : Type*} {mΩ : MeasurableSpace Ω}
    {R S : Ω → ℝ} (hR : Measurable R) (hS : Measurable S) :
    MeasurableSet (failureEvent R S) := by
  exact measurableSet_le (hR.sub hS) measurable_const

/-- Increasing the resistance almost everywhere can only decrease the
failure measure; for a probability measure this is the failure
probability. -/
theorem measure_failureEvent_le_of_le_ae_resistance {Ω : Type*}
    {mΩ : MeasurableSpace Ω} {μ : Measure Ω} {R R' S : Ω → ℝ}
    (h : R ≤ᵐ[μ] R') :
    μ (failureEvent R' S) ≤ μ (failureEvent R S) := by
  apply measure_mono_ae
  filter_upwards [h] with ω hω hmem
  rw [mem_failureEvent] at hmem ⊢
  exact hω.trans hmem

/-- Decreasing the load effect almost everywhere can only decrease the
failure measure; for a probability measure this is the failure
probability. -/
theorem measure_failureEvent_le_of_le_ae_load {Ω : Type*}
    {mΩ : MeasurableSpace Ω} {μ : Measure Ω} {R S S' : Ω → ℝ}
    (h : S' ≤ᵐ[μ] S) :
    μ (failureEvent R S') ≤ μ (failureEvent R S) := by
  apply measure_mono_ae
  filter_upwards [h] with ω hω hmem
  rw [mem_failureEvent] at hmem ⊢
  exact hmem.trans hω

end Reliability
