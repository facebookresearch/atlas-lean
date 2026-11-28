/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import PhyslibExt.Reliability.ConditionalFailureEvents
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.NormNum

/-!
# Single-epoch conditional failure checks

Concrete consumers of `PhyslibExt.Reliability.ConditionalFailureEvents`: three scenarios with
weights `(1/2, 1/4, 1/4)`, one component with linear damage `r t` (rates `1, 2, 3`) against the
threshold `2`, a unit-gain sensor with errors `(1, -1, 0)` and the bin `[1, 2]`, all at `t = 1`.
The readings are `(2, 1, 3)`, the bin has probability `3/4`, and the conditional failure
probability is `1/3`, the second scenario failing at equality. The alarm `z ≥ 2` is not the
failure event, the bin and the failure event are dependent under the joint law, and the bin
`[4, 5]` is null. The normalized weights form a distribution, the general conditional-probability
theorem applies to the fixture, and the calibration returns the damage plus the scaled error.

## i. Overview

These are elaboration and non-vacuity checks, not new results.

## ii. Key results

No new results are introduced here. Section A defines the three-scenario fixture and proves its
events, which the later examples use.

## iii. Table of contents

- A. The three-scenario fixture

## iv. References

- `PhyslibExt.Reliability.ConditionalFailureEvents`
-/

@[expose] public section

namespace PhyslibExtTest.Reliability.ConditionalFailureEvents

open _root_.Reliability MathlibExt.Probability.FiniteProbability
open scoped NNReal

/-! ## A. The three-scenario fixture -/

/-- Fixture rates `r = (1, 2, 3)` of the single component in the three scenarios. -/
def fixtureRate : Fin 1 → Fin 3 → ℝ := fun _ => ![1, 2, 3]

/-- Fixture sensor errors `ε = (1, -1, 0)`. -/
def fixtureError : Fin 3 → ℝ := ![1, -1, 0]

/-- Fixture scenario weights `p = (1/2, 1/4, 1/4)`. -/
noncomputable def fixtureWeight : Fin 3 → ℝ := ![1 / 2, 1 / 4, 1 / 4]

/-- The fixture bin event at `t = 1`: unit gain, zero offset, `d0 = 0`, bin `[1, 2]`. -/
noncomputable def fixtureBin : Finset (Fin 3) :=
  binEvent (fun ω => sensorReading 1 0 one_ne_zero (0 + fixtureRate 0 ω * (1 : ℝ≥0))
    (fixtureError ω)) 1 2

/-- The fixture system failure event at `t = 1`: one component, `d0 = 0`, threshold `D = 2`. -/
noncomputable def fixtureFailure : Finset (Fin 3) :=
  systemFailureEvent (seriesEvent (Fin 1)) (fun _ _ => 0) fixtureRate (fun _ _ => 2) 1

/-- **Fixture events.** The readings are `(2, 1, 3)`; the bin `[1, 2]` holds the first two
scenarios, with `P(A) = 3/4`; the component has failed at `t = 1` in the second and third. -/
lemma fixture_bin_failure :
    (fun ω => sensorReading 1 0 one_ne_zero (0 + fixtureRate 0 ω * (1 : ℝ≥0)) (fixtureError ω)) =
        ![2, 1, 3] ∧
      fixtureBin = {0, 1} ∧ prob fixtureWeight fixtureBin = 3 / 4 ∧ fixtureFailure = {1, 2} := by
  have hbin : fixtureBin = {0, 1} := by
    ext ω
    fin_cases ω <;>
      simp [fixtureBin, binEvent, sensorReading, fixtureRate, fixtureError] <;> norm_num
  have hfail : fixtureFailure = {1, 2} := by
    ext ω
    rw [fixtureFailure, mem_systemFailureEvent_iff (isIncreasing_seriesEvent (Fin 1))
      (fun i ω => by fin_cases ω <;> simp [fixtureRate])]
    fin_cases ω <;> norm_num [seriesEvent, fixtureRate]
  refine ⟨?_, hbin, ?_, hfail⟩
  · funext ω
    fin_cases ω <;> simp [sensorReading, fixtureRate, fixtureError] <;> norm_num
  · rw [hbin]
    simp [prob, fixtureWeight]
    norm_num

/-- **Fixture conditional failure probability.** The bin has positive probability, and normalized
on it the failure probability at `t = 1` is `1/3`; the second scenario fails at equality, its
lifetime `(2 - 0) / 2 = 1` being the epoch itself. -/
example :
    ∃ hA : 0 < prob fixtureWeight fixtureBin,
      prob (condWeights fixtureWeight fixtureBin hA) fixtureFailure = 1 / 3 ∧
        damageLifetime (linearDamage (fun _ => 0) (fixtureRate 0)) (fun _ => 2) 1 = 1 ∧
        (1 : Fin 3) ∈ fixtureFailure := by
  obtain ⟨-, hbin, hP, hfail⟩ := fixture_bin_failure
  have hA : 0 < prob fixtureWeight fixtureBin := by rw [hP]; norm_num
  refine ⟨hA, ?_, ?_, by rw [hfail]; simp⟩
  · rw [prob_condWeights, hP, hbin, hfail]
    simp [prob, fixtureWeight]
    norm_num
  · rw [damageLifetime_linearDamage (by simp [fixtureRate]) (by norm_num)]
    simp [fixtureRate]

/-- **Alarm, dependence and a null bin.** The alarm event `{z ≥ 2}` is not the failure event; the
bin and the failure event are not independent under the joint law,
`P(A ∩ F) = 1/4 ≠ 3/8 = P(A) P(F)`; and the bin `[4, 5]` holds no scenario, so it has
probability zero and no normalized law. -/
example :
    Finset.univ.filter (fun ω => 2 ≤ sensorReading 1 0 one_ne_zero
        (0 + fixtureRate 0 ω * (1 : ℝ≥0)) (fixtureError ω)) ≠ fixtureFailure ∧
      prob fixtureWeight (fixtureBin ∩ fixtureFailure) ≠
        prob fixtureWeight fixtureBin * prob fixtureWeight fixtureFailure ∧
      ¬ 0 < prob fixtureWeight (binEvent (fun ω => sensorReading 1 0 one_ne_zero
        (0 + fixtureRate 0 ω * (1 : ℝ≥0)) (fixtureError ω)) 4 5) := by
  obtain ⟨hz, hbin, -, hfail⟩ := fixture_bin_failure
  refine ⟨?_, ?_, ?_⟩
  · rw [hfail]
    intro h
    have h0 : (0 : Fin 3) ∈ Finset.univ.filter (fun ω => 2 ≤ sensorReading 1 0 one_ne_zero
        (0 + fixtureRate 0 ω * (1 : ℝ≥0)) (fixtureError ω)) := by
      simp [sensorReading, fixtureRate, fixtureError]
      norm_num
    rw [h] at h0
    simp at h0
  · rw [hbin, hfail]
    simp [prob, fixtureWeight]
    norm_num
  · rw [prob_pos_iff_nonempty (fun ω => by fin_cases ω <;> norm_num [fixtureWeight]),
      Finset.not_nonempty_iff_eq_empty]
    ext ω
    fin_cases ω <;> simp [binEvent, sensorReading, fixtureRate, fixtureError] <;> norm_num

/-- The weights normalized on the fixture bin form a finite distribution. -/
example (hA : 0 < prob fixtureWeight fixtureBin) :
    (∀ ω, 0 ≤ condWeights fixtureWeight fixtureBin hA ω) ∧
      ∑ ω, condWeights fixtureWeight fixtureBin hA ω = 1 :=
  ⟨(condWeights_isDistribution (fun ω => by fin_cases ω <;> norm_num [fixtureWeight]) hA).1,
    (condWeights_isDistribution (fun ω => by fin_cases ω <;> norm_num [fixtureWeight]) hA).2.1⟩

/-- The general conditional failure theorem applies to the fixture with every hypothesis
discharged: the conditional failure probability is the ratio and lies in `[0, 1]`. -/
example (hA : 0 < prob fixtureWeight fixtureBin) :
    prob (condWeights fixtureWeight fixtureBin hA) fixtureFailure =
        prob fixtureWeight (fixtureBin ∩ fixtureFailure) / prob fixtureWeight fixtureBin ∧
      prob (condWeights fixtureWeight fixtureBin hA) fixtureFailure ∈ Set.Icc 0 1 := by
  have h := prob_condWeights_systemFailureEvent (isIncreasing_seriesEvent (Fin 1))
    (d0 := fun _ _ => 0) (D := fun _ _ => 2)
    (fun i ω => by fin_cases ω <;> norm_num [fixtureRate]) one_ne_zero 0 fixtureError
    fixtureWeight (fun ω => by fin_cases ω <;> norm_num [fixtureWeight]) 1 rfl rfl hA
  exact ⟨h.2.2.1, h.2.2.2.1⟩

/-- Failure at equality through the fixed-time criterion: in the second scenario the damage
`2 * 1` equals the threshold `2`, so the lifetime is at most `1`. -/
example : damageLifetime (linearDamage (fun _ => 0) (fixtureRate 0)) (fun _ => 2) 1 ≤
    ((1 : ℝ≥0) : ENNReal) := by
  rw [damageLifetime_linearDamage_le_iff (by norm_num [fixtureRate])]
  norm_num [fixtureRate]

/-- The calibration of the first scenario's reading `2` returns the damage `1` plus the error
`1`. -/
example : Statistics.CalibrationPorts.gaugeStrain 1 0 (sensorReading 1 0 one_ne_zero 1 1)
    one_ne_zero = 2 := by
  rw [gaugeStrain_sensorReading]
  norm_num

end PhyslibExtTest.Reliability.ConditionalFailureEvents
