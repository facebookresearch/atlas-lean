/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import CSLibExt.Complexity.BooleanFunctions.KKL.KKLEvents
public import CSLibExtTest.Complexity.BooleanFunctions.KKL.KKLInequality

/-!
# Tests for the KKL inequality for events

Tests for `CSLibExt.Complexity.BooleanFunctions.KKL.KKLWire`:

* `StatMech.prob`, `StatMech.BeffaraDC.influence` and `kklw_logMaxInfl` of the event
  `{ω | ω true ∧ ω false}` at `p = 1/2` are `1/4`, `1/2` and `log 2`;
* non-vacuity of the headline `kklw_hkkl_half`: at that event it is the explicit inequality
  `2 · 3/16 · log 2 ≤ 1`;
* `kklw_sharpThreshold` and `kklw_sharpThreshold_window` take KKL on `(1/2, q)` as a hypothesis,
  which this library proves for no `q > 1/2`; the only instances available here are the
  degenerate ones with `q = 1/2`, where the interior of `[1/2, q]` is empty. The test records
  this instance for the dictator event, an increasing event with `P_{1/2} = 1/2`.
-/

@[expose] public section

namespace StatMechTest.BooleanFunctions

open StatMech StatMech.OSSS StatMech.Probability StatMech.TwoDim

lemma andEvent_indicator : andEvent.indicator (fun _ => (1 : ℝ)) = andInd := by
  funext ω
  cases h₁ : ω true <;> cases h₂ : ω false <;> simp [andEvent, andFun, h₁, h₂]

lemma prob_andEvent : StatMech.prob (1 / 2) andEvent = 1 / 4 := by
  rw [kklw_prob_eq_expect, andEvent_indicator]
  simp [expect, weight, sum_configSpace_bool, andFun, bernoulliWeight]
  norm_num

lemma influence_andEvent (e : Bool) : StatMech.BeffaraDC.influence (1 / 2) andEvent e = 1 / 2 := by
  rw [kklw_influence_eq_infl, andEvent_indicator]; exact infl_andFun e

lemma logMaxInfl_andEvent : kklw_logMaxInfl (1 / 2) andEvent = Real.log 2 := by
  rw [kklw_logMaxInfl, andEvent_indicator, maxInfl_andInd]; norm_num

/-- `kklw_hkkl_half` at the `AND` event: `2 · (1/4 · 3/4) · log 2 ≤ 1/2 + 1/2`. -/
example : 2 * (1 / 4 * (3 / 4)) * Real.log 2 ≤ 1 := by
  have h := kklw_hkkl_half andEvent
  rw [prob_andEvent, logMaxInfl_andEvent, Fintype.sum_bool, influence_andEvent,
    influence_andEvent] at h
  linarith

/-! ## Sharp thresholds: the degenerate instance `q = 1/2` -/

/-- The dictator event `{ω | ω true}`. -/
def dictEvent : Set (ConfigSpace Bool) := {ω | ω true = true}

lemma dictEvent_isIncreasing : IsIncreasing dictEvent := by
  intro ω ω' hle hω
  simp only [dictEvent, Set.mem_ofPred_eq] at hω ⊢
  have := hle true
  rw [hω] at this
  revert this; cases ω' true <;> simp

lemma prob_dictEvent : StatMech.prob (1 / 2) dictEvent = 1 / 2 := by
  rw [kklw_prob_eq_expect]
  simp [expect, weight, sum_configSpace_bool, dictEvent, bernoulliWeight, Set.indicator_apply]
  norm_num

lemma interior_Icc_half : interior (Set.Icc (1 / 2 : ℝ) (1 / 2)) = ∅ := by simp

example : 1 / 2 + (2 * 1 * 1) * ((1 / 2 : ℝ) - 1 / 2) ≤ StatMech.prob (1 / 2) dictEvent :=
  kklw_sharpThreshold dictEvent dictEvent_isIncreasing le_rfl zero_le_one zero_le_one
    prob_dictEvent (by simp) (by simp) (by simp)

example : (1 / 2 : ℝ) - 1 / 2 ≤ (1 / 2 - 1 / 2) / (2 * 1 * 1) :=
  kklw_sharpThreshold_window dictEvent dictEvent_isIncreasing le_rfl (by norm_num)
    prob_dictEvent zero_le_one zero_le_one (by simp) (by simp) (by simp)
    (by rw [prob_dictEvent]; norm_num)

end StatMechTest.BooleanFunctions
