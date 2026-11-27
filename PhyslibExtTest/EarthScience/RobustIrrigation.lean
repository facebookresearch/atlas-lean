/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

import PhyslibExt.EarthScience.RobustIrrigation
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum

/-!
# Checks for robust irrigation feasibility

## i. Overview

The same uncertain gain can allow a unique action, or no robust action at all, depending
on the width of the storage band. Feedback over two steps uses the observed storage.

## ii. Key results

These examples distinguish hindsight from a fixed rule and reachable states from all safe states.

## iii. Table of contents

- A. One-step choices
- B. Two steps and the empty horizon

## iv. References

- `PhyslibExt.EarthScience.RobustIrrigation`
-/

namespace PhyslibExtTest.EarthScience.RobustIrrigation

open Set EarthScience.Irrigation

/-- Both endpoints are possible, as are the gains in between. -/
private def forecast : NonemptyInterval ℝ := ⟨(-2, 0), by norm_num⟩

/-! ## A. One-step choices -/

-- At the lower storage boundary the only robust depth is the full cap. The two forecast
-- endpoints then give next storages 1 and 3, hitting both boundaries.
example : actionInterval 1 3 2 1 forecast = {2} := by
  norm_num [actionInterval, forecast, max_def, min_def]

-- Narrow the storage band to [3,4]. Seeing w first permits a = -w, but the dry endpoint
-- requires a ≥ 2 and the wet one requires a ≤ 1. No single irrigation depth meets both.
example : (∀ w ∈ forecast, ∃ a ∈ Icc (0 : ℝ) 2, 3 + a + w ∈ Icc 3 4) ∧
    ¬ ∃ a ∈ Icc (0 : ℝ) 2, ∀ w ∈ forecast, 3 + a + w ∈ Icc 3 4 := by
  constructor
  · intro w hw
    change -2 ≤ w ∧ w ≤ 0 at hw
    refine ⟨-w, ⟨by linarith [hw.2], by linarith [hw.1]⟩, ?_⟩
    constructor <;> linarith
  · rintro ⟨a, ha, hSafe⟩
    have h := mem_actionInterval_iff.mpr ⟨ha, hSafe⟩
    norm_num [actionInterval, forecast, mem_Icc, max_def, min_def] at h

/-! ## B. Two steps and the empty horizon -/

-- The rule fills to 3 before each gain. From storage 2 it first chooses 1; its next
-- choice depends on the first disturbance. All intermediate and terminal storages are safe.
example (w : Fin 2 → ℝ) (hw : ∀ k, w k ∈ forecast) :
    ∀ t (ht : t ≤ 2), storage (fun _ s => 3 - s) 2 w t ht ∈ Icc 1 3 := by
  apply storage_mem_of_mem_actionInterval (cap := 2) (forecast := fun _ => forecast) _
    (by norm_num [mem_Icc]) hw
  intro k s hs
  apply mem_actionInterval_iff.mpr
  refine ⟨⟨by linarith [hs.2], by linarith [hs.1]⟩, ?_⟩
  intro v hv
  change -2 ≤ v ∧ v ≤ 0 at hv
  exact ⟨by linarith [hv.1], by linarith [hv.2]⟩

-- The second action distinguishes two possible first gains, and has no dependence on w 1.
example (w : Fin 2 → ℝ) :
    3 - storage (fun _ s => 3 - s) 2 w 1 (by decide) = -(w 0) := by
  change 3 - (2 + (3 - 2) + w 0) = -(w 0)
  linarith

/-- A nonnegative gain of at most half a unit per step. -/
private noncomputable def rain : NonemptyInterval ℝ := ⟨(0, 1 / 2), by norm_num⟩

-- From zero, two gains of at most 1/2 fit even without irrigation. Storage 1 is safe,
-- but cannot be reached before the last gain and offers no robust action against more rain.
example : (∀ w : Fin 2 → ℝ, (∀ k, w k ∈ rain) →
      ∀ t (ht : t ≤ 2), storage (fun _ _ => 0) 0 w t ht ∈ Icc 0 1) ∧
    ¬ (actionInterval 0 1 0 1 rain).Nonempty := by
  constructor
  · intro w hw
    apply storage_mem_of_mem_actionInterval_on_path (cap := 0) (forecast := fun _ => rain)
      (fun _ _ => 0) (by norm_num [mem_Icc]) w hw
    intro k s _
    have hpre : s ∈ Icc 0 (1 / 2) := by
      obtain ⟨j, hj⟩ := k
      have : j = 0 ∨ j = 1 := by omega
      rcases this with rfl | rfl
      · change (0 : ℝ) ∈ Icc 0 (1 / 2)
        norm_num [mem_Icc]
      · change 0 + 0 + w 0 ∈ Icc 0 (1 / 2)
        simpa only [zero_add] using (show w 0 ∈ Icc 0 (1 / 2) from hw 0)
    apply mem_actionInterval_iff.mpr
    refine ⟨⟨le_rfl, le_rfl⟩, ?_⟩
    intro v hv
    have hv' : 0 ≤ v ∧ v ≤ 1 / 2 := hv
    constructor <;> linarith [hpre.1, hpre.2, hv'.1, hv'.2]
  · norm_num [actionInterval, rain, nonempty_Icc, max_def, min_def]

-- No cap or forecast is needed before the first step.
example (rule : Fin 0 → ℝ → ℝ) (s₀ : ℝ) (w : Fin 0 → ℝ) :
    storage rule s₀ w 0 le_rfl = s₀ := rfl

end PhyslibExtTest.EarthScience.RobustIrrigation
