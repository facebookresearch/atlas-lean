/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import CSLibExt.Computability.BusyBeaverStepsFour

/-!
# Four-state Busy Beaver runtime tests

The 107-step cutoff decides blank-tape halting, and a machine still running after 106 steps
can halt on the next step.
-/

open Cslib.BusyBeaver Cslib.BusyBeaverWanted

example (M : Machine 4) : Halts M ↔ HaltsWithin M 107 := by
  refine ⟨fun h => haltsWithin_mono (haltsWithin_haltTime M h) ?_, fun h => ⟨107, h⟩⟩
  simpa only [busyBeaverSteps_four_wanted] using haltTime_le_busyBeaverSteps M h

example : ∃ M : Machine 4, ¬ HaltsWithin M 106 ∧ HaltsWithin M 107 := by
  obtain ⟨M, hM⟩ := exists_stepsOf_eq 4
  rw [busyBeaverSteps_four_wanted] at hM
  by_cases h : Halts M
  · simp only [stepsOf, dite_eq_left h] at hM
    refine ⟨M, fun h106 => ?_, hM ▸ haltsWithin_haltTime M h⟩
    have := haltTime_le M h h106
    omega
  · simp [stepsOf, h] at hM
