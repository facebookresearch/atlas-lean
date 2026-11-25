/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import CSLibExt.Computability.BusyBeaverStepsThree

/-!
# Three-state Busy Beaver runtime tests

The 21-step cutoff decides blank-tape halting, and a machine still running after 20 steps
can halt on the next step.
-/

open Cslib.BusyBeaver Cslib.BusyBeaverWanted

example (M : Machine 3) : Halts M ↔ HaltsWithin M 21 := by
  refine ⟨fun h => haltsWithin_mono (haltsWithin_haltTime M h) ?_, fun h => ⟨21, h⟩⟩
  simpa only [busyBeaverSteps_three_wanted] using haltTime_le_busyBeaverSteps M h

example : ∃ M : Machine 3, ¬ HaltsWithin M 20 ∧ HaltsWithin M 21 := by
  obtain ⟨M, hM⟩ := exists_stepsOf_eq 3
  rw [busyBeaverSteps_three_wanted] at hM
  by_cases h : Halts M
  · simp only [stepsOf, dite_eq_left h] at hM
    refine ⟨M, fun h₂₀ => ?_, hM ▸ haltsWithin_haltTime M h⟩
    have := haltTime_le M h h₂₀
    omega
  · simp [stepsOf, h] at hM
