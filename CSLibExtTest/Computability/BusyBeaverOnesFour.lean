/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import CSLibExt.Computability.BusyBeaverOnesFour
import all CSLibExt.Computability.BusyBeaverStepsFour.Checker

/-!
# Four-state Busy Beaver score tests

Apply the score bound to an arbitrary halting tape and extract a halting witness attaining 13.
Check that a halting write that would raise the score to 14 is rejected.
-/

open Cslib.BusyBeaver Cslib.BusyBeaverWanted

example (M : Machine 4) (h : Halts M) : onesAt M (haltTime M h) ≤ 13 := by
  simpa only [scoreOf, dite_eq_left h, busyBeaverOnes_four_wanted] using
    scoreOf_le_busyBeaverOnes M

example : ∃ (M : Machine 4) (h : Halts M), onesAt M (haltTime M h) = 13 := by
  obtain ⟨M, hM⟩ := exists_scoreOf_eq 4
  rw [busyBeaverOnes_four_wanted] at hM
  by_cases h : Halts M
  · exact ⟨M, h, by simpa only [scoreOf, dite_eq_left h] using hM⟩
  · simp [scoreOf, h] at hM

section

open Cslib.BusyBeaverWanted.busyBeaverSteps_four_wanted

-- The low 13 bits mark cells to the left of the blank scanned cell.
private def scoreBoundaryPoint : Point := ⟨0, ⟨8191, 0, 0⟩, 13⟩

example : (scoreBoundaryPoint.tape.write 0).ones.card = 13 := by decide +kernel

example : (scoreBoundaryPoint.tape.write 1).ones.card = 14 := by decide +kernel

example : haltScoreOK scoreBoundaryPoint = false := by decide +kernel

end
