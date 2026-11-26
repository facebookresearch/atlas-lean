/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import CSLibExt.Computability.BusyBeaverOnesFour

/-!
# Four-state Busy Beaver score tests

Apply the score bound to an arbitrary halting tape and extract a halting witness attaining 13.
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
