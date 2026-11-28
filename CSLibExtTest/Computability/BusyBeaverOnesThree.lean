/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import CSLibExt.Computability.BusyBeaverOnesThree

/-!
# Three-state Busy Beaver score tests

Apply the maximum to an arbitrary halting tape and extract a halting witness attaining six.
-/

open Cslib.BusyBeaver Cslib.BusyBeaverWanted

example (M : Machine 3) (h : Halts M) : onesAt M (haltTime M h) ≤ 6 := by
  simpa only [scoreOf, dite_eq_left h, busyBeaverOnes_three_wanted] using
    scoreOf_le_busyBeaverOnes M

example : ∃ (M : Machine 3) (h : Halts M), onesAt M (haltTime M h) = 6 := by
  obtain ⟨M, hm⟩ := exists_scoreOf_eq 3
  rw [busyBeaverOnes_three_wanted] at hm
  by_cases h : Halts M
  · exact ⟨M, h, by simpa only [scoreOf, dite_eq_left h] using hm⟩
  · simp [scoreOf, h] at hm
