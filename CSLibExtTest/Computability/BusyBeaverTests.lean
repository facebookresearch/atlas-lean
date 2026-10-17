/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.Computability.BusyBeaver

/-!
# Busy Beaver public-API and boundary checks

Exact-statement exercises for Rado's shift and score functions, their
proved values at `0` and `1` states, monotonicity, the marching
one-state non-halting criterion, and the theory-relative first
undecidable index.
-/

@[expose] public section

namespace BusyBeaverTests

open Cslib.BusyBeaver

/-- Proved value `S(0) = 0`. -/
example : busyBeaverSteps 0 = 0 := busyBeaverSteps_zero

/-- Proved value `S(1) = 1`. -/
example : busyBeaverSteps 1 = 1 := busyBeaverSteps_one

/-- Proved value `Σ(1) = 1`. -/
example : busyBeaverOnes 1 = 1 := busyBeaverOnes_one

/-- Every halting time is bounded by the shift function. -/
example {n : ℕ} (M : Machine n) (h : Halts M) :
    haltTime M h ≤ busyBeaverSteps n :=
  haltTime_le_busyBeaverSteps M h

/-- The score function never exceeds the shift function. -/
example (n : ℕ) : busyBeaverOnes n ≤ busyBeaverSteps n :=
  busyBeaverOnes_le_steps n

/-- Both Busy Beaver functions are monotone in the number of states. -/
example (n : ℕ) : busyBeaverSteps n ≤ busyBeaverSteps (n + 1) :=
  busyBeaverSteps_mono n

example (n : ℕ) : busyBeaverOnes n ≤ busyBeaverOnes (n + 1) :=
  busyBeaverOnes_mono n

/-- The one-state machine that writes `1`, moves right, and halts does
so after exactly one step. -/
example :
    (run (fun _ _ => (1, Move.right, none) : Machine 1) 1).state = none :=
  run_one_state _

/-- The one-state machine that always returns to its only state never
halts. -/
example : ¬ Halts (fun _ _ => (1, Move.right, some 0) : Machine 1) :=
  not_halts_of_one_state_march _ rfl

/-- No one-state machine halts at time zero. -/
example (M : Machine 1) : ¬ HaltsWithin M 0 :=
  not_haltsWithin_zero_one M

/-- Ones on the tape are bounded by the number of steps taken. -/
example {n : ℕ} (M : Machine n) (t : ℕ) : onesAt M t ≤ t :=
  onesAt_le_steps M t

/-- The first undecidable size bounds any undecidable size from below. -/
example (T : FormalTheory) {n : ℕ} (h : ¬ DecidesHalting T n) :
    firstUndecidable T ≤ n :=
  firstUndecidable_le_of_not_decides h

/-- Catalogue lower-bound shape: decidability through five states
pushes the first undecidable size to at least six. -/
example (T : FormalTheory) (h5 : ∀ n ≤ 5, DecidesHalting T n)
    (hex : ∃ n, ¬ DecidesHalting T n) :
    6 ≤ firstUndecidable T :=
  six_le_firstUndecidable_of_decides_le_five h5 hex

/-- A consistency-search machine blocks decidability at its size, with
provability read on syntactic sentence codes. -/
example (T : FormalTheory) {n : ℕ} (M : Machine n)
    (hM : Halts M ↔ T.Provable falseSentence)
    (hsound : T.Provable (haltsSentence M) → Halts M)
    (hcons : Consistent T) (hnot : ¬ T.Provable (notHaltsSentence M)) :
    ¬ DecidesHalting T n :=
  not_decides_of_consistency_machine M hM hsound hcons hnot

/-- Halting and false sentence codes are syntactically distinct. -/
example {n : ℕ} (M : Machine n) : haltsSentence M ≠ falseSentence :=
  haltsSentence_ne_falseSentence M

/-- Any presentation satisfying the verification bundle decides
halting through five states. -/
example (Z : ZFCPresentation) : ∀ n ≤ 5, DecidesHalting Z.theory n :=
  Z.decidesHalting_le_five

/-- The score maximum is attained. -/
example (n : ℕ) : ∃ M : Machine n, scoreOf M = busyBeaverOnes n :=
  exists_scoreOf_eq n

end BusyBeaverTests
