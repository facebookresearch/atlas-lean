/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.Computability.Distributed.TwoPhaseCommit

/-!
# Tests for two-phase commit

With two participants:

* Both vote yes, the coordinator commits, and both learn it: a reachable state
  in which everybody committed, so the invariant does not hold vacuously.
* One votes no, the coordinator aborts, and the other learns it: everybody
  aborted.
* The coordinator cannot commit while a participant has not voted.
-/

@[expose] public section

namespace Cslib.Distributed.TwoPhaseCommit.Tests

/-- Everybody commits. -/
example : ∃ s : State (Fin 2), Reachable s ∧ ∀ p, s.part p = .committed := by
  have h1 := Reachable.step reachable_initial (Step.voteYes (initial : State (Fin 2)) 0 rfl)
  have h2 := Reachable.step h1 (Step.voteYes _ 1 rfl)
  have h3 := Reachable.step h2 (Step.decideCommit _ rfl (by decide))
  have h4 := Reachable.step h3 (Step.learnCommit _ 0 rfl rfl)
  have h5 := Reachable.step h4 (Step.learnCommit _ 1 rfl rfl)
  refine ⟨_, h5, ?_⟩
  decide

/-- Everybody aborts. -/
example : ∃ s : State (Fin 2), Reachable s ∧ ∀ p, s.part p = .aborted := by
  have h1 := Reachable.step reachable_initial (Step.voteNo (initial : State (Fin 2)) 0 rfl)
  have h2 := Reachable.step h1 (Step.decideAbort _ rfl)
  have h3 := Reachable.step h2 (Step.learnAbort _ 1 rfl (Or.inr rfl))
  refine ⟨_, h3, ?_⟩
  decide

/-- The coordinator cannot commit while participant `1` has not voted. -/
example (t : State (Fin 2)) :
    ¬ Step ((initial : State (Fin 2)).setPart 0 .prepared) .decideCommit t := by
  intro h
  cases h with
  | decideCommit _ hall => exact absurd (hall 1) (by decide)

end Cslib.Distributed.TwoPhaseCommit.Tests
