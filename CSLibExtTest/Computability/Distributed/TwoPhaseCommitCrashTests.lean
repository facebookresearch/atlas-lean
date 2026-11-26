/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.Computability.Distributed.TwoPhaseCommitCrash

/-!
# Tests for two-phase commit with crashes

With two participants:

* A run with only protocol steps and yes votes commits everybody and ends in a state where no
  protocol step can be taken, so both hypotheses of AC-4 in `atomic_commitment_and_blocking` are
  satisfiable.
* A timeout aborts although both participants voted yes, so AC-4 needs a run without failures.
* Both participants vote yes and the coordinator crashes after deciding commit, or after
  aborting on a timeout: the participants' states are the same in both runs, so they cannot
  tell the decision, and every participant is still operational; asking each other is not
  possible; once the coordinator recovers, a participant learns its decision.
* Cooperative termination decides when some participant knows the decision: a participant learns
  the commit, the coordinator crashes, and the other participant commits by asking it.
* A participant that crashes before voting aborts when it recovers.
-/

@[expose] public section

namespace Cslib.Distributed.TwoPhaseCommit.CrashTests

/-- A run with only protocol steps and yes votes ends with everybody committed. -/
example : ∃ s : CrashState (Fin 2), (crashLts (P := Fin 2)).MTr crashInitial
    [.protocol (.voteYes 0), .protocol (.voteYes 1), .protocol .decideCommit,
      .protocol (.learnCommit 0), .protocol (.learnCommit 1)] s ∧
    s.coord = .committed ∧ ∀ p, s.part p = .committed := by
  refine ⟨_, .stepL (CrashStep.voteYes crashInitial 0 rfl rfl) <|
    .stepL (CrashStep.voteYes _ 1 rfl rfl) <|
    .stepL (CrashStep.decideCommit _ rfl rfl (by decide)) <|
    .stepL (CrashStep.learnCommit _ 0 rfl rfl rfl rfl) <|
    .stepL (CrashStep.learnCommit _ 1 rfl rfl rfl rfl) .refl, rfl, by decide⟩

/-- The run that commits everybody ends in a state in which no protocol step can be taken. -/
example : ∃ (as : List (CrashAction (Fin 2))) (s : CrashState (Fin 2)),
    (crashLts (P := Fin 2)).MTr crashInitial as s ∧
    (∀ a ∈ as, ∃ b, a = .protocol b ∧ ∀ p, b ≠ .voteNo p) ∧
    ∀ b t, ¬ CrashStep s (.protocol b) t := by
  refine ⟨_, _, .stepL (CrashStep.voteYes crashInitial 0 rfl rfl) <|
    .stepL (CrashStep.voteYes _ 1 rfl rfl) <|
    .stepL (CrashStep.decideCommit _ rfl rfl (by decide)) <|
    .stepL (CrashStep.learnCommit _ 0 rfl rfl rfl rfl) <|
    .stepL (CrashStep.learnCommit _ 1 rfl rfl rfl rfl) .refl, by simp, fun b t h => ?_⟩
  cases h with
  | voteYes p _ h | voteNo p _ h | learnCommit p _ _ _ h => revert h; revert p; decide
  | decideCommit _ hc _ | decideAbort _ hc _ | learnAbort _ _ _ hc _ => cases hc

/-- A coordinator timeout aborts although both participants voted yes. -/
example : ∃ s : CrashState (Fin 2), CrashReachable s ∧ s.coord = .aborted ∧
    ∀ p, s.part p = .prepared :=
  ⟨_, ⟨_, .stepL (CrashStep.voteYes crashInitial 0 rfl rfl) <|
    .stepL (CrashStep.voteYes _ 1 rfl rfl) <| .stepL (CrashStep.timeoutCoord _ rfl rfl) .refl⟩,
    rfl, by decide⟩

/-- The blocking scenario: both participants voted yes and the coordinator crashed, having
decided commit in one run and abort in the other. The participants' states and which processes
are operational are the same in both runs. -/
example : ∃ s t : CrashState (Fin 2), CrashReachable s ∧ CrashReachable t ∧
    s.coordUp = false ∧ t.coordUp = false ∧ (∀ p, s.part p = .prepared) ∧ s.part = t.part ∧
    (∀ p, s.up p) ∧ s.up = t.up ∧ s.coord = .committed ∧ t.coord = .aborted :=
  ⟨_, _, ⟨_, .stepL (CrashStep.voteYes crashInitial 0 rfl rfl) <|
      .stepL (CrashStep.voteYes _ 1 rfl rfl) <|
      .stepL (CrashStep.decideCommit _ rfl rfl (by decide)) <|
      .stepL (CrashStep.crashCoord _ rfl) .refl⟩,
    ⟨_, .stepL (CrashStep.voteYes crashInitial 0 rfl rfl) <|
      .stepL (CrashStep.voteYes _ 1 rfl rfl) <| .stepL (CrashStep.timeoutCoord _ rfl rfl) <|
      .stepL (CrashStep.crashCoord _ rfl) .refl⟩,
    rfl, rfl, by decide, rfl, by decide, rfl, rfl, rfl⟩

/-- In the blocking scenario, an uncertain participant gets no answer from another uncertain
participant. -/
example (s t : CrashState (Fin 2)) (hs : ∀ p, s.part p = .prepared) :
    ¬ CrashStep s (.ask 0 1) t := by
  intro h
  cases h with
  | askCommit _ _ _ _ _ hd | askAbort _ _ _ _ _ hd | askWorking _ _ _ _ _ hd =>
      rw [hs] at hd
      cases hd

/-- Once the coordinator recovers, a participant learns its commit decision. -/
example : ∃ s : CrashState (Fin 2), CrashReachable s ∧ s.part 0 = .committed := by
  refine ⟨_, ⟨_, .stepL (CrashStep.voteYes crashInitial 0 rfl rfl) <|
    .stepL (CrashStep.voteYes _ 1 rfl rfl) <|
    .stepL (CrashStep.decideCommit _ rfl rfl (by decide)) <|
    .stepL (CrashStep.crashCoord _ rfl) <| .stepL (CrashStep.recoverCoord _ rfl) <|
    .stepL (CrashStep.learnCommit _ 0 rfl rfl rfl rfl) .refl⟩, rfl⟩

/-- A coordinator that crashes while waiting aborts when it recovers. -/
example : ∃ s : CrashState (Fin 2), CrashReachable s ∧ s.coordUp = true ∧
    s.coord = .aborted ∧ ∀ p, s.part p = .prepared :=
  ⟨_, ⟨_, .stepL (CrashStep.voteYes crashInitial 0 rfl rfl) <|
    .stepL (CrashStep.voteYes _ 1 rfl rfl) <| .stepL (CrashStep.crashCoord _ rfl) <|
    .stepL (CrashStep.recoverCoord _ rfl) .refl⟩, rfl, rfl, by decide⟩

/-- Cooperative termination: participant `0` learns the commit, the coordinator crashes, and
participant `1` commits by asking participant `0`. -/
example : ∃ s : CrashState (Fin 2), CrashReachable s ∧ s.coordUp = false ∧
    ∀ p, s.part p = .committed :=
  ⟨_, ⟨_, .stepL (CrashStep.voteYes crashInitial 0 rfl rfl) <|
    .stepL (CrashStep.voteYes _ 1 rfl rfl) <|
    .stepL (CrashStep.decideCommit _ rfl rfl (by decide)) <|
    .stepL (CrashStep.learnCommit _ 0 rfl rfl rfl rfl) <| .stepL (CrashStep.crashCoord _ rfl) <|
    .stepL (CrashStep.askCommit _ 1 0 rfl rfl rfl rfl) .refl⟩, rfl, by decide⟩

/-- A participant that crashes before voting aborts when it recovers. -/
example : ∃ s : CrashState (Fin 2), CrashReachable s ∧ s.up 0 = true ∧ s.part 0 = .aborted :=
  ⟨_, ⟨_, .stepL (CrashStep.crash crashInitial 0 rfl) <|
    .stepL (CrashStep.recover _ 0 rfl) .refl⟩, rfl, rfl⟩

end Cslib.Distributed.TwoPhaseCommit.CrashTests
