/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Two-phase commit
-/
module

public import Cslib.Foundations.Semantics.LTS.Basic
public import Mathlib.Logic.Function.Basic

/-!
# Two-phase commit is atomic

The two-phase commit protocol (J. Gray, *Notes on data base operating systems*,
1978; P. A. Bernstein, V. Hadzilacos and N. Goodman, *Concurrency Control and
Recovery in Database Systems*, 1987, Chapter 7) as a labelled transition
system over an arbitrary set of participants. This is a failure-free safety
model: no process crashes and no message is lost; the coordinator may still
abort at any time before it commits (for instance on a timeout).

* A participant that is still working may vote yes (it becomes `prepared` and
  may no longer abort on its own) or vote no (it aborts).
* The coordinator commits when every participant is prepared; it may abort at
  any time before committing (a no vote, or a timeout).
* Prepared participants learn the decision: they commit after the coordinator
  commits and abort after it aborts; working participants abort after the
  coordinator aborts.

Messages are abstracted into guards on the global state: a participant reacts
to the coordinator's decision, and the coordinator's commit reads all votes.

The coordinator takes part in the decision but does not vote separately: its
vote is yes exactly when it decides commit, so "every process voted yes" means
every participant voted yes and the coordinator committed.

* `inv_reachable`: an inductive invariant holds in every reachable state.
* `atomicity`, `coord_committed_part_not_aborted`, `coord_aborted_part_not_committed`,
  `part_committed_coord_committed`: all processes that have decided, the
  coordinator included, decided the same way (Bernstein et al.'s AC1).
* `coord_committed_imp_all_voted_yes`, `committed_imp_all_voted_yes`: if the
  coordinator or a participant commits, every participant voted yes, and the
  coordinator decided commit (AC3);
  `aborted_imp_not_committed`: once a participant has aborted, the coordinator
  has not committed.
-/

@[expose] public section

namespace Cslib.Distributed.TwoPhaseCommit

/-- Coordinator states. -/
inductive CoordState
  /-- Collecting votes. -/
  | waiting
  /-- Decided commit. -/
  | committed
  /-- Decided abort. -/
  | aborted
  deriving DecidableEq

/-- Participant states. -/
inductive PartState
  /-- Has not voted. -/
  | working
  /-- Voted yes; waits for the decision. -/
  | prepared
  /-- Committed. -/
  | committed
  /-- Aborted (voted no, or learned an abort). -/
  | aborted
  deriving DecidableEq

/-- Global states. -/
structure State (P : Type*) where
  /-- The coordinator's state. -/
  coord : CoordState
  /-- Each participant's state. -/
  part : P → PartState

variable {P : Type*} [DecidableEq P]

/-- Protocol actions. -/
inductive Action (P : Type*)
  | voteYes (p : P)
  | voteNo (p : P)
  | decideCommit
  | decideAbort
  | learnCommit (p : P)
  | learnAbort (p : P)

/-- Set the state of one participant. -/
def State.setPart (s : State P) (p : P) (x : PartState) : State P :=
  ⟨s.coord, Function.update s.part p x⟩

/-- The transitions of the protocol. -/
inductive Step : State P → Action P → State P → Prop
  | voteYes (s : State P) (p : P) (h : s.part p = .working) :
      Step s (.voteYes p) (s.setPart p .prepared)
  | voteNo (s : State P) (p : P) (h : s.part p = .working) :
      Step s (.voteNo p) (s.setPart p .aborted)
  | decideCommit (s : State P) (hc : s.coord = .waiting) (h : ∀ p, s.part p = .prepared) :
      Step s .decideCommit ⟨.committed, s.part⟩
  | decideAbort (s : State P) (hc : s.coord = .waiting) :
      Step s .decideAbort ⟨.aborted, s.part⟩
  | learnCommit (s : State P) (p : P) (hc : s.coord = .committed)
      (h : s.part p = .prepared) :
      Step s (.learnCommit p) (s.setPart p .committed)
  | learnAbort (s : State P) (p : P) (hc : s.coord = .aborted)
      (h : s.part p = .prepared ∨ s.part p = .working) :
      Step s (.learnAbort p) (s.setPart p .aborted)

/-- Two-phase commit as a labelled transition system. -/
def lts : LTS (State P) (Action P) where
  Tr := Step

/-- The initial state: the coordinator waits, every participant works. -/
def initial : State P := ⟨.waiting, fun _ => .working⟩

/-- The states reachable from the initial state, by upstream `LTS.CanReach`
(a multistep transition `LTS.MTr` along some list of actions). -/
def Reachable (s : State P) : Prop := (lts (P := P)).CanReach initial s

theorem reachable_initial : Reachable (initial : State P) := ⟨[], .refl⟩

/-- A step from a reachable state reaches a reachable state. -/
theorem Reachable.step {s t : State P} {a : Action P} (hs : Reachable s) (h : Step s a t) :
    Reachable t :=
  let ⟨as, hm⟩ := hs
  ⟨as ++ [a], LTS.MTr.stepR _ hm h⟩

/-- The inductive invariant: a committed coordinator has only prepared or
committed participants, and a committed participant has a committed
coordinator. -/
structure Inv (s : State P) : Prop where
  coord_committed : s.coord = .committed →
    ∀ p, s.part p = .prepared ∨ s.part p = .committed
  part_committed : ∀ p, s.part p = .committed → s.coord = .committed

omit [DecidableEq P] in
theorem inv_initial : Inv (initial : State P) :=
  ⟨fun h => by simp [initial] at h, fun p h => by simp [initial] at h⟩

theorem inv_step {s t : State P} {a : Action P} (hs : Inv s) (h : Step s a t) : Inv t := by
  cases h with
  | voteYes p hp =>
      refine ⟨fun hc q => ?_, fun q hq => ?_⟩
      · have := hs.coord_committed hc p
        rw [hp] at this
        simp at this
      · by_cases hqp : q = p
        · subst hqp
          simp [State.setPart] at hq
        · simp only [State.setPart, Function.update_of_ne hqp] at hq
          exact hs.part_committed q hq
  | voteNo p hp =>
      refine ⟨fun hc q => ?_, fun q hq => ?_⟩
      · have := hs.coord_committed hc p
        rw [hp] at this
        simp at this
      · by_cases hqp : q = p
        · subst hqp
          simp [State.setPart] at hq
        · simp only [State.setPart, Function.update_of_ne hqp] at hq
          exact hs.part_committed q hq
  | decideCommit hc hall =>
      exact ⟨fun _ q => Or.inl (hall q), fun _ _ => rfl⟩
  | decideAbort hc =>
      refine ⟨fun h => by simp at h, fun q hq => ?_⟩
      have := hs.part_committed q hq
      rw [hc] at this
      simp at this
  | learnCommit p hc hp =>
      refine ⟨fun _ q => ?_, fun _ _ => hc⟩
      by_cases hqp : q = p
      · subst hqp
        simp [State.setPart]
      · simp only [State.setPart, Function.update_of_ne hqp]
        exact hs.coord_committed hc q
  | learnAbort p hc hp =>
      refine ⟨fun h => by simp [State.setPart, hc] at h, fun q hq => ?_⟩
      by_cases hqp : q = p
      · subst hqp
        simp [State.setPart] at hq
      · simp only [State.setPart, Function.update_of_ne hqp] at hq
        have := hs.part_committed q hq
        rw [hc] at this
        simp at this

/-- Multistep transitions preserve the invariant. -/
theorem inv_mtr {s t : State P} {as : List (Action P)} (hm : (lts (P := P)).MTr s as t)
    (hs : Inv s) : Inv t := by
  induction hm with
  | refl => exact hs
  | stepL htr _ ih => exact ih (inv_step hs htr)

/-- The invariant holds in every reachable state. -/
theorem inv_reachable {s : State P} (h : Reachable s) : Inv s :=
  let ⟨_, hm⟩ := h
  inv_mtr hm inv_initial

/-- **Atomicity** (AC1), between participants: no reachable state has one
participant committed and another aborted. -/
theorem atomicity {s : State P} (h : Reachable s) {p q : P}
    (hp : s.part p = .committed) : s.part q ≠ .aborted := by
  have hinv := inv_reachable h
  rcases hinv.coord_committed (hinv.part_committed p hp) q with hq | hq <;> rw [hq] <;> simp

/-- **Validity** (AC3) for the coordinator: if it commits, every participant
voted yes (it is prepared or committed). -/
theorem coord_committed_imp_all_voted_yes {s : State P} (h : Reachable s)
    (hc : s.coord = .committed) (q : P) :
    s.part q = .prepared ∨ s.part q = .committed :=
  (inv_reachable h).coord_committed hc q

/-- **Validity** (AC3): if a participant commits, every participant voted
yes (it is prepared or committed); the coordinator decided commit by
`part_committed_coord_committed`. -/
theorem committed_imp_all_voted_yes {s : State P} (h : Reachable s) {p : P}
    (hp : s.part p = .committed) (q : P) :
    s.part q = .prepared ∨ s.part q = .committed :=
  (inv_reachable h).coord_committed ((inv_reachable h).part_committed p hp) q

/-- Once a participant has aborted, the coordinator has not committed. -/
theorem aborted_imp_not_committed {s : State P} (h : Reachable s) {p : P}
    (hp : s.part p = .aborted) : s.coord ≠ .committed := fun hc => by
  rcases (inv_reachable h).coord_committed hc p with hq | hq <;> rw [hp] at hq <;> simp at hq

/-- AC1 between a participant and the coordinator: a committed participant
has a committed coordinator. -/
theorem part_committed_coord_committed {s : State P} (h : Reachable s) {p : P}
    (hp : s.part p = .committed) : s.coord = .committed :=
  (inv_reachable h).part_committed p hp

/-- AC1 between the coordinator and a participant: a committed coordinator has
no aborted participant. -/
theorem coord_committed_part_not_aborted {s : State P} (h : Reachable s)
    (hc : s.coord = .committed) (q : P) : s.part q ≠ .aborted := by
  rcases (inv_reachable h).coord_committed hc q with hq | hq <;> rw [hq] <;> simp

/-- AC1 between the coordinator and a participant: an aborted coordinator has
no committed participant. -/
theorem coord_aborted_part_not_committed {s : State P} (h : Reachable s)
    (hc : s.coord = .aborted) (q : P) : s.part q ≠ .committed := fun hq => by
  have := (inv_reachable h).part_committed q hq
  rw [hc] at this
  simp at this

end Cslib.Distributed.TwoPhaseCommit
