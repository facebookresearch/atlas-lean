/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Two-phase commit with crashes
-/
module

public import CSLibExt.Computability.Distributed.TwoPhaseCommit

/-!
# Two-phase commit with crashes: atomic commitment and blocking

The two-phase commit protocol of `CSLibExt.Computability.Distributed.TwoPhaseCommit` with
failures, following L. Alvisi, *Atomic Commit*, lecture notes, CS 371D, University of Texas at
Austin, Fall 2008. The states are those of the failure-free model with an operational flag for
each process; each process keeps its state in its log on stable storage. `CrashStep` lets each
process crash and recover, following the recovery rules of the log, lets the coordinator and a
participant that has not voted abort on a timeout, and lets an uncertain participant ask another
participant for the decision (cooperative termination). Protocol steps are those of `Step`,
taken by operational processes, except that the coordinator aborts without a timeout only when
some participant has aborted. Messages are abstracted into guards on the global state, as in the
failure-free model; a participant learns the decision from the coordinator only while the
coordinator is operational, so a crash loses the decision messages the coordinator has not
delivered.

* `atomic_commitment_and_blocking`: two-phase commit with crashes satisfies AC-1 to AC-4, and
  once every participant is uncertain and the coordinator has crashed, no participant decides
  until the coordinator recovers.
-/

@[expose] public section

namespace Cslib.Distributed.TwoPhaseCommit

variable {P : Type*} [DecidableEq P]

/-- **States of two-phase commit with crashes.** For a set $P$ of participants, a state of
two-phase commit with crashes is a global state of the protocol together with whether the
coordinator is operational and, for each participant $p \in P$, whether $p$ is operational. Each
process keeps its own state in its log on stable storage, so a crash does not change it. -/
structure CrashState (P : Type*) extends State P where
  /-- Whether the coordinator is operational. -/
  coordUp : Bool
  /-- Whether each participant is operational. -/
  up : P → Bool

/-- **Actions of two-phase commit with crashes.** The actions of two-phase commit with crashes
over a set $P$ of participants are: a protocol action of two-phase commit; the coordinator times
out waiting for votes; a participant $p$ times out waiting for the vote request; a participant
$p$ asks a participant $q$ for the decision (cooperative termination); the coordinator crashes;
the coordinator recovers; a participant $p$ crashes; and a participant $p$ recovers. -/
inductive CrashAction (P : Type*)
  | protocol (a : Action P)
  | timeoutCoord
  | timeoutPart (p : P)
  | ask (p q : P)
  | crashCoord
  | recoverCoord
  | crash (p : P)
  | recover (p : P)

/-- **Transitions of two-phase commit with crashes.** The protocol with crashes steps from a
state $s$ to a state $t$ by an action exactly in the following cases; in each step every other
part of the state is unchanged.

* Protocol actions, taken only by operational processes. An operational working participant may
  vote yes, after which it is prepared, or vote no, after which it is aborted. An operational
  waiting coordinator may decide commit when every participant is prepared, and decide abort
  when some participant has aborted. An operational prepared participant
  learns commit from an operational committed coordinator, and an operational prepared or
  working participant learns abort from an operational aborted coordinator.
* Timeouts. An operational waiting coordinator may decide abort, and an operational working
  participant may decide abort.
* Cooperative termination. An operational prepared participant $p$ may ask an operational
  participant $q$: if $q$ has committed, $p$ commits; if $q$ has aborted, $p$ aborts; if $q$ is
  working, $q$ aborts.
* Crashes and recovery. An operational process may crash. A crashed coordinator recovers, and
  aborts if it was waiting. A crashed participant recovers, and aborts if it was working.

A participant learns a decision from the coordinator only while the coordinator is operational:
a crash loses the decision messages the coordinator has not delivered. -/
inductive CrashStep : CrashState P → CrashAction P → CrashState P → Prop
  | voteYes (s : CrashState P) (p : P) (hp : s.up p) (h : s.part p = .working) :
      CrashStep s (.protocol (.voteYes p)) ⟨s.setPart p .prepared, s.coordUp, s.up⟩
  | voteNo (s : CrashState P) (p : P) (hp : s.up p) (h : s.part p = .working) :
      CrashStep s (.protocol (.voteNo p)) ⟨s.setPart p .aborted, s.coordUp, s.up⟩
  | decideCommit (s : CrashState P) (hu : s.coordUp) (hc : s.coord = .waiting)
      (h : ∀ p, s.part p = .prepared) :
      CrashStep s (.protocol .decideCommit) ⟨⟨.committed, s.part⟩, s.coordUp, s.up⟩
  | decideAbort (s : CrashState P) (hu : s.coordUp) (hc : s.coord = .waiting)
      (h : ∃ p, s.part p = .aborted) :
      CrashStep s (.protocol .decideAbort) ⟨⟨.aborted, s.part⟩, s.coordUp, s.up⟩
  | learnCommit (s : CrashState P) (p : P) (hu : s.coordUp) (hp : s.up p)
      (hc : s.coord = .committed) (h : s.part p = .prepared) :
      CrashStep s (.protocol (.learnCommit p)) ⟨s.setPart p .committed, s.coordUp, s.up⟩
  | learnAbort (s : CrashState P) (p : P) (hu : s.coordUp) (hp : s.up p)
      (hc : s.coord = .aborted) (h : s.part p = .prepared ∨ s.part p = .working) :
      CrashStep s (.protocol (.learnAbort p)) ⟨s.setPart p .aborted, s.coordUp, s.up⟩
  | timeoutCoord (s : CrashState P) (hu : s.coordUp) (hc : s.coord = .waiting) :
      CrashStep s .timeoutCoord ⟨⟨.aborted, s.part⟩, s.coordUp, s.up⟩
  | timeoutPart (s : CrashState P) (p : P) (hp : s.up p) (h : s.part p = .working) :
      CrashStep s (.timeoutPart p) ⟨s.setPart p .aborted, s.coordUp, s.up⟩
  | askCommit (s : CrashState P) (p q : P) (hp : s.up p) (hq : s.up q)
      (h : s.part p = .prepared) (hd : s.part q = .committed) :
      CrashStep s (.ask p q) ⟨s.setPart p .committed, s.coordUp, s.up⟩
  | askAbort (s : CrashState P) (p q : P) (hp : s.up p) (hq : s.up q)
      (h : s.part p = .prepared) (hd : s.part q = .aborted) :
      CrashStep s (.ask p q) ⟨s.setPart p .aborted, s.coordUp, s.up⟩
  | askWorking (s : CrashState P) (p q : P) (hp : s.up p) (hq : s.up q)
      (h : s.part p = .prepared) (hd : s.part q = .working) :
      CrashStep s (.ask p q) ⟨s.setPart q .aborted, s.coordUp, s.up⟩
  | crashCoord (s : CrashState P) (hu : s.coordUp) :
      CrashStep s .crashCoord ⟨s.toState, false, s.up⟩
  | recoverCoord (s : CrashState P) (hu : s.coordUp = false) :
      CrashStep s .recoverCoord
        ⟨⟨if s.coord = .waiting then .aborted else s.coord, s.part⟩, true, s.up⟩
  | crash (s : CrashState P) (p : P) (hp : s.up p) :
      CrashStep s (.crash p) ⟨s.toState, s.coordUp, Function.update s.up p false⟩
  | recover (s : CrashState P) (p : P) (hp : s.up p = false) :
      CrashStep s (.recover p)
        ⟨s.setPart p (if s.part p = .working then .aborted else s.part p), s.coordUp,
          Function.update s.up p true⟩

/-- **Two-phase commit with crashes as a transition system.** For a set $P$ of participants, the
labelled transition system whose states are the states of two-phase commit with crashes, whose
labels are its actions, and whose transitions are its steps. -/
def crashLts : LTS (CrashState P) (CrashAction P) where
  Tr := CrashStep

/-- **Initial state of two-phase commit with crashes.** The coordinator is waiting, every
participant is working, and every process is operational. -/
def crashInitial : CrashState P := ⟨initial, true, fun _ => true⟩

/-- **Reachable states of two-phase commit with crashes.** A state $s$ of two-phase commit with
crashes is reachable when some finite sequence of actions leads from the initial state, in which
the coordinator is waiting, every participant is working and every process is operational, to
$s$. -/
def CrashReachable (s : CrashState P) : Prop := (crashLts (P := P)).CanReach crashInitial s

private theorem setPart_part_ne (s : State P) {p q : P} (x : PartState) (h : q ≠ p) :
    (s.setPart p x).part q = s.part q := Function.update_of_ne h _ _

private theorem inv_setPart {s : State P} (hs : Inv s) (p : P) (x : PartState)
    (hc : s.coord = .committed → x = .prepared ∨ x = .committed)
    (hx : x = .committed → s.coord = .committed) : Inv (s.setPart p x) := by
  refine ⟨fun h q => ?_, fun q hq => ?_⟩
  · by_cases hqp : q = p
    · subst hqp
      simpa [State.setPart] using hc h
    · rw [setPart_part_ne _ _ hqp]
      exact hs.coord_committed h q
  · by_cases hqp : q = p
    · subst hqp
      exact hx (by simpa [State.setPart] using hq)
    · rw [setPart_part_ne _ _ hqp] at hq
      exact hs.part_committed q hq

private theorem inv_crashStep {s t : CrashState P} {a : CrashAction P} (hs : Inv s.toState)
    (h : CrashStep s a t) : Inv t.toState := by
  cases h with
  | voteYes p _ hp =>
      refine inv_setPart hs p _ (fun hc => ?_) (by simp)
      rcases hs.coord_committed hc p with h | h <;> simp_all
  | voteNo p _ hp =>
      refine inv_setPart hs p _ (fun hc => ?_) (by simp)
      rcases hs.coord_committed hc p with h | h <;> simp_all
  | decideCommit _ _ hall => exact ⟨fun _ q => Or.inl (hall q), fun _ _ => rfl⟩
  | decideAbort _ hc _ =>
      refine ⟨fun h => by simp at h, fun q hq => ?_⟩
      have := hs.part_committed q hq
      simp_all
  | learnCommit p _ _ hc _ => exact inv_setPart hs p _ (by simp) (fun _ => hc)
  | learnAbort p _ _ hc _ => exact inv_setPart hs p _ (by simp_all) (by simp)
  | timeoutCoord _ hc =>
      refine ⟨fun h => by simp at h, fun q hq => ?_⟩
      have := hs.part_committed q hq
      simp_all
  | timeoutPart p _ hp =>
      refine inv_setPart hs p _ (fun hc => ?_) (by simp)
      rcases hs.coord_committed hc p with h | h <;> simp_all
  | askCommit p q _ _ _ hd => exact inv_setPart hs p _ (by simp) (fun _ => hs.part_committed q hd)
  | askAbort p q _ _ _ hd =>
      refine inv_setPart hs p _ (fun hc => ?_) (by simp)
      rcases hs.coord_committed hc q with h | h <;> simp_all
  | askWorking p q _ _ _ hd =>
      refine inv_setPart hs q _ (fun hc => ?_) (by simp)
      rcases hs.coord_committed hc q with h | h <;> simp_all
  | crashCoord => exact hs
  | recoverCoord =>
      refine ⟨fun h q => ?_, fun q hq => ?_⟩
      · have hc : s.coord = .committed := by split_ifs at h; exact h
        exact hs.coord_committed hc q
      · simp [hs.part_committed q hq]
  | crash => exact hs
  | recover p _ =>
      refine inv_setPart hs p _ (fun hc => ?_) (fun hx => ?_)
      · rcases hs.coord_committed hc p with h | h <;> simp_all
      · exact hs.part_committed p (by split_ifs at hx; exact hx)

private theorem inv_crashReachable {s : CrashState P} (h : CrashReachable s) : Inv s.toState :=
  let ⟨_, hm⟩ := h
  LTS.mtrInv_of_trInv (p := fun s : CrashState P => Inv s.toState)
    (fun _ _ _ htr hs => inv_crashStep hs htr) _ _ _ hm inv_initial

private theorem setPart_keeps (u : State P) (p q : P) (x : PartState)
    (hx : u.part p = .committed ∨ u.part p = .aborted → x = u.part p) :
    (u.part q = .committed → (u.setPart p x).part q = .committed) ∧
      (u.part q = .aborted → (u.setPart p x).part q = .aborted) := by
  by_cases hqp : q = p
  · subst hqp
    refine ⟨fun h => ?_, fun h => ?_⟩ <;> simp [State.setPart, hx (by simp [h]), h]
  · simp [setPart_part_ne _ _ hqp]

private theorem crashStep_keeps {s t : CrashState P} {a : CrashAction P} (h : CrashStep s a t) :
    (s.coord = .committed → t.coord = .committed) ∧ (s.coord = .aborted → t.coord = .aborted) ∧
      ∀ p, (s.part p = .committed → t.part p = .committed) ∧
        (s.part p = .aborted → t.part p = .aborted) := by
  cases h with
  | decideCommit _ hc _ => simp_all
  | decideAbort _ hc _ => simp_all
  | timeoutCoord _ hc => simp_all
  | recoverCoord => refine ⟨?_, ?_, fun p => ⟨id, id⟩⟩ <;> intro h <;> simp [h]
  | crashCoord => exact ⟨id, id, fun _ => ⟨id, id⟩⟩
  | crash => exact ⟨id, id, fun _ => ⟨id, id⟩⟩
  | recover p _ =>
      exact ⟨id, id, fun q => setPart_keeps _ _ q _ (by rintro (h | h) <;> simp [h])⟩
  | voteYes p _ h | voteNo p _ h | timeoutPart p _ h | askWorking _ p _ _ _ h =>
      exact ⟨id, id, fun q => setPart_keeps _ _ q _ (by rintro (h' | h') <;> simp_all)⟩
  | learnCommit p _ _ _ h | learnAbort p _ _ _ h | askCommit p _ _ _ h | askAbort p _ _ _ h =>
      exact ⟨id, id, fun q => setPart_keeps _ _ q _ (by rintro (h' | h') <;> simp_all)⟩

/-- A protocol step other than a no vote aborts nothing that was not aborted and keeps every
process operational. -/
private theorem crashStep_no_abort {s t : CrashState P} {b : Action P}
    (h : CrashStep s (.protocol b) t) (hb : ∀ p, b ≠ .voteNo p)
    (hs : s.coord ≠ .aborted ∧ (∀ p, s.part p ≠ .aborted) ∧ s.coordUp ∧ ∀ p, s.up p) :
    t.coord ≠ .aborted ∧ (∀ p, t.part p ≠ .aborted) ∧ t.coordUp ∧ ∀ p, t.up p := by
  obtain ⟨hc, hp, hu⟩ := hs
  have upd : ∀ (q : P) (x : PartState), x ≠ .aborted → ∀ p, (s.setPart q x).part p ≠ .aborted := by
    intro q x hx p
    by_cases hpq : p = q
    · subst hpq
      simpa [State.setPart] using hx
    · rw [setPart_part_ne _ _ hpq]
      exact hp p
  cases h with
  | voteYes q => exact ⟨hc, upd q _ (by simp), hu⟩
  | voteNo q => exact absurd rfl (hb q)
  | decideCommit => exact ⟨by simp, hp, hu⟩
  | decideAbort _ _ h =>
      obtain ⟨q, hq⟩ := h
      exact absurd hq (hp q)
  | learnCommit q => exact ⟨hc, upd q _ (by simp), hu⟩
  | learnAbort _ _ _ hc' => exact absurd hc' hc

/-- A state reached by a failure-free run without no votes has no abort, and every process in it
is operational. -/
private theorem no_abort_of_failureFree {as : List (CrashAction P)} {s : CrashState P}
    (hm : (crashLts (P := P)).MTr crashInitial as s)
    (hn : ∀ a ∈ as, ∃ b, a = .protocol b ∧ ∀ p, b ≠ .voteNo p) :
    s.coord ≠ .aborted ∧ (∀ p, s.part p ≠ .aborted) ∧ s.coordUp ∧ ∀ p, s.up p := by
  suffices ∀ {s t : CrashState P} {as}, (crashLts (P := P)).MTr s as t →
      (∀ a ∈ as, ∃ b, a = .protocol b ∧ ∀ p, b ≠ .voteNo p) →
      (s.coord ≠ .aborted ∧ (∀ p, s.part p ≠ .aborted) ∧ s.coordUp ∧ ∀ p, s.up p) →
      t.coord ≠ .aborted ∧ (∀ p, t.part p ≠ .aborted) ∧ t.coordUp ∧ ∀ p, t.up p from
    this hm hn (by simp [crashInitial, initial])
  intro s t as hm hn hs
  induction hm with
  | refl => exact hs
  | @stepL s₁ a s₂ _ _ htr _ ih =>
      obtain ⟨b, rfl, hb⟩ := hn a List.mem_cons_self
      exact ih (fun b hb => hn b (List.mem_cons_of_mem _ hb)) (crashStep_no_abort htr hb hs)

/-- **Two-phase commit satisfies AC-1 to AC-4 and blocks.** For every set $P$ of participants,
two-phase commit with crashes, recovery, timeouts and cooperative termination has the following
properties. A run is failure-free when it consists of protocol actions only, with no crash,
recovery, timeout or cooperative termination; a prepared or committed participant has voted
yes.

1. (AC-1) In every reachable state, no participant has committed while another has aborted, the
   coordinator has not committed while a participant has aborted, and the coordinator has not
   aborted while a participant has committed.
2. (AC-2) Along every finite run, from any state, every process that has committed stays
   committed and every process that has aborted stays aborted.
3. (AC-3) In every reachable state in which the coordinator or some participant has committed,
   every participant is prepared or committed.
4. (AC-4) In every state reached from the initial state by a failure-free run in which no
   participant votes no, no process has aborted; and if no protocol action other than a no vote
   can be taken there, the coordinator and every participant have committed.
5. (Blocking) From every state in which every participant is prepared, that is, voted yes and
   is uncertain of the decision, and the coordinator has crashed, every finite run in which the
   coordinator does not recover keeps every participant prepared, although operational
   participants may still ask each other for the decision.

(L. Alvisi, *Atomic Commit*, lecture notes, CS 371D, University of Texas at Austin, Fall 2008:
"AC Specification", "Notes on 2PC" and "2PC and blocking".) -/
theorem atomic_commitment_and_blocking :
    (∀ s : CrashState P, CrashReachable s →
      (∀ p q, s.part p = .committed → s.part q ≠ .aborted) ∧
      (s.coord = .committed → ∀ q, s.part q ≠ .aborted) ∧
      (s.coord = .aborted → ∀ q, s.part q ≠ .committed)) ∧
    (∀ (s t : CrashState P) (as : List (CrashAction P)), (crashLts (P := P)).MTr s as t →
      (s.coord = .committed → t.coord = .committed) ∧ (s.coord = .aborted → t.coord = .aborted) ∧
      ∀ p, (s.part p = .committed → t.part p = .committed) ∧
        (s.part p = .aborted → t.part p = .aborted)) ∧
    (∀ s : CrashState P, CrashReachable s → (s.coord = .committed ∨ ∃ p, s.part p = .committed) →
      ∀ q, s.part q = .prepared ∨ s.part q = .committed) ∧
    (∀ (as : List (CrashAction P)) (s : CrashState P), (crashLts (P := P)).MTr crashInitial as s →
      (∀ a ∈ as, ∃ b, a = .protocol b ∧ ∀ p, b ≠ .voteNo p) →
      (s.coord ≠ .aborted ∧ ∀ p, s.part p ≠ .aborted) ∧
      ((∀ b t, (∀ p, b ≠ .voteNo p) → ¬ CrashStep s (.protocol b) t) →
        s.coord = .committed ∧ ∀ p, s.part p = .committed)) ∧
    (∀ (s t : CrashState P) (as : List (CrashAction P)), s.coordUp = false →
      (∀ p, s.part p = .prepared) → (crashLts (P := P)).MTr s as t → .recoverCoord ∉ as →
      ∀ p, t.part p = .prepared) := by
  refine ⟨fun s hs => ?_, fun s t as hm => ?_, fun s hs hc q => ?_, fun as s hm hn => ?_,
    fun s t as hu hp hm hr => ?_⟩
  · have hi := inv_crashReachable hs
    refine ⟨fun p q hp => ?_, fun hc q => ?_, fun hc q hq => ?_⟩
    · rcases hi.coord_committed (hi.part_committed p hp) q with h | h <;> simp [h]
    · rcases hi.coord_committed hc q with h | h <;> simp [h]
    · have := hi.part_committed q hq
      simp_all
  · induction hm with
    | refl => exact ⟨id, id, fun _ => ⟨id, id⟩⟩
    | stepL htr _ ih =>
        obtain ⟨h1, h2, h3⟩ := crashStep_keeps htr
        exact ⟨ih.1 ∘ h1, ih.2.1 ∘ h2, fun p => ⟨(ih.2.2 p).1 ∘ (h3 p).1,
          (ih.2.2 p).2 ∘ (h3 p).2⟩⟩
  · have hi := inv_crashReachable hs
    refine hi.coord_committed ?_ q
    rcases hc with hc | ⟨p, hp⟩
    · exact hc
    · exact hi.part_committed p hp
  · obtain ⟨hc, hp, hcu, hpu⟩ := no_abort_of_failureFree hm hn
    refine ⟨⟨hc, hp⟩, fun hterm => ?_⟩
    have hi := inv_crashReachable ⟨as, hm⟩
    have hvoted : ∀ p, s.part p = .prepared ∨ s.part p = .committed := by
      intro p
      cases hq : s.part p with
      | working => exact absurd (CrashStep.voteYes s p (hpu p) hq) (hterm _ _ (by simp))
      | prepared => exact Or.inl rfl
      | committed => exact Or.inr rfl
      | aborted => exact absurd hq (hp p)
    have hcc : s.coord = .committed := by
      cases hq : s.coord with
      | committed => rfl
      | aborted => exact absurd hq hc
      | waiting =>
          refine absurd (CrashStep.decideCommit s hcu hq fun p => ?_) (hterm _ _ (by simp))
          rcases hvoted p with h | h
          · exact h
          · have := hi.part_committed p h
            simp_all
    refine ⟨hcc, fun p => ?_⟩
    rcases hvoted p with h | h
    · exact absurd (CrashStep.learnCommit s p hcu (hpu p) hcc h) (hterm _ _ (by simp))
    · exact h
  · suffices ∀ {s t : CrashState P} {as}, (crashLts (P := P)).MTr s as t →
        .recoverCoord ∉ as → s.coordUp = false → (∀ p, s.part p = .prepared) →
        ∀ p, t.part p = .prepared from this hm hr hu hp
    intro s t as hm hr hu hp
    induction hm with
    | refl => exact hp
    | @stepL s₁ a s₂ _ _ htr _ ih =>
        have hr' : a ≠ .recoverCoord := fun h => hr (h ▸ List.mem_cons_self)
        refine ih (fun h => hr (List.mem_cons_of_mem _ h)) ?_ ?_
        · cases htr <;> simp_all
        · cases htr with
          | crashCoord => exact hp
          | crash => exact hp
          | recoverCoord => exact absurd rfl hr'
          | recover q =>
              intro p
              by_cases hpq : p = q
              · subst hpq; simp [State.setPart, hp p]
              · rw [setPart_part_ne _ _ hpq]; exact hp p
          | _ => simp_all

end Cslib.Distributed.TwoPhaseCommit
