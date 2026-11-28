/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import CSLibExt.Computability.Distributed.RotatingCoordinator.Safety

/-!
# A three-round execution of rotating-coordinator consensus

False and true compete at timestamp zero. Round 1 obtains a mixed majority of replies.
The next coordinator selects true at stamp 1 instead of its own false at stamp 0. Round 2
issues a request, one recipient decides and crashes, and round 3 issues a distinct request.
A survivor R-delivers both requests but decides just once. These are explicit sends and
receives, checked against the same transition relation as the uniform safety theorem. The
69-event witness extends to an infinite trace satisfying the article's service assumptions.
Separate probes distinguish pre-invocation delivery from decision, a raw maximum from a legal
timestamp write, and scheduling a correct actor from executing its enabled instruction.
-/

namespace Cslib.Distributed.RotatingCoordinator.Tests

private abbrev E := Event 2 Bool

private def actions : Array E := #[
  .propose 0 false, .propose 1 true, .propose 2 false,
  .advance 0 1, .report 0 1 0 false, .advance 1 1, .report 1 1 0 true,
  .advance 2 1, .report 2 1 0 false, .receive (.report 0 1 0 false), .receive (.report 1 1 0 true),
  .choose 1 0 true, .send 0 1 true, .send 1 1 true, .send 2 1 true,
  .receive (.suggest 1 1 true), .ack 1 1 true, .nack 0 1, .nack 2 1,
  .receive (.reply 1 1 true), .receive (.reply 0 1 false), .finish 1 none,
  .advance 0 2, .report 0 2 0 false, .advance 1 2, .report 1 2 1 true,
  .advance 2 2, .report 2 2 0 false, .receive (.report 1 2 1 true), .receive (.report 2 2 0 false),
  .choose 2 1 true, .send 0 2 true, .send 1 2 true, .send 2 2 true,
  .receive (.suggest 1 2 true), .ack 1 2 true, .receive (.suggest 2 2 true), .ack 2 2 true,
  .nack 0 2, .receive (.reply 1 2 true), .receive (.reply 2 2 true), .finish 2 (some true),
  .deliver 1 2 true,
  .advance 0 3, .report 0 3 0 false, .advance 2 3, .report 2 3 2 true,
  .receive (.report 0 3 0 false), .receive (.report 2 3 2 true), .choose 3 2 true,
  .send 0 3 true, .send 1 3 true, .send 2 3 true,
  .receive (.suggest 0 3 true), .ack 0 3 true, .receive (.suggest 2 3 true), .ack 2 3 true,
  .receive (.reply 0 3 true), .receive (.reply 2 3 true), .finish 3 (some true),
  .deliver 0 2 true, .deliver 0 3 true, .deliver 2 3 true, .deliver 2 2 true,
  .receive (.suggest 0 1 true), .receive (.suggest 2 1 true), .receive (.report 0 2 0 false),
  .receive (.suggest 0 2 true), .receive (.reply 0 2 false)]

private def ev (t : ℕ) : E := actions[t]?.getD (.wait (if t % 2 = 0 then 0 else 2))

-- Process 1 acts at tick 42, decides, and is crashed from tick 43 onwards.
private def failures : FailureDetector.FailurePattern (Proc 2) where
  crashedBy t := {p | 43 ≤ t ∧ p = 1}
  mono _ _ h _ hp := ⟨hp.1.trans h, hp.2⟩
  exists_correct := ⟨0, fun _ h => by have : (0 : Proc 2) = 1 := h.2; contradiction⟩

private def suspects : FailureDetector.History (Proc 2) := fun _ t => {p | t < 43 ∨ p = 1}

private instance (stream : ℕ → E) (t : ℕ) (e : E) : Decidable (Guard stream suspects t e) := by
  cases e <;> unfold Guard <;>
    dsimp only [suspects, Set.mem_ofPred_eq, Paxos.QuorumSystem.majority] <;> infer_instance

private instance (stream : ℕ → E) (t : ℕ) (e : E) :
    Decidable (Enabled stream failures suspects t e) := by
  unfold Enabled
  change Decidable ((∀ p, e.actor = some p → ¬ (43 ≤ t ∧ p = 1)) ∧ _)
  infer_instance

set_option maxRecDepth 12000 in
private theorem prefix_ok : ProgramPrefix ev failures suspects actions.size := by
  unfold ProgramPrefix
  decide

-- One predicate per upcall, with finite tests on its strictly earlier history.
private def hasOrigin (t : ℕ) : Prop := match ev t with
  | .deliver _ r v => Seen ev t fun e => e = .finish r (some v)
  | _ => True

private instance (t : ℕ) : Decidable (hasOrigin t) := by
  unfold hasOrigin
  split <;> infer_instance

private theorem legal : LegalPrefix ev failures suspects actions.size := by
  have causal : ∀ i : Fin actions.size, hasOrigin i := by decide
  refine ⟨prefix_ok, fun i p r v hi => ?_⟩
  simpa [hasOrigin, hi] using causal i

example : (lts failures suspects).MTr [] (List.ofFn (fun t : Fin actions.size => ev t))
    (List.ofFn (fun t : Fin actions.size => ev t)) := legal.1.mTr

-- Either received zero-stamp value can be selected, not only the value in the witness.
example : Guard ev suspects 11 (.choose 1 0 false) ∧ Guard ev suspects 11 (.choose 1 0 true) :=
  by decide

example : ¬ (Paxos.QuorumSystem.majority (Proc 3)).IsQuorum {0, 1} := by
  change ¬ (4 < 2 * ({0, 1} : Finset (Proc 3)).card)
  decide

example : replies ev 21 1 false = {0, 1} ∧ replies ev 21 1 true = {1} := by decide

example : ¬ Guard ev suspects 21 (.finish 1 (some true)) := by decide

example : latest ev (Event.incoming 2 1) 30 = some (1, true) ∧
    latest ev (Event.incoming 2 2) 30 = some (0, false) ∧
    ¬ Guard ev suspects 30 (.choose 2 0 false) := by decide

example : ¬ Guard ev suspects 0 (.receive (.suggest 0 1 true)) := by decide

example : Decides ev 1 42 true ∧ (1 : Proc 2) ∈ failures.crashedBy 43 := by
  exact ⟨⟨⟨2, rfl⟩, by decide⟩, ⟨by decide, rfl⟩⟩

example : Decides ev 0 60 true ∧ ev 61 = .deliver 0 3 true ∧ ¬ Decides ev 0 61 true := by
  refine ⟨⟨⟨2, rfl⟩, by decide⟩, rfl, fun h => ?_⟩
  exact (show ¬ OpenGuard ev 0 61 by decide) h.2

example : UniformSafety ev actions.size := uniformSafety_of_prefix legal

-- A concrete history from an eventually strong detector (early false suspicions are allowed).
private def detector : FailureDetector.Detector (Proc 2) := fun F =>
  {h | ∀ p t q, q ∈ h p t ↔ t < 43 ∨ q ∈ F.crashed}

private theorem detector_class :
    detector ∈ FailureDetector.DetectorClass.eventuallyStrong.detectors := by
  constructor
  · intro F h hh
    exact ⟨43, fun p hp q _ t _ => (hh q t p).2 (.inr hp)⟩
  · intro F h hh
    obtain ⟨p, hp⟩ := F.exists_correct
    refine ⟨43, p, hp, fun t ht q _ he => ?_⟩
    rcases (hh q t p).1 he with early | ⟨i, hi⟩
    · omega
    · exact hp i hi

private theorem history_allowed : suspects ∈ detector failures := by
  intro p t q
  change (t < 43 ∨ q = 1) ↔ t < 43 ∨ ∃ i, 43 ≤ i ∧ q = 1
  grind

private theorem correct_iff (p : Proc 2) : p ∈ failures.correct ↔ p ≠ 1 := by
  change (∀ t, ¬ (43 ≤ t ∧ p = 1)) ↔ _
  exact ⟨fun h hp => h 43 ⟨le_rfl, hp⟩, fun h _ hp => h hp.2⟩

private theorem tail_wait {t : ℕ} (ht : actions.size ≤ t) :
    ev t = .wait (if t % 2 = 0 then 0 else 2) := by simp [ev, Array.getElem?_eq_none ht]

private theorem all_steps (T : ℕ) : ProgramPrefix ev failures suspects T := by
  intro t
  by_cases h : t.val < actions.size
  · exact prefix_ok ⟨t, h⟩
  rw [tail_wait (by omega)]
  unfold Enabled
  simp only [Event.actor, Option.some.injEq, Event.slot, Guard, ite_self, ne_eq, not_true_eq_false,
    false_implies, implies_true, and_true, forall_eq']
  split <;> simp [failures]

private abbrev RBE := ReliableBroadcast.Event (Proc 2) (ℕ × Bool)

private def rbKey : RBE → Bool × Proc 2 × ℕ × Bool
  | .broadcast p m => (true, p, m)
  | .deliver p m => (false, p, m)

private instance : DecidableEq RBE := fun a b =>
  decidable_of_iff (rbKey a = rbKey b) (by cases a <;> cases b <;> simp [rbKey])

-- Check all channel and RB obligations on the finite non-wait part. Quantifying over send
-- occurrences rather than an a priori value universe also checks that no request was invented.
private def channelAt (i : Fin actions.size) : Option (Wire 2 Bool) → Prop
  | none => True
  | some m => (Event.receive m).actor ≠ some 1 →
    ∃ j : Fin actions.size, i < j ∧ ev j = .receive m

private def rbAt (i : Fin actions.size) : Option RBE → Prop
  | none => True
  | some (.broadcast p m) => p ≠ 1 →
    ∃ j : Fin actions.size, i ≤ j ∧ (ev j).rb = some (.deliver p m)
  | some (.deliver p m) =>
    (p ≠ 1 → ∀ q : Proc 2, q ≠ 1 → ∃ j : Fin actions.size, (ev j).rb = some (.deliver q m)) ∧
    (∀ j : Fin actions.size, (ev j).rb = some (.deliver p m) → j = i) ∧
    ∃ j : Fin actions.size, j < i ∧ (ev j).rb = some (.broadcast (coord 2 m.1) m)

private abbrev serviceAt (i : Fin actions.size) := channelAt i (ev i).sent ∧ rbAt i (ev i).rb

private instance (i : Fin actions.size) (m : Option (Wire 2 Bool)) : Decidable (channelAt i m) := by
  cases m <;> unfold channelAt <;> infer_instance

private instance (i : Fin actions.size) (m : Option RBE) : Decidable (rbAt i m) := by
  cases m with
  | none => exact isTrue trivial
  | some x => cases x <;> unfold rbAt <;> infer_instance

private theorem services : ∀ i : Fin actions.size, serviceAt i := by decide

private theorem rb_finite {t : ℕ} {x : RBE} (hx : (ev t).rb = some x) : t < actions.size := by
  by_contra! ht
  rw [tail_wait ht] at hx
  cases hx

private theorem rb_good : ReliableBroadcast.IsReliableBroadcast (fun m : ℕ × Bool => coord 2 m.1)
    failures.correct (fun t => (ev t).rb) := by
  constructor
  · intro p hp m t he
    have h := (services ⟨t, rb_finite he⟩).2
    simp only [he, rbAt] at h
    obtain ⟨j, hj, hje⟩ := h ((correct_iff _).1 hp)
    exact ⟨j, hj, hje⟩
  · intro p hp m t he q hq
    have h := (services ⟨t, rb_finite he⟩).2
    simp only [he, rbAt] at h
    obtain ⟨j, hj⟩ := h.1 ((correct_iff _).1 hp) q ((correct_iff _).1 hq)
    exact ⟨j, hj⟩
  · intro p m t he
    have h := (services ⟨t, rb_finite he⟩).2
    simp only [he, rbAt] at h
    obtain ⟨j, hj, he'⟩ := h.2.2
    exact ⟨fun i hi => congrArg Fin.val (h.2.1 ⟨i, rb_finite hi⟩ hi), j, hj, he'⟩

private theorem survivors : ∀ p : Proc 2, p ≠ 1 → p = 0 ∨ p = 2 := by decide

-- The two survivors receive all outstanding messages and requests, then continue taking steps.
private theorem actual : ArticleRun ev failures detector suspects where
  execution := execution_of_programPrefixes all_steps
  detector := detector_class
  history := history_allowed
  majority := ⟨{0, 2}, by change 3 < 2 * ({0, 2} : Finset (Proc 2)).card; decide,
    fun p hp => (correct_iff _).2 (by rintro rfl; contradiction)⟩
  proposes p hp := by
    have hn := (correct_iff _).1 hp
    rcases survivors p hn with rfl | rfl
    · exact ⟨0, false, rfl⟩
    · exact ⟨2, false, rfl⟩
  scheduling p hp t := by
    have hn := (correct_iff _).1 hp
    rcases survivors p hn with rfl | rfl
    · refine ⟨2 * (t + actions.size), by omega, ?_⟩
      rw [tail_wait (by omega)]; simp [Event.actor]
    · refine ⟨2 * (t + actions.size) + 1, by omega, ?_⟩
      rw [tail_wait (by omega)]; simp [Event.actor, Nat.add_mod]
  channels t m he p ep hp := by
    have ht : t < actions.size := by
      by_contra! hn
      rw [tail_wait hn] at he; cases he
    have h := (services ⟨t, ht⟩).1
    simp only [he, channelAt] at h
    obtain ⟨j, hj, he'⟩ := h (by simpa [ep] using (correct_iff _).1 hp)
    exact ⟨j, hj, he'⟩
  broadcast := rb_good

example (T : ℕ) : UniformSafety ev T := actual.uniformSafety T

-- A raw handler probe, not an execution: a slot collision and another process's invocation
-- cannot arm process 2. Its early upcall is observed by RB and is not replayed at invocation.
private def handler : ℕ → E
  | 0 => .advance 2 0
  | 1 => .propose 0 true
  | 2 => .deliver 2 1 false
  | 3 => .propose 2 false
  | 4 => .deliver 2 3 true
  | 5 => .propose 2 true
  | 6 => .deliver 2 7 false
  | _ => .idle

example : (handler 0).slot 2 = 1 ∧ (handler 2).rb = some (.deliver 2 (1, false)) ∧
    ¬ Decides handler 2 2 false ∧ ¬ Decides handler 2 3 false ∧ Decides handler 2 4 true ∧
    ¬ Decides handler 2 6 false := by
  refine ⟨rfl, rfl, fun h => ?_, fun h => ?_, ⟨⟨3, rfl⟩, by decide⟩, fun h => ?_⟩
  · exact (show ¬ OpenGuard handler 2 2 by decide) h.2
  · obtain ⟨r, hr⟩ := h.1; cases hr
  · exact (show ¬ OpenGuard handler 2 6 by decide) h.2

-- On a raw stream a later, smaller ACK cannot reduce the prefix maximum.
example : stamp (fun i => if i = 0 then Event.ack (0 : Proc 2) 4 true else .ack 0 1 false)
    0 2 = 4 := by decide

-- Keep the original detector, crashes, and all three proposals, but replace *every* subsequent
-- instruction by a poll. This satisfies the scheduling and service clauses without progress.
private def parked (t : ℕ) : E := if t < 3 then ev t else .wait (if t % 2 = 0 then 0 else 2)

private theorem parkedSteps (T : ℕ) : ProgramPrefix parked failures suspects T := by
  intro t
  by_cases ht : t.val < 3
  · exact (show ∀ i : Fin 3, Enabled parked failures suspects i (parked i) by decide) ⟨t, ht⟩
  simp only [parked, ite_eq_right ht]
  unfold Enabled
  split <;> simp [Guard, Event.actor, Event.slot, failures]

private theorem silent (t : ℕ) : (parked t).sent = none ∧ (parked t).rb = none := by
  by_cases ht : t < 3
  · exact (show ∀ i : Fin 3, (parked i).sent = none ∧ (parked i).rb = none by decide) ⟨t, ht⟩
  simp [parked, ht, Event.sent, Event.rb]

private theorem pollsOnly : ArticleRun parked failures detector suspects where
  execution := execution_of_programPrefixes parkedSteps
  detector := actual.detector
  history := actual.history
  majority := actual.majority
  proposes p hp := by
    rcases survivors p ((correct_iff _).1 hp) with rfl | rfl
    · exact ⟨0, false, rfl⟩
    · exact ⟨2, false, rfl⟩
  scheduling p hp t := by
    obtain ⟨i, hi, he⟩ := actual.scheduling p hp (max t actions.size)
    have hi' := le_trans (le_max_right t actions.size) hi
    have h₃ : 3 ≤ actions.size := by decide
    have hnot : ¬ i < 3 := by omega
    refine ⟨i, (le_max_left _ _).trans hi, ?_⟩
    simpa [parked, hnot, tail_wait hi'] using he
  channels t _ he := by rw [(silent t).1] at he; cases he
  broadcast := by
    constructor <;> intros <;> simp_all [(silent _).2]

example : ArticleRun parked failures detector suspects ∧
    Enabled parked failures suspects 3 (.advance 0 1) ∧ ∀ p i v, ¬ Decides parked p i v := by
  refine ⟨pollsOnly, by decide, fun p i v h => ?_⟩
  obtain ⟨r, he⟩ := h.1
  have hr := (silent i).2
  rw [he] at hr; cases hr

end Cslib.Distributed.RotatingCoordinator.Tests
