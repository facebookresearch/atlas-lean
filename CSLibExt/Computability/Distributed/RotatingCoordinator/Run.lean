/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.Computability.Distributed.RotatingCoordinator.Protocol

/-!
# A safety abstraction of rotating-coordinator runs

The state of the labelled transition system is its chronological event log, initially empty.
A step appends one enabled instruction or message action. The ordinary channels require both a
prior send and an unconsumed copy, including for self-messages. The reliable-broadcast layer is
an external service: `ArticleRun` requires its specification on the actual projection of Phase 4
requests and upcalls, including upcalls ignored at the receiver. The prefix projection uses
uniform no-creation, not agreement of broadcast payloads.

`ArticleRun` retains the canonical eventually strong detector (◇S) and the source's correct
majority, proposals and reliable deliveries. It relaxes local instruction progress: arbitrarily
late actions by each correct actor suffice for scheduling. A `wait p` counts even at an enabled
instruction; `idle` has no actor. Thus a process may poll forever without starting an enabled
round. This admits extra schedules, which strengthens a safety proof but does not model the
local progress needed for termination. There is no fairness requirement on finite prefixes.

Source: T. D. Chandra and S. Toueg, *Unreliable failure detectors for reliable distributed
systems*, JACM 43(2), 1996, §§2.1–2.5, 4, 6.2.
-/

@[expose] public section

namespace Cslib.Distributed.RotatingCoordinator

variable {n : ℕ} {V : Type*} {ev fs : ℕ → Event n V} {t : ℕ}

private theorem latest_congr {A : Type*} (f : Event n V → Option A)
    (h : ∀ i < t, ev i = fs i) : latest ev f t = latest fs f t := by
  induction t with
  | zero => rfl
  | succ k ih => simp only [latest, h k (by omega), ih (fun i hi => h i (by omega))]

private theorem stamp_congr (p : Proc n) (h : ∀ i < t, ev i = fs i) :
    stamp ev p t = stamp fs p t := by
  induction t with
  | zero => rfl
  | succ k ih => simp only [stamp, h k (by omega), ih (fun i hi => h i (by omega))]

private theorem seen_congr (f : Event n V → Prop) (h : ∀ i < t, ev i = fs i) :
    Seen ev t f ↔ Seen fs t f := by simp only [Seen, h _ (Fin.isLt _)]

variable [DecidableEq V] {F : FailureDetector.FailurePattern (Proc n)}
    {H : FailureDetector.History (Proc n)}

private theorem enabled_congr (e : Event n V) (h : ∀ i < t, ev i = fs i) :
    Enabled ev F H t e ↔ Enabled fs F H t e := by
  have hq (r : ℕ) : reporters ev t r = reporters fs t r := by
    simp only [reporters, latest_congr _ h]
  have ha (r : ℕ) (b : Bool) : replies ev t r b = replies fs t r b := by
    simp only [replies, seen_congr _ h]
  have hopen (p : Proc n) : OpenGuard ev p t ↔ OpenGuard fs p t := by
    have hbefore (i : Fin t) := seen_congr (fun e => e.invoker = some p)
      (fun j (hj : j < i.val) => h j (hj.trans i.isLt))
    simp only [OpenGuard, seen_congr _ h, h _ (Fin.isLt _), hbefore]
  cases e <;> simp only [Enabled, Guard, hopen, Done, ReadyToReply, hq, ha, latest_congr _ h,
    stamp_congr _ h, seen_congr _ h, h _ (Fin.isLt _)]

/-- The history transition system for Figure 6 safety. A step appends one enabled event;
entries beyond the existing log are not inspected. A live process can always append a poll,
so an execution need not advance an enabled instruction. -/
def lts (F : FailureDetector.FailurePattern (Proc n)) (H : FailureDetector.History (Proc n)) :
    LTS (List (Event n V)) (Event n V) where
  Tr log e log' :=
    Enabled (fun i => log[i]?.getD .idle) F H log.length e ∧ log' = log ++ [e]

/-- Every prefix of an infinite execution from the empty log meets the timed program guards. -/
theorem programPrefix_of_execution {logs : ℕ → List (Event n V)} (init : logs 0 = [])
    (steps : (lts F H).OmegaExecution ⟨logs⟩ ⟨ev⟩) (T : ℕ) : ProgramPrefix ev F H T := by
  have step (k : ℕ) : (lts F H).Tr (logs k) (ev k) (logs (k + 1)) := steps k
  have hist (t : ℕ) : logs t = List.ofFn (fun i : Fin t => ev i) := by
    induction t with
    | zero => simpa using init
    | succ k ih => rw [(step k).2, ih, List.ofFn_succ_last]; rfl
  intro t
  have h := (step t.val).1
  rw [hist] at h
  simp only [List.length_ofFn] at h
  apply (enabled_congr (ev t) _).mp h
  intro i hi
  simp [hi]

/-- Conversely, a timed program prefix is a genuine finite multistep execution with precisely
those labels, starting from the empty history. No extension or future progress is needed. -/
theorem ProgramPrefix.mTr {T : ℕ} (h : ProgramPrefix ev F H T) :
    (lts F H).MTr [] (List.ofFn (fun i : Fin T => ev i)) (List.ofFn (fun i : Fin T => ev i)) := by
  induction T with
  | zero => simp
  | succ k ih =>
    have prev := ih (fun i => h ⟨i.val, by omega⟩)
    rw [List.ofFn_succ_last]
    apply LTS.MTr.stepR (lts F H) prev
    refine ⟨?_, rfl⟩
    simp only [List.length_ofFn]
    apply (enabled_congr _ _).mp (h ⟨k, by omega⟩)
    intro i hi
    simp [hi]

/-- A stream whose every finite prefix obeys the guards runs on the log machine without a
future oracle: at tick `t` its state consists of exactly its first `t` events. -/
theorem execution_of_programPrefixes (h : ∀ t, ProgramPrefix ev F H t) :
    ∃ logs : ℕ → List (Event n V), logs 0 = [] ∧ (lts F H).OmegaExecution ⟨logs⟩ ⟨ev⟩ := by
  let logs (t : ℕ) := List.ofFn (fun i : Fin t => ev i)
  refine ⟨logs, rfl, fun t => ?_⟩
  change Enabled _ F H (logs t).length (ev t) ∧ logs (t + 1) = logs t ++ [ev t]
  constructor
  · simp only [logs, List.length_ofFn]
    apply (enabled_congr _ _).mp (h (t + 1) ⟨t, by omega⟩)
    intro i hi
    simp [hi]
  · exact List.ofFn_succ_last ..

/-- A safety abstraction of Figure 6 runs for a single consensus instance. The same failure
pattern and trace witness a detector in the eventually strong class ◇S (strong completeness and
eventual weak accuracy), a history permitted by that detector, a strict correct majority, local
proposals by every correct process, eventual receipt of ordinary sends to correct destinations,
and reliable broadcast of the projected decision requests. A recipient need not have proposed
when a request is delivered. Each correct process is the actor
at arbitrarily late ticks. An unrestricted `wait p` counts, even at an enabled instruction;
this scheduling condition does not enforce local instruction progress or imply termination. -/
structure ArticleRun (ev : ℕ → Event n V) (F : FailureDetector.FailurePattern (Proc n))
    (D : FailureDetector.Detector (Proc n)) (H : FailureDetector.History (Proc n)) : Prop where
  execution : ∃ logs : ℕ → List (Event n V), logs 0 = [] ∧ (lts F H).OmegaExecution ⟨logs⟩ ⟨ev⟩
  detector : D ∈ FailureDetector.DetectorClass.eventuallyStrong.detectors
  history : H ∈ D F
  majority : ∃ Q : Finset (Proc n), (Paxos.QuorumSystem.majority _).IsQuorum Q ∧
    ∀ p ∈ Q, p ∈ F.correct
  proposes : ∀ p ∈ F.correct, ∃ t v, ev t = .propose p v
  scheduling : ∀ p ∈ F.correct, ∀ t, ∃ i ≥ t, (ev i).actor = some p
  channels : ∀ t m, (ev t).sent = some m → ∀ p, (Event.receive m).actor = some p →
    p ∈ F.correct → ∃ i > t, ev i = .receive m
  broadcast : ReliableBroadcast.IsReliableBroadcast (fun m : ℕ × V => coord n m.1)
    F.correct (fun t => (ev t).rb)

/-- At every cut, the whole-run safety abstraction with the canonical ◇S detector and reliable
broadcast projects to a legal prefix. The origin clause of broadcast integrity applies even at
receivers whose local decision handler ignores the upcall. No local progress premise is used. -/
theorem ArticleRun.legalPrefix {D : FailureDetector.Detector (Proc n)}
    (a : ArticleRun ev F D H) (T : ℕ) : LegalPrefix ev F H T := by
  obtain ⟨logs, hi, hs⟩ := a.execution
  refine ⟨programPrefix_of_execution hi hs T, ?_⟩
  intro t p r v h
  have hd : (ev t).rb = some (.deliver p (r, v)) := by rw [h]; rfl
  obtain ⟨i, hit, he⟩ := (a.broadcast.uniformIntegrity _ _ _ hd).2
  refine ⟨⟨i, hit⟩, ?_⟩
  change ev i = _
  cases heq : ev i with
  | finish k out => cases out <;> simp_all [Event.rb]
  | _ => simp_all [Event.rb]

end Cslib.Distributed.RotatingCoordinator
