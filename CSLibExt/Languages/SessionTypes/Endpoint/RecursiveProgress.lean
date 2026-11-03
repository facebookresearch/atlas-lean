/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.Languages.SessionTypes.Endpoint.RuntimeGlobalProgress
public import CSLibExt.Languages.SessionTypes.Endpoint.RecursiveReduction
public import CSLibExt.Languages.SessionTypes.Endpoint.RecursiveQuiescence

/-!
# Actual repeated-session runtime through GENERAL qualified progress

Exposed outputs exclude Idle independently of the previously chosen execution.
-/

@[expose] public section

namespace Cslib.SessionTypes.Endpoint.Runtime

open PiCalculus

private theorem phase_output (b : Name) (i : Nat) : HasUnguardedOutput (phase b i) := by
  have hm : i % 3 < 3 := Nat.mod_lt i (by decide)
  have hh : i % 3 = 0 ∨ i % 3 = 1 ∨ i % 3 = 2 := by omega
  rcases hh with h | h | h <;>
    simp [phase, h, HasUnguardedOutput, pending, sentInvoked, bothInvoked,
      senderRequest, receiverRequest, senderWorker, receiverWorker]

/-- GENERAL qualified progress produces an ACTUAL Step at every recursive phase,
BOTH roles and arbitrary scoped endpoint. Idle is excluded by exposed output syntax,
not by assuming the previously selected execution or readiness. -/
theorem phase_general_step {n : Nat} (r : Role) (b : Name) (hb : b.ClosedAt n)
    (hf : EndpointFresh b) (i : Nat) : ∃ q, PiCalculus.Step (phase b i) q := by
  rcases (phase_typed_by_preservation r b hb hf i).progress_balanced
    (recurring_balanced b r) (phase_available_by_reduction b r i) with hi | hs
  · exact False.elim (hi.no_unguarded_output (phase_output b i))
  · exact hs

private theorem bound_phase_typed (r : Role) (i : Nat) :
    HasType 0 (services r) ∅ (.nu (phase (.var 0) i)) := by
  have hp := phase_typed_by_preservation r (.var 0) (Nat.zero_lt_succ 0)
    (by constructor <;> intro h <;> cases h) i
  cases r with
  | positive =>
    apply HasType.nu (c := recurringCap) (separated_empty _)
    rw [Context.bind_empty]
    exact hp
  | negative =>
    apply HasType.nu (c := recurringCap.dual) (separated_empty _)
    rw [Context.bind_empty, Capability.dual_dual]
    rw [Finmap.union_comm_of_disjoint (by simp [Finmap.Disjoint, Finmap.mem_singleton])]
    exact hp

/-- GENERAL empty-interface progress includes the genuine private session in
BOTH orientations/all phases. Actual output syntax forces its Step branch. -/
theorem bound_phase_general_step (r : Role) (i : Nat) :
    ∃ q, PiCalculus.Step (.nu (phase (.var 0) i)) q := by
  rcases (bound_phase_typed r i).progress_empty
    (phase_available_by_reduction (.var 0) r i) with hi | hs
  · exact False.elim (hi.no_unguarded_output (phase_output (.var 0) i))
  · exact hs

/-- EVERY m has a SAME-witness counted repeated-session trace, all state types,
actual availability and ALL marked session edges, plus GENERAL progress at EVERY
state (including the last). This is not all-schedules fairness or termination. -/
theorem repeatable_trace_global {n : Nat} (r : Role) (b : Name) (hb : b.ClosedAt n)
    (hf : EndpointFresh b) (m : Nat) :
    ∃ f : Fin (3 * (m + 1) + 1) → Proc,
      f ⟨0, by omega⟩ = pending b ∧
      f ⟨3 * (m + 1), Nat.lt_succ_self _⟩ = pending b ∧
      (∀ i : Fin (3 * (m + 1)), PiCalculus.Step (f i.castSucc) (f i.succ)) ∧
      (∀ i, HasType n (services r) (recurringInterface b r) (f i)) ∧
      (∀ i, Available (services r) (f i)) ∧
      (∀ i, ∃ q, PiCalculus.Step (f i) q) ∧
      ∀ j : Fin (m + 1),
        f ⟨3 * j.val + 2, by omega⟩ = bothInvoked b ∧
          f ⟨3 * j.val + 3, by omega⟩ = pending b := by
  refine ⟨fun i => phase b i.val, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp [phase]
  · simp [phase]
  · intro i
    exact phase_step b i.val
  · intro i
    exact phase_typed_by_preservation r b hb hf i.val
  · intro i
    exact phase_available_by_reduction b r i.val
  · intro i
    exact phase_general_step r b hb hf i.val
  · intro j
    exact ⟨(session_round_phase b j.val).1, (session_round_phase b j.val).2.1⟩

end Cslib.SessionTypes.Endpoint.Runtime
