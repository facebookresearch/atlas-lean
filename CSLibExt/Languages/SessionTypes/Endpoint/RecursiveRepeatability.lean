/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.Languages.SessionTypes.Endpoint.RecursiveOwnership

/-!
# Nonzero finite traces of actual repeated endpoint actions

A trace indexes states of the SAME finite replicated Pi code. Each edge is
canonical Step, with one actual session communication per three edges. This
is finite repeatability, not fairness, termination or general runtime progress.
-/

@[expose] public section

namespace Cslib.SessionTypes.Endpoint.Runtime

open PiCalculus

/-- Three phases of actual execution; this does not generate unrolled Pi code. -/
def phase (b : Name) (i : Nat) : Proc :=
  match i % 3 with
  | 0 => pending b
  | 1 => sentInvoked b
  | _ => bothInvoked b

/-- Every consecutive phase has a real canonical Step, including session reentry. -/
theorem phase_step (b : Name) (i : Nat) : PiCalculus.Step (phase b i) (phase b (i + 1)) := by
  have hm := Nat.mod_lt i (by decide : 0 < 3)
  rcases (by omega : i % 3 = 0 ∨ i % 3 = 1 ∨ i % 3 = 2) with h | h | h
  · simpa [phase, Nat.add_mod, h] using sender_invocation b
  · simpa [phase, Nat.add_mod, h] using receiver_invocation b
  · simpa [phase, Nat.add_mod, h] using session_and_reentry b

/-- For EVERY requested count, a nonzero trace returns to the identical pending code.
It has exactly three times (m+1) actual Steps, never a reflexive reachability proof. -/
theorem repeatable_trace (b : Name) (m : Nat) :
    ∃ f : Fin (3 * (m + 1) + 1) → Proc,
      f ⟨0, by omega⟩ = pending b ∧
      f ⟨3 * (m + 1), Nat.lt_succ_self _⟩ = pending b ∧
      (∀ i : Fin (3 * (m + 1)), PiCalculus.Step (f i.castSucc) (f i.succ)) ∧
      ∀ j : Fin (m + 1),
        f ⟨3 * j.val + 2, by omega⟩ = bothInvoked b ∧
          f ⟨3 * j.val + 3, by omega⟩ = pending b := by
  refine ⟨fun i => phase b i.val, ?_, ?_, ?_, ?_⟩
  · simp [phase]
  · simp [phase]
  · intro i
    exact phase_step b i.val
  · intro j
    constructor
    · simp [phase, Nat.add_mod]
    · simp [phase]

/-- EVERY round contains an actual action on the SAME session endpoint b. -/
theorem session_round_phase (b : Name) (i : Nat) :
    phase b (3 * i + 2) = bothInvoked b ∧ phase b (3 * i + 3) = pending b ∧
      PiCalculus.Step (phase b (3 * i + 2)) (phase b (3 * i + 3)) := by
  have h₁ : phase b (3 * i + 2) = bothInvoked b := by simp [phase, Nat.add_mod]
  have h₂ : phase b (3 * i + 3) = pending b := by simp [phase]
  exact ⟨h₁, h₂, h₁ ▸ h₂ ▸ session_and_reentry b⟩

/-- Every actual runtime phase retains the same exact two-role linear interface. -/
theorem phase_typed {n : Nat} (r : Role) (b : Name) (hb : b.ClosedAt n)
    (hf : EndpointFresh b) (i : Nat) :
    HasType n (services r) (recurringInterface b r) (phase b i) := by
  have hm := Nat.mod_lt i (by decide : 0 < 3)
  rcases (by omega : i % 3 = 0 ∨ i % 3 = 1 ∨ i % 3 = 2) with h | h | h
  · simpa [phase, h] using pending_typed r b hb hf
  · simpa [phase, h] using sentInvoked_typed r b hb hf
  · simpa [phase, h] using bothInvoked_typed r b hb hf

/-- Arbitrarily long NONZERO actual execution with ownership at EVERY state.
The conclusion is a trace; no trace/Step/result is part of service admission. -/
theorem typed_repeatable_trace {n : Nat} (r : Role) (b : Name) (hb : b.ClosedAt n)
    (hf : EndpointFresh b) (m : Nat) :
    ∃ f : Fin (3 * (m + 1) + 1) → Proc,
      f ⟨0, by omega⟩ = pending b ∧
      f ⟨3 * (m + 1), Nat.lt_succ_self _⟩ = pending b ∧
      (∀ i : Fin (3 * (m + 1)), PiCalculus.Step (f i.castSucc) (f i.succ)) ∧
      (∀ i, HasType n (services r) (recurringInterface b r) (f i)) ∧
      ∀ j : Fin (m + 1),
        f ⟨3 * j.val + 2, by omega⟩ = bothInvoked b ∧
          f ⟨3 * j.val + 3, by omega⟩ = pending b := by
  refine ⟨fun i => phase b i.val, ?_, ?_, ?_, ?_, ?_⟩
  · simp [phase]
  · simp [phase]
  · intro i
    exact phase_step b i.val
  · intro i
    exact phase_typed r b hb hf i.val
  · intro j
    exact ⟨(session_round_phase b j.val).1, (session_round_phase b j.val).2.1⟩

/-- Induction on actual Step count reaches each phase of the persistent runtime code. -/
theorem phase_reachable (b : Name) (i : Nat) :
    Relation.ReflTransGen PiCalculus.Step (pending b) (phase b i) := by
  induction i with
  | zero => exact .refl
  | succ i ih => exact ih.tail (phase_step b i)

/-- Actual unguarded daemons offer BOTH declared services at EVERY runtime phase. -/
theorem phase_offers (b : Name) (r : Role) (i : Nat) :
    Offered (services r) (phase b i) 710 (senderSignature r) ∧
      Offered (services r) (phase b i) 711 (receiverSignature r) := by
  have hm := Nat.mod_lt i (by decide : 0 < 3)
  have hh : i % 3 = 0 ∨ i % 3 = 1 ∨ i % 3 = 2 := by omega
  constructor
  · refine ⟨sender_declared r, ?_⟩
    rcases hh with h | h | h <;>
      simp [phase, h, OfferedIn, AcceptIn, pending, sentInvoked, bothInvoked,
        senderDaemon, receiverDaemon]
  · refine ⟨receiver_declared r, ?_⟩
    rcases hh with h | h | h <;>
      simp [phase, h, OfferedIn, AcceptIn, pending, sentInvoked, bothInvoked,
        senderDaemon, receiverDaemon]

end Cslib.SessionTypes.Endpoint.Runtime
