/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import CSLibExt.Foundations.Semantics.WeakMemory.X86TSOAbstractMachine

/-! # Single-step tests for the x86-TSO abstract machine -/

namespace Cslib.Semantics.WeakMemory.X86TSO

private abbrev machine := abstractMachine Bool Nat Nat

private def pending : State Bool Nat Nat where
  memory := fun _ => 40
  buffers := fun p => if p then [(2, 31)] else [(0, 11), (0, 13), (1, 21)]
  lockOwner := none

private def blocked : State Bool Nat Nat := { pending with lockOwner := some true }

private def emptyLocal : State Bool Nat Nat :=
  { pending with buffers := fun p => if p then [(2, 31)] else [] }

private def owned : State Bool Nat Nat := { emptyLocal with lockOwner := some false }

private def ownedPending : State Bool Nat Nat := { pending with lockOwner := some false }

-- The second write to address 0 is forwarded, despite a newer write to a different address.
example : machine.Tr pending (.read false 0 13) pending :=
  Step.readBuffer (Or.inl rfl) rfl

example : machine.Tr ownedPending (.read false 0 13) ownedPending :=
  Step.readBuffer (Or.inr rfl) rfl

example (target : State Bool Nat Nat) : ¬ machine.Tr pending (.read false 0 11) target := by
  intro h
  change Step _ _ _ at h
  cases h with
  | readBuffer _ hvalue => simp [State.latestWrite, pending] at hvalue

-- A pending write masks the shared value at its address.
example (target : State Bool Nat Nat) : ¬ machine.Tr pending (.read false 0 40) target := by
  intro h
  change Step _ _ _ at h
  cases h with
  | readMemory _ hmiss => simp [State.latestWrite, pending] at hmiss
  | readBuffer _ hvalue => simp [State.latestWrite, pending] at hvalue

-- Pending writes by another thread do not mask the shared value.
example : machine.Tr pending (.read false 2 40) pending :=
  Step.readMemory (Or.inl rfl) rfl

example (target : State Bool Nat Nat) : ¬ machine.Tr blocked (.read false 0 13) target := by
  intro h
  change Step _ _ _ at h
  cases h with
  | readBuffer hunblocked _ => simp [State.NotBlocked, blocked] at hunblocked

example (target : State Bool Nat Nat) : ¬ machine.Tr blocked (.read false 2 40) target := by
  intro h
  change Step _ _ _ at h
  cases h with
  | readMemory hunblocked _ => simp [State.NotBlocked, blocked] at hunblocked
  | readBuffer hunblocked _ => simp [State.NotBlocked, blocked] at hunblocked

-- Enqueue does not propagate a write or change the other thread's buffer or lock ownership.
example : machine.Tr blocked (.write false 0 15)
    { blocked with buffers := fun p => if p then [(2, 31)]
        else [(0, 11), (0, 13), (1, 21), (0, 15)] } := by
  have hbuffers : Function.update blocked.buffers false (blocked.buffers false ++ [(0, 15)]) =
      (fun p => if p then [(2, 31)] else [(0, 11), (0, 13), (1, 21), (0, 15)]) := by
    funext p
    cases p <;> rfl
  rw [← hbuffers]
  exact Step.write blocked false 0 15

-- Propagation removes the FIFO head, not the value that forwarding would return.
-- All other addresses, the other buffer, and the lock are unchanged.
example : machine.Tr ownedPending (.flush false)
    { ownedPending with memory := fun a => if a = 0 then 11 else 40
                        buffers := fun p => if p then [(2, 31)] else [(0, 13), (1, 21)] } := by
  have hmemory : Function.update ownedPending.memory 0 11 =
      (fun a => if a = 0 then 11 else 40) := by
    funext a
    by_cases ha : a = 0 <;> simp [Function.update, ownedPending, pending, ha]
  have hbuffers : Function.update ownedPending.buffers false [(0, 13), (1, 21)] =
      (fun p => if p then [(2, 31)] else [(0, 13), (1, 21)]) := by
    funext p
    cases p <;> rfl
  rw [← hmemory, ← hbuffers]
  exact Step.flush (s := ownedPending) (p := false) (a := 0) (value := 11)
    (tail := [(0, 13), (1, 21)]) (Or.inr rfl) rfl

example (target : State Bool Nat Nat) (h : machine.Tr pending (.flush false) target) :
    target.memory 0 ≠ 13 := by
  change Step _ _ _ at h
  cases h with
  | flush _ oldest =>
      simp [pending] at oldest
      obtain ⟨⟨rfl, rfl⟩, rfl⟩ := oldest
      decide

example (target : State Bool Nat Nat) : ¬ machine.Tr blocked (.flush false) target := by
  intro h
  change Step _ _ _ at h
  cases h with
  | flush hunblocked _ => simp [State.NotBlocked, blocked] at hunblocked

example (target : State Bool Nat Nat) : ¬ machine.Tr emptyLocal (.flush false) target := by
  intro h
  change Step _ _ _ at h
  cases h with
  | flush _ oldest => simp [emptyLocal] at oldest

-- MFENCE checks only the acting thread's buffer, even if another thread holds the lock.
example :
    let s := { emptyLocal with lockOwner := some true }
    machine.Tr s (.mfence false) s :=
  Step.mfence rfl

example (target : State Bool Nat Nat) : ¬ machine.Tr pending (.mfence false) target := by
  intro h
  change Step _ _ _ at h
  cases h with
  | mfence hempty => simp [pending] at hempty

-- Acquisition and release change only the owner, and do not inspect other buffers.
example : machine.Tr emptyLocal (.acquire false) owned := Step.acquire rfl rfl

example : machine.Tr owned (.release false) emptyLocal := Step.release rfl rfl

example (target : State Bool Nat Nat) : ¬ machine.Tr owned (.acquire false) target := by
  intro h
  change Step _ _ _ at h
  cases h with
  | acquire hfree _ => simp [owned] at hfree

example (target : State Bool Nat Nat) : ¬ machine.Tr pending (.acquire false) target := by
  intro h
  change Step _ _ _ at h
  cases h with
  | acquire _ hempty => simp [pending] at hempty

example (target : State Bool Nat Nat) :
    ¬ machine.Tr { emptyLocal with lockOwner := some true } (.release false) target := by
  intro h
  change Step _ _ _ at h
  cases h with
  | release howner _ => simp at howner

example (target : State Bool Nat Nat) :
    ¬ machine.Tr { pending with lockOwner := some false } (.release false) target := by
  intro h
  change Step _ _ _ at h
  cases h with
  | release _ hempty => simp [pending] at hempty

end Cslib.Semantics.WeakMemory.X86TSO
