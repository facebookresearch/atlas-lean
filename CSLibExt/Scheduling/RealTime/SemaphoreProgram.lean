/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Data.Fintype.Basic
public import Mathlib.Data.List.OfFn

/-!
# Matched critical sections of a finite job

A straight-line instruction stream is specified by its length and a table of matching pairs of
atomic semaphore operations in order of acquisition. All other instructions are ordinary CPU
work. Disjoint sections may use the same semaphore; nested sections may not. The table is a
finite representation of the program, not a list of locks held continuously from job release.

We use one processor slot per instruction. The duration of the code *between* the two operations
counts the owner's instructions strictly between them (including nested operations), not slots
spent waiting or preempted. The P and V instructions themselves each occupy a separate slot.

Source: L. Sha, R. Rajkumar and J. P. Lehoczky, “Priority Inheritance Protocols: An Approach to
Real-Time Synchronization”, IEEE Transactions on Computers 39(9), 1990, §II, pp. 1176–1177.
-/

@[expose] public section

namespace Cslib.Scheduling.RealTime.Semaphore

/-- A section descriptor records a semaphore name and two local instruction addresses. A `Program`
checks that these are matching P and V endpoints. Different occurrences may share a name. -/
structure Section (R : Type*) where
  /-- Semaphore acquired and released by this occurrence. -/
  lock : R
  /-- Local address of the P instruction. -/
  enter : ℕ
  /-- Local address of the matching V instruction. -/
  leave : ℕ
  deriving DecidableEq

variable {R : Type*}

/-- Strict containment of one section in another: both endpoints are strictly interior. -/
abbrev Section.Inside (a b : Section R) : Prop := b.enter < a.enter ∧ a.leave < b.leave

/-- At the boundary before local instruction `pc`, a section is open after its P and up to
and including the boundary before its V. -/
abbrev Section.Held (a : Section R) (pc : ℕ) : Prop := a.enter < pc ∧ pc ≤ a.leave

/-- Solo duration of the section body in unit instruction slots, excluding the matching P and V. -/
def Section.duration (a : Section R) : ℕ := a.leave - (a.enter + 1)

/-- Compatibility in acquisition order: disjoint, or strictly nested on different semaphores. -/
abbrev Section.Before (a b : Section R) : Prop :=
  a.leave < b.enter ∨ (b.Inside a ∧ a.lock ≠ b.lock)

/-- A finite instruction program specified by its length and its table of matching P/V pairs.
The table is indexed in order of the P instructions; every pair is in bounds, and every two
pairs in opening order are disjoint or properly nested on distinct locks. -/
structure Program (R : Type*) where
  /-- Number of local instructions. -/
  length : ℕ
  /-- Number of matching P/V pairs. -/
  count : ℕ
  /-- Section of the indicated P instruction (zero based). -/
  sec : Fin count → Section R
  /-- Both instructions occur in the program, in order. -/
  bounds : ∀ k, (sec k).enter < (sec k).leave ∧ (sec k).leave < length
  /-- Pairwise check, including non-adjacent ancestors of nested sections. -/
  ordered : ∀ k l, k < l → (sec k).Before (sec l)

/-- Atomic instructions of a job using binary semaphores. Only completion of a P or V changes
lock ownership; an ordinary CPU instruction needs no matching operation. -/
inductive Instruction (R : Type*)
  | cpu
  | acquire (s : R)
  | release (s : R)
  deriving DecidableEq

namespace Program

variable (p : Program R)

/-- The P/V table gives the instruction at a local address. Every non-endpoint is a CPU
instruction; addresses at or beyond the program length are never executed. -/
def instruction (pc : ℕ) : Instruction R :=
  match (List.ofFn p.sec).find? (fun z => z.enter == pc) with
  | some z => .acquire z.lock
  | none => match (List.ofFn p.sec).find? (fun z => z.leave == pc) with
    | some z => .release z.lock
    | none => .cpu

/-- P and V addresses are each unique, and no P address is a V address. -/
theorem endpoints (k l : Fin p.count) :
    ((p.sec k).enter = (p.sec l).enter → k = l) ∧
    ((p.sec k).leave = (p.sec l).leave → k = l) ∧ (p.sec k).enter ≠ (p.sec l).leave := by
  have := p.bounds k
  have := p.bounds l
  rcases lt_trichotomy k l with h | rfl | h
  · rcases p.ordered k l h with h | ⟨⟨h₁, h₂⟩, _⟩ <;> omega
  · exact ⟨fun _ => rfl, fun _ => rfl, by omega⟩
  · rcases p.ordered l k h with h | ⟨⟨h₁, h₂⟩, _⟩ <;> omega

private theorem find_endpoint (key : Section R → ℕ) (k : Fin p.count)
    (uniq : ∀ l, key (p.sec l) = key (p.sec k) → l = k) :
    (List.ofFn p.sec).find? (fun z => key z == key (p.sec k)) = some (p.sec k) := by
  cases h : (List.ofFn p.sec).find? (fun z => key z == key (p.sec k)) with
  | none => simpa using (List.find?_eq_none.mp h (p.sec k) (List.mem_ofFn.mpr ⟨k, rfl⟩))
  | some z =>
    obtain ⟨l, rfl⟩ := List.mem_ofFn.mp (List.mem_of_find?_eq_some h)
    have he := uniq l (by simpa using List.find?_some h)
    rw [he]

/-- Entering and leaving an occurrence really execute P and V of the very same semaphore. -/
theorem matching (k : Fin p.count) :
    p.instruction (p.sec k).enter = .acquire (p.sec k).lock ∧
    p.instruction (p.sec k).leave = .release (p.sec k).lock := by
  have hn : (List.ofFn p.sec).find? (fun z => z.enter == (p.sec k).leave) = none := by
    apply List.find?_eq_none.mpr
    intro z hz
    obtain ⟨l, rfl⟩ := List.mem_ofFn.mp hz
    simpa using (p.endpoints l k).2.2
  simp [instruction, p.find_endpoint Section.enter k (fun l => (p.endpoints l k).1), hn,
    p.find_endpoint Section.leave k (fun l => (p.endpoints l k).2.1)]

/-- An acquire instruction never requests a semaphore the job already holds. -/
theorem fresh (k l : Fin p.count) (h : (p.sec l).Held (p.sec k).enter) :
    (p.sec k).lock ≠ (p.sec l).lock := by
  have := p.bounds k
  have := p.bounds l
  obtain ⟨h₁, h₂⟩ := h
  rcases lt_trichotomy k l with hk | rfl | hl
  · rcases p.ordered k l hk with hd | ⟨⟨ha, hb⟩, _⟩ <;> omega
  · omega
  · rcases p.ordered l k hl with hd | ⟨_, hn⟩
    · omega
    · exact hn.symm

/-- At termination no critical section is still open. -/
theorem released_at_end (k : Fin p.count) : ¬ (p.sec k).Held p.length := by
  have := p.bounds k
  simp [Section.Held, not_le.mpr this.2]

end Program
end Cslib.Scheduling.RealTime.Semaphore
