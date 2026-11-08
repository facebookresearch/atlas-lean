/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Deadlock and circular wait
-/
module

public import Mathlib.Logic.Relation
public import Mathlib.Data.Fintype.Pigeonhole
public import Mathlib.Data.Set.Finite.Basic

/-!
# Deadlock and circular wait

Snapshots of resource allocation with single-instance resources (Coffman,
Elphick and Shoshani, *System deadlocks*, ACM Computing Surveys 3(2), 1971;
Holt, *Some deadlock properties of computer systems*, ACM Computing Surveys
4(3), 1972). A snapshot (`AllocState`) records the holder of each resource, if
any, and the outstanding requests; a process never requests a resource it
already holds. Mutual exclusion is built in: each resource has at most one
holder. The other conditions of Coffman et al. are assumptions of the reading,
not of the static model: requests follow the AND model (a process waits until
all its requests are granted), processes keep what they hold while waiting
(hold and wait), and nothing is taken from a holder (no preemption). Under those
assumptions a deadlocked set is a graph property of the snapshot, stated with
the wait-for relation (`WaitsFor`): `p` waits for `q` when `p` requests a
resource held by `q`. Circular wait is a cycle of `WaitsFor`.

* `Deadlocked s D`: a nonempty set of processes, each waiting for a resource
  held by a member of the set. Under the assumptions above, none of them can
  proceed and none will release what it holds.
* `exists_deadlocked_of_circularWait`: circular wait gives a deadlocked set.
* `circularWait_of_deadlocked`: with finitely many processes, a deadlocked set
  contains a cycle of the wait-for relation. So `deadlock_iff_circularWait`:
  for finitely many processes, deadlock is exactly circular wait. Finiteness is
  needed: an infinite chain of processes each waiting for the next is
  deadlocked without a cycle (see the tests).
* `not_circularWait_of_ordered`, `not_deadlocked_of_ordered`: Havender's
  resource ordering (*Avoiding deadlock in multitasking systems*, IBM Systems
  Journal 7(2), 1968). If every process requests only resources ranked above
  every resource it holds, there is no circular wait, hence, with finitely many
  processes, no deadlock.
-/

@[expose] public section

namespace Cslib.Algorithms.Concurrency.Deadlock

variable {P Res : Type*}

/-- A resource-allocation snapshot: the holder of each single-instance resource,
if any, and the outstanding requests of each process. -/
structure AllocState (P Res : Type*) where
  /-- The process holding each resource, if any. -/
  holder : Res → Option P
  /-- Outstanding requests. -/
  requests : P → Res → Prop
  /-- A process does not request a resource it holds. -/
  requests_not_held : ∀ p r, requests p r → holder r ≠ some p

namespace AllocState

variable (s : AllocState P Res)

/-- `p` waits for `q`: `p` requests a resource held by `q`. -/
def WaitsFor (p q : P) : Prop := ∃ r, s.requests p r ∧ s.holder r = some q

/-- A deadlocked set of processes: nonempty, and each member waits for a
resource held by a member. -/
def Deadlocked (D : Set P) : Prop := D.Nonempty ∧ ∀ p ∈ D, ∃ q ∈ D, s.WaitsFor p q

/-- Circular wait: some process waits for itself through a chain of
wait-for edges. -/
def CircularWait : Prop := ∃ p, Relation.TransGen s.WaitsFor p p

variable {s}

/-- No process waits for itself directly. -/
theorem not_waitsFor_self (p : P) : ¬ s.WaitsFor p p := fun ⟨r, hreq, hheld⟩ =>
  s.requests_not_held p r hreq hheld

/-- A request for a free resource creates no wait-for edge. -/
theorem not_waitsFor_of_free {p q : P} (hfree : ∀ r, s.requests p r → s.holder r = none) :
    ¬ s.WaitsFor p q := fun ⟨r, hreq, hheld⟩ => by simp [hfree r hreq] at hheld

/-- Circular wait gives a deadlocked set: the processes on a cycle through `p`. -/
theorem exists_deadlocked_of_circularWait (h : s.CircularWait) : ∃ D, s.Deadlocked D := by
  obtain ⟨p, hp⟩ := h
  refine ⟨{q | Relation.TransGen s.WaitsFor p q ∧ Relation.TransGen s.WaitsFor q p},
    ⟨p, hp, hp⟩, ?_⟩
  rintro q ⟨hpq, hqp⟩
  obtain ⟨q', hqq', hq'p⟩ := Relation.TransGen.head'_iff.mp hqp
  refine ⟨q', ⟨hpq.tail hqq', ?_⟩, hqq'⟩
  rcases Relation.ReflTransGen.cases_head hq'p with rfl | ⟨m, hm, hmp⟩
  · exact hp
  · exact Relation.TransGen.head' hm hmp

/-- With finitely many processes, a deadlocked set contains a wait-for cycle:
following wait-for edges inside the set must revisit a process. -/
theorem circularWait_of_deadlocked [Finite P] {D : Set P} (h : s.Deadlocked D) :
    s.CircularWait := by
  obtain ⟨⟨p₀, hp₀⟩, hsucc⟩ := h
  choose next hnext hwait using hsucc
  let g : D → D := fun x => ⟨next x.1 x.2, hnext x.1 x.2⟩
  let seq : ℕ → D := fun k => g^[k] ⟨p₀, hp₀⟩
  have hstep : ∀ k, s.WaitsFor (seq k).1 (seq (k + 1)).1 := fun k => by
    simp only [seq, Function.iterate_succ_apply']
    exact hwait _ _
  have hchain : ∀ i d, Relation.TransGen s.WaitsFor (seq i).1 (seq (i + d + 1)).1 := by
    intro i d
    induction d with
    | zero => exact .single (hstep i)
    | succ d ih => exact ih.tail (hstep (i + d + 1))
  obtain ⟨i, j, hij, heq⟩ := Finite.exists_ne_map_eq_of_infinite seq
  rcases Nat.lt_or_gt_of_ne hij with hlt | hlt
  · refine ⟨(seq i).1, ?_⟩
    have := hchain i (j - i - 1)
    rwa [show i + (j - i - 1) + 1 = j by omega, ← heq] at this
  · refine ⟨(seq j).1, ?_⟩
    have := hchain j (i - j - 1)
    rwa [show j + (i - j - 1) + 1 = i by omega, heq] at this

/-- **Deadlock is circular wait** (finitely many processes). -/
theorem deadlock_iff_circularWait [Finite P] : (∃ D, s.Deadlocked D) ↔ s.CircularWait :=
  ⟨fun ⟨_, hD⟩ => circularWait_of_deadlocked hD, exists_deadlocked_of_circularWait⟩

/-! ## Resource ordering -/

/-- Havender's discipline: a process requests only resources ranked above every
resource it holds. -/
def Ordered (rank : Res → ℕ) : Prop :=
  ∀ p r r', s.requests p r → s.holder r' = some p → rank r' < rank r

/-- Along a wait-for chain from `p` to `q`, the resource `p` requests first and
the resource `q` holds last are linked by a chain of "held by a process that
requests" steps. -/
private theorem chain_of_transGen {p q : P} (h : Relation.TransGen s.WaitsFor p q) :
    ∃ r₁ r₂, s.requests p r₁ ∧ s.holder r₂ = some q ∧
      Relation.ReflTransGen (fun r r' => ∃ m, s.holder r = some m ∧ s.requests m r') r₁ r₂ := by
  induction h with
  | single hpq =>
      obtain ⟨r, hreq, hheld⟩ := hpq
      exact ⟨r, r, hreq, hheld, .refl⟩
  | tail _ hmq ih =>
      obtain ⟨r₁, r₂, hreq, hheld, hchain⟩ := ih
      obtain ⟨r, hreq', hheld'⟩ := hmq
      exact ⟨r₁, r, hreq, hheld', hchain.tail ⟨_, hheld, hreq'⟩⟩

/-- **Resource ordering prevents circular wait.** -/
theorem not_circularWait_of_ordered {rank : Res → ℕ} (hord : s.Ordered rank) :
    ¬ s.CircularWait := by
  rintro ⟨p, hp⟩
  obtain ⟨r₁, r₂, hreq, hheld, hchain⟩ := chain_of_transGen hp
  have hmono : ∀ a b, Relation.ReflTransGen
      (fun r r' => ∃ m, s.holder r = some m ∧ s.requests m r') a b → rank a ≤ rank b := by
    intro a b hab
    induction hab with
    | refl => exact le_rfl
    | tail _ hstep ih =>
        obtain ⟨m, hheld', hreq'⟩ := hstep
        exact ih.trans (hord m _ _ hreq' hheld').le
  exact absurd ((hmono _ _ hchain).trans_lt (hord p r₁ r₂ hreq hheld)) (lt_irrefl _)

/-- **Resource ordering prevents deadlock** (finitely many processes). -/
theorem not_deadlocked_of_ordered [Finite P] {rank : Res → ℕ} (hord : s.Ordered rank)
    (D : Set P) : ¬ s.Deadlocked D :=
  fun hD => not_circularWait_of_ordered hord (circularWait_of_deadlocked hD)

end AllocState

end Cslib.Algorithms.Concurrency.Deadlock
