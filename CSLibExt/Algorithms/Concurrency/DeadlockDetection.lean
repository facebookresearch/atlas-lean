/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Deadlock detection with multiple resource instances
-/
module

public import Mathlib.Data.Fintype.Pi
public import Mathlib.Algebra.Order.Pi
public import Mathlib.Algebra.BigOperators.Group.List.Basic
public import Mathlib.Data.List.Perm.Basic

/-!
# Deadlock detection with multiple resource instances

The deadlock-detection algorithm for resources with several instances
(E. G. Coffman, M. J. Elphick and A. Shoshani, *System deadlocks*, ACM
Computing Surveys 3(2), 1971; R. C. Holt, *Some deadlock properties of computer
systems*, ACM Computing Surveys 4(3), 1972, graph reduction). Resource vectors
are functions `R → ℕ` on a finite set of resource types, ordered componentwise.

Each process `p` holds `alloc p` and is blocked on its outstanding request
`request p`. A *reduction sequence* (`Reduces`) from the free vector `work`
lists processes that can finish one after another: each one's request fits in
what is free, and when it finishes it releases its allocation.

`detect` is the detection algorithm: repeatedly let any process whose request
fits finish and release its allocation; the processes left over are reported.
They are the permanently blocked processes of Holt's graph reduction. This
includes processes that hold nothing but wait for resources held by deadlocked
processes; the textbook version of the algorithm (Silberschatz, Galvin and
Gagne, *Operating System Concepts*, Section 7.6.2) marks processes with zero
allocation as finished at the start, and so reports only resource holders.
The results:

* `detect_stuck`: every reported process requests more than is free even after
  all the processes that the algorithm lets finish have released their
  allocations.
* `mem_detect_iff`: a pending process is reported exactly when no reduction
  sequence finishes it. In particular the report does not depend on the order
  in which the algorithm picks processes (Holt's uniqueness of the irreducible
  state).
* `detect_eq_nil_iff`: nothing is reported exactly when all the processes can
  finish in some order (complete reducibility).

The list of pending processes is assumed to be duplicate-free. The model is
the standard one of these papers: a blocked process waits for its whole
request, holds what it has (hold and wait), and is not preempted.
-/

@[expose] public section

namespace Cslib.Algorithms.Concurrency.DeadlockDetection

variable {P R : Type*}

/-- Allocations and outstanding requests of the processes. -/
structure State (P R : Type*) where
  /-- The resources each process holds. -/
  alloc : P → R → ℕ
  /-- The resources each process is waiting for. -/
  request : P → R → ℕ

namespace State

variable (S : State P R)

/-- `Reduces S work σ`: starting with `work` free, each process of `σ` in turn
gets its request, finishes, and releases its allocation. -/
def Reduces : (R → ℕ) → List P → Prop
  | _, [] => True
  | work, p :: rest => S.request p ≤ work ∧ Reduces (work + S.alloc p) rest

@[simp] theorem reduces_nil (work : R → ℕ) : S.Reduces work [] := trivial

@[simp] theorem reduces_cons (work : R → ℕ) (p : P) (rest : List P) :
    S.Reduces work (p :: rest) ↔ S.request p ≤ work ∧ S.Reduces (work + S.alloc p) rest :=
  Iff.rfl

/-- Whether a list is a reduction sequence is decidable. -/
instance decidableReduces [Fintype R] :
    (work : R → ℕ) → (σ : List P) → Decidable (S.Reduces work σ)
  | _, [] => isTrue trivial
  | work, p :: rest =>
      have := decidableReduces (work + S.alloc p) rest
      inferInstanceAs (Decidable (S.request p ≤ work ∧ S.Reduces (work + S.alloc p) rest))

variable {S}

/-- If a process can finish now, letting it finish first keeps any reduction
sequence valid without it. -/
theorem Reduces.erase [DecidableEq P] {work : R → ℕ} {σ : List P} {p : P}
    (h : S.Reduces work σ) (hfit : S.request p ≤ work) :
    S.Reduces (work + S.alloc p) (σ.erase p) := by
  induction σ generalizing work with
  | nil => trivial
  | cons q rest ih =>
      by_cases hqp : q = p
      · subst hqp
        simpa using h.2
      · rw [List.erase_cons_tail (by simpa using hqp)]
        refine ⟨h.1.trans fun r => Nat.le_add_right _ _, ?_⟩
        have := ih h.2 (hfit.trans fun r => Nat.le_add_right _ _)
        rwa [add_right_comm] at this

/-- A reduction sequence whose processes all request more than `work` is
empty. -/
theorem Reduces.eq_nil {work : R → ℕ} {σ : List P} (h : S.Reduces work σ)
    (hstuck : ∀ q ∈ σ, ¬ S.request q ≤ work) : σ = [] := by
  cases σ with
  | nil => rfl
  | cons q rest => exact absurd h.1 (hstuck q (List.mem_cons_self ..))

variable (S) [DecidableEq P] [Fintype R]

/-- The detection algorithm with explicit fuel; returns the processes that
finished, in order, and the processes left over. -/
def reduceAux : ℕ → (R → ℕ) → List P → List P × List P
  | 0, _, pending => ([], pending)
  | fuel + 1, work, pending =>
      match pending.find? (fun p => decide (S.request p ≤ work)) with
      | none => ([], pending)
      | some p =>
          let r := reduceAux fuel (work + S.alloc p) (pending.erase p)
          (p :: r.1, r.2)

/-- The processes that the detection algorithm lets finish, in order. -/
def finished (work : R → ℕ) (pending : List P) : List P :=
  (S.reduceAux pending.length work pending).1

/-- **The detection algorithm**: the processes reported as deadlocked. -/
def detect (work : R → ℕ) (pending : List P) : List P :=
  (S.reduceAux pending.length work pending).2

variable {S}

theorem reduceAux_perm (fuel : ℕ) (work : R → ℕ) (pending : List P) :
    ((S.reduceAux fuel work pending).1 ++ (S.reduceAux fuel work pending).2).Perm pending := by
  induction fuel generalizing work pending with
  | zero => simp [reduceAux]
  | succ fuel ih =>
    rw [reduceAux]
    split
    next => simp
    next p hsome =>
      have hp := List.mem_of_find?_eq_some hsome
      exact ((ih _ _).cons p).trans (List.perm_cons_erase hp).symm

theorem reduceAux_reduces (fuel : ℕ) (work : R → ℕ) (pending : List P) :
    S.Reduces work (S.reduceAux fuel work pending).1 := by
  induction fuel generalizing work pending with
  | zero => trivial
  | succ fuel ih =>
    rw [reduceAux]
    split
    next => trivial
    next p hsome => exact ⟨by simpa using List.find?_some hsome, ih _ _⟩

theorem reduceAux_stuck (fuel : ℕ) (work : R → ℕ) (pending : List P)
    (hlen : pending.length ≤ fuel) :
    ∀ q ∈ (S.reduceAux fuel work pending).2,
      ¬ S.request q ≤ work + ((S.reduceAux fuel work pending).1.map S.alloc).sum := by
  induction fuel generalizing work pending with
  | zero =>
      intro q hq
      simp [reduceAux, List.length_eq_zero_iff.mp (Nat.le_zero.mp hlen)] at hq
  | succ fuel ih =>
    rw [reduceAux]
    split
    next hnone =>
      rw [List.find?_eq_none] at hnone
      intro q hq
      simpa using hnone q hq
    next p hsome =>
      have hp := List.mem_of_find?_eq_some hsome
      intro q hq
      have hlen' : (pending.erase p).length ≤ fuel := by
        rw [List.length_erase_of_mem hp]
        omega
      simpa [add_assoc] using ih (work + S.alloc p) (pending.erase p) hlen' q hq

/-- No process of a duplicate-free reduction sequence drawn from the pending
processes is left over by the algorithm. -/
theorem reduceAux_disjoint (fuel : ℕ) (work : R → ℕ) (pending : List P)
    (hlen : pending.length ≤ fuel) (hnd : pending.Nodup) {σ : List P}
    (hσ : S.Reduces work σ) (hσnd : σ.Nodup) (hsub : σ ⊆ pending) :
    ∀ x ∈ σ, x ∉ (S.reduceAux fuel work pending).2 := by
  induction fuel generalizing work pending σ with
  | zero =>
      intro x hx
      simp [reduceAux, List.length_eq_zero_iff.mp (Nat.le_zero.mp hlen)]
  | succ fuel ih =>
    rw [reduceAux]
    split
    next hnone =>
      rw [List.find?_eq_none] at hnone
      have : σ = [] := hσ.eq_nil fun q hq => by simpa using hnone q (hsub hq)
      subst this
      simp
    next p hsome =>
      have hp := List.mem_of_find?_eq_some hsome
      have hfit : S.request p ≤ work := by simpa using List.find?_some hsome
      intro x hx hrem
      have hlen' : (pending.erase p).length ≤ fuel := by
        rw [List.length_erase_of_mem hp]
        omega
      have hxp : x ≠ p := by
        rintro rfl
        have hperm := reduceAux_perm (S := S) fuel (work + S.alloc x) (pending.erase x)
        have hmem := hperm.subset (List.mem_append_right _ hrem)
        exact (List.Nodup.not_mem_erase hnd) hmem
      refine ih (work + S.alloc p) (pending.erase p) hlen' (hnd.erase p) (hσ.erase hfit)
        (hσnd.erase p) ?_ x ((List.Nodup.mem_erase_iff hσnd).2 ⟨hxp, hx⟩) hrem
      intro y hy
      have hyp : y ≠ p := fun h => (List.Nodup.not_mem_erase hσnd) (h ▸ hy)
      exact (List.Nodup.mem_erase_iff hnd).2 ⟨hyp, hsub (List.mem_of_mem_erase hy)⟩

/-- **Every reported process is stuck**: it requests more than is free even
after all the processes that the algorithm lets finish have released their
allocations. -/
theorem detect_stuck (work : R → ℕ) (pending : List P) :
    ∀ q ∈ S.detect work pending,
      ¬ S.request q ≤ work + ((S.finished work pending).map S.alloc).sum :=
  reduceAux_stuck _ work pending le_rfl

/-- The processes that the algorithm lets finish do finish, in that order. -/
theorem finished_reduces (work : R → ℕ) (pending : List P) :
    S.Reduces work (S.finished work pending) :=
  reduceAux_reduces _ work pending

theorem finished_append_detect_perm (work : R → ℕ) (pending : List P) :
    (S.finished work pending ++ S.detect work pending).Perm pending :=
  reduceAux_perm _ work pending

/-- **Correctness of deadlock detection**: a pending process is reported
exactly when no reduction sequence of pending processes finishes it. -/
theorem mem_detect_iff {work : R → ℕ} {pending : List P} (hnd : pending.Nodup) {p : P} :
    p ∈ S.detect work pending ↔
      p ∈ pending ∧ ¬ ∃ σ, S.Reduces work σ ∧ σ.Nodup ∧ σ ⊆ pending ∧ p ∈ σ := by
  have hperm := finished_append_detect_perm (S := S) work pending
  constructor
  · intro hp
    refine ⟨hperm.subset (List.mem_append_right _ hp), ?_⟩
    rintro ⟨σ, hσ, hσnd, hsub, hpσ⟩
    exact reduceAux_disjoint _ work pending le_rfl hnd hσ hσnd hsub p hpσ hp
  · rintro ⟨hp, hno⟩
    have hp' := hperm.symm.subset hp
    rcases List.mem_append.mp hp' with hfin | hdet
    · exact absurd ⟨_, finished_reduces work pending,
        (hperm.nodup_iff.mpr hnd).sublist (List.sublist_append_left _ _),
        fun x hx => hperm.subset (List.mem_append_left _ hx), hfin⟩ hno
    · exact hdet

/-- **No deadlock is reported exactly when all the processes can finish** in
some order. -/
theorem detect_eq_nil_iff {work : R → ℕ} {pending : List P} (hnd : pending.Nodup) :
    S.detect work pending = [] ↔ ∃ σ, σ.Perm pending ∧ S.Reduces work σ := by
  have hperm := finished_append_detect_perm (S := S) work pending
  constructor
  · intro h
    rw [h, List.append_nil] at hperm
    exact ⟨_, hperm, finished_reduces work pending⟩
  · rintro ⟨σ, hσperm, hσ⟩
    rw [List.eq_nil_iff_forall_not_mem]
    intro p hp
    exact ((mem_detect_iff hnd).1 hp).2
      ⟨σ, hσ, hσperm.nodup_iff.mpr hnd, hσperm.subset, hσperm.symm.subset
        (hperm.subset (List.mem_append_right _ hp))⟩

end State

end Cslib.Algorithms.Concurrency.DeadlockDetection
