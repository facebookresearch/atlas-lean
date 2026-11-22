/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# The banker's algorithm
-/
module

public import CSLibExt.Algorithms.Concurrency.DeadlockDetection
public import Mathlib.Data.Fintype.Pi
public import Mathlib.Algebra.Order.Pi
public import Mathlib.Data.List.Perm.Basic

/-!
# The banker's algorithm: safety

Dijkstra's banker's algorithm for deadlock avoidance (E. W. Dijkstra,
*Cooperating Sequential Processes*, EWD 123, 1965; *The mathematics behind the
Banker's Algorithm*, EWD 623, 1977), in the multi-resource form of
A. N. Habermann (*Prevention of system deadlocks*, CACM 12(7), 1969). Resource
vectors are functions `R → ℕ` on a finite set of resource types, ordered
componentwise.

Each process `p` has a maximum claim `claim p` and a current allocation
`alloc p`; its remaining need is `need p = claim p - alloc p` (truncated
subtraction, so an allocation above the claim counts as zero need; `request`
never grants beyond the claim). A list of
processes is a *safe sequence* from the vector `work` of free resources
(`SafeSeq`) if each process in turn can be given its whole remaining need from
what is free, after which it finishes and releases its allocation. A state is
*safe* for a list of pending processes (`Safe`) if the list has no repetitions
and some ordering of it is a safe sequence; a repeated process would release
its allocation twice, so `safetyCheck` rejects lists with repetitions.

* `safetyCheck` is the banker's greedy safety algorithm: repeatedly let any
  pending process whose need fits finish, and release its allocation.
  `safetyCheck_iff`: it succeeds exactly when the state is safe. Correctness
  of the greedy choice rests on `SafeSeq.erase`: letting a process that fits
  finish first never destroys a safe sequence.
* `Safe.exists_runnable`: a safe state with pending processes is not
  deadlocked; some pending process can run to completion.
* `request`: the resource-request algorithm. A request by a pending process
  (in a duplicate-free pending list) is granted exactly when it is within the
  process's remaining need and the free resources and the resulting state is
  safe (`request_eq_some_iff`); in particular granted states are safe
  (`request_safe`).
* For a duplicate-free pending list, safety is the complete reducibility of
  `DeadlockDetection.lean` with each process requesting its remaining need
  (`toDetectionState`, `safe_iff_detect_eq_nil`): safe sequences are reduction
  sequences (`safeSeq_iff_reduces`, which also holds for lists with
  repetitions), with equal fuel the safety loop succeeds exactly when the
  detection loop leaves no process (`safetyCheckAux_iff_reduceAux`), and the
  safety check succeeds exactly when the pending list has no repetitions and
  deadlock detection reports no process
  (`safetyCheck_eq_true_iff_detect_eq_nil`). Detection alone does not reject
  repeated processes: it lets each copy finish and credits its allocation
  each time. `SafeSeq.erase` and `safetyCheckAux_iff` are derived from the
  detection results.
-/

@[expose] public section

namespace Cslib.Algorithms.Concurrency.Banker

variable {P R : Type*}

/-- Maximum claims and current allocations of the processes. -/
@[ext]
structure System (P R : Type*) where
  /-- The maximum demand of each process. -/
  claim : P → R → ℕ
  /-- The resources currently allocated to each process. -/
  alloc : P → R → ℕ

namespace System

variable (S : System P R)

/-- The remaining need of a process (truncated subtraction). -/
def need (p : P) : R → ℕ := S.claim p - S.alloc p

/-- The banker's state as a deadlock-detection state: each process holds its
allocation and requests its remaining need. -/
def toDetectionState (S : System P R) : DeadlockDetection.State P R :=
  ⟨S.alloc, S.need⟩

@[simp] theorem toDetectionState_alloc (S : System P R) : S.toDetectionState.alloc = S.alloc :=
  rfl

@[simp] theorem toDetectionState_request (S : System P R) :
    S.toDetectionState.request = S.need :=
  rfl

/-- `SafeSeq S work σ`: starting with `work` free, each process of `σ` in turn
can be given its remaining need, finish, and release its allocation. -/
def SafeSeq : (R → ℕ) → List P → Prop
  | _, [] => True
  | work, p :: rest => S.need p ≤ work ∧ SafeSeq (work + S.alloc p) rest

@[simp] theorem safeSeq_nil (work : R → ℕ) : S.SafeSeq work [] := trivial

@[simp] theorem safeSeq_cons (work : R → ℕ) (p : P) (rest : List P) :
    S.SafeSeq work (p :: rest) ↔ S.need p ≤ work ∧ S.SafeSeq (work + S.alloc p) rest :=
  Iff.rfl

/-- A safe sequence is a deadlock-detection reduction sequence in which every
process requests its remaining need. -/
theorem safeSeq_iff_reduces (S : System P R) (work : R → ℕ) (σ : List P) :
    S.SafeSeq work σ ↔ S.toDetectionState.Reduces work σ := by
  induction σ generalizing work with
  | nil => simp
  | cons p rest ih => simp [ih]

/-- The pending processes, listed without repetition, can all finish in some
order from `work`. -/
def Safe (work : R → ℕ) (pending : List P) : Prop :=
  pending.Nodup ∧ ∃ σ, σ.Perm pending ∧ S.SafeSeq work σ

variable {S}

/-- More free resources keep a sequence safe. -/
theorem SafeSeq.mono {work work' : R → ℕ} (hle : work ≤ work') {σ : List P}
    (h : S.SafeSeq work σ) : S.SafeSeq work' σ := by
  induction σ generalizing work work' with
  | nil => trivial
  | cons p rest ih =>
      exact ⟨h.1.trans hle, ih (fun r => Nat.add_le_add_right (hle r) _) h.2⟩

variable [DecidableEq P]

/-- Crediting a member's allocation in advance preserves the safe sequence
with one occurrence of that process removed. -/
theorem SafeSeq.erase {work : R → ℕ} {σ : List P} {p : P} (h : S.SafeSeq work σ)
    (hp : p ∈ σ) : S.SafeSeq (work + S.alloc p) (σ.erase p) := by
  rw [safeSeq_iff_reduces] at h ⊢
  exact h.erase_of_mem hp

omit [DecidableEq P] in
theorem safe_nil (work : R → ℕ) : S.Safe work [] :=
  ⟨List.nodup_nil, [], List.Perm.refl _, trivial⟩

omit [DecidableEq P] in
/-- A safe state with pending processes is not deadlocked: some pending process
can be given its whole remaining need. -/
theorem Safe.exists_runnable {work : R → ℕ} {pending : List P} (h : S.Safe work pending)
    (hne : pending ≠ []) : ∃ p ∈ pending, S.need p ≤ work := by
  obtain ⟨-, σ, hperm, hsafe⟩ := h
  cases σ with
  | nil => exact absurd (List.Perm.nil_eq hperm).symm hne
  | cons p rest => exact ⟨p, hperm.subset (List.mem_cons_self ..), hsafe.1⟩

/-- Once a pending process that fits has finished, safety of the remaining
processes is equivalent to safety of all of them. -/
theorem safe_iff_safe_erase {work : R → ℕ} {pending : List P} {p : P} (hnd : pending.Nodup)
    (hp : p ∈ pending) (hfit : S.need p ≤ work) :
    S.Safe work pending ↔ S.Safe (work + S.alloc p) (pending.erase p) := by
  constructor
  · rintro ⟨-, σ, hperm, hsafe⟩
    exact ⟨hnd.erase p, σ.erase p, hperm.erase p, hsafe.erase (hperm.mem_iff.mpr hp)⟩
  · rintro ⟨-, σ, hperm, hsafe⟩
    exact ⟨hnd, p :: σ, ((hperm.cons p).trans (List.perm_cons_erase hp).symm), hfit, hsafe⟩

variable (S) [Fintype R]

/-- A state is safe exactly when the pending list has no repetitions and the
deadlock-detection algorithm, run with the remaining needs as requests, reports
no process. -/
theorem safe_iff_detect_eq_nil (S : System P R) (work : R → ℕ) (pending : List P) :
    S.Safe work pending ↔ pending.Nodup ∧ S.toDetectionState.detect work pending = [] := by
  constructor
  · rintro ⟨hnd, σ, hperm, hsafe⟩
    exact ⟨hnd, (DeadlockDetection.State.detect_eq_nil_iff hnd).mpr
      ⟨σ, hperm, (S.safeSeq_iff_reduces work σ).mp hsafe⟩⟩
  · rintro ⟨hnd, hnil⟩
    obtain ⟨σ, hperm, hred⟩ := (DeadlockDetection.State.detect_eq_nil_iff hnd).mp hnil
    exact ⟨hnd, σ, hperm, (S.safeSeq_iff_reduces work σ).mpr hred⟩

/-- The banker's safety algorithm with explicit fuel: let some pending process
whose remaining need fits in the free resources finish, release its
allocation, and repeat; succeed when no process is left. -/
def safetyCheckAux : ℕ → (R → ℕ) → List P → Bool
  | 0, _, pending => pending.isEmpty
  | fuel + 1, work, pending =>
      match pending.find? (fun p => decide (S.need p ≤ work)) with
      | none => pending.isEmpty
      | some p => safetyCheckAux fuel (work + S.alloc p) (pending.erase p)

/-- With the same fuel, the safety loop succeeds exactly when the detection
loop leaves no processes. No duplicate-free assumption is needed for the loops. -/
theorem safetyCheckAux_iff_reduceAux (fuel : ℕ) (work : R → ℕ) (pending : List P) :
    S.safetyCheckAux fuel work pending = true ↔
      (S.toDetectionState.reduceAux fuel work pending).2 = [] := by
  induction fuel generalizing work pending with
  | zero => simp [safetyCheckAux, DeadlockDetection.State.reduceAux]
  | succ fuel ih =>
      rw [safetyCheckAux, DeadlockDetection.State.reduceAux]
      change
        (match pending.find? (fun p => decide (S.need p ≤ work)) with
          | none => pending.isEmpty
          | some p => S.safetyCheckAux fuel (work + S.alloc p) (pending.erase p)) = true ↔
        (match pending.find? (fun p => decide (S.need p ≤ work)) with
          | none => ([], pending)
          | some p =>
              let r := S.toDetectionState.reduceAux fuel (work + S.alloc p) (pending.erase p)
              (p :: r.1, r.2)).2 = []
      cases hfind : pending.find? (fun p => decide (S.need p ≤ work)) with
      | none => simp
      | some p => exact ih (work + S.alloc p) (pending.erase p)

/-- The banker's safety algorithm: reject a pending list with repetitions,
then at most one round per pending process. -/
def safetyCheck (work : R → ℕ) (pending : List P) : Bool :=
  decide pending.Nodup && S.safetyCheckAux pending.length work pending

variable {S}

theorem safetyCheckAux_iff (fuel : ℕ) (work : R → ℕ) (pending : List P)
    (hlen : pending.length = fuel) (hnd : pending.Nodup) :
    S.safetyCheckAux fuel work pending = true ↔ S.Safe work pending := by
  rw [safetyCheckAux_iff_reduceAux, ← hlen]
  change S.toDetectionState.detect work pending = [] ↔ S.Safe work pending
  rw [safe_iff_detect_eq_nil]
  simp only [hnd, true_and]

/-- **Correctness of the safety algorithm**: it succeeds exactly on safe
states. -/
theorem safetyCheck_iff (work : R → ℕ) (pending : List P) :
    S.safetyCheck work pending = true ↔ S.Safe work pending := by
  by_cases hnd : pending.Nodup
  · simp only [safetyCheck, hnd, decide_true, Bool.true_and]
    exact safetyCheckAux_iff _ work pending rfl hnd
  · simp only [safetyCheck, hnd, decide_false, Bool.false_and, Bool.false_eq_true, false_iff]
    exact fun h => hnd h.1

/-! ## Requests -/

/-- The system after granting `req` to `p`. -/
def grant (S : System P R) (p : P) (req : R → ℕ) : System P R :=
  ⟨S.claim, Function.update S.alloc p (S.alloc p + req)⟩

omit [Fintype R] in
@[simp] theorem grant_claim (S : System P R) (p : P) (req : R → ℕ) :
    (S.grant p req).claim = S.claim := rfl

omit [Fintype R] in
@[simp] theorem grant_alloc_self (S : System P R) (p : P) (req : R → ℕ) :
    (S.grant p req).alloc p = S.alloc p + req := by simp [grant]

omit [Fintype R] in
theorem grant_alloc_of_ne (S : System P R) {p q : P} (h : q ≠ p) (req : R → ℕ) :
    (S.grant p req).alloc q = S.alloc q := by simp [grant, h]

omit [Fintype R] in
/-- Granting `req` lowers the remaining need by `req`. -/
@[simp] theorem need_grant_self (S : System P R) (p : P) (req : R → ℕ) :
    (S.grant p req).need p = S.need p - req := by
  funext r
  simp [need, Nat.sub_sub]

/-- The resource-request algorithm: process `p` asks for `req` more resources
out of `available`. The request is granted, returning the new free vector and
system, when `p` is pending (in a duplicate-free list), the request is within
`p`'s remaining need and the free resources, and the resulting state is safe.
`none` covers the error case of the textbook algorithm (a request beyond the
remaining claim), the cases where the process must wait, and malformed input (a
requester that is not pending, or a pending list with repetitions). -/
def request (S : System P R) (available : R → ℕ) (pending : List P) (p : P)
    (req : R → ℕ) : Option ((R → ℕ) × System P R) :=
  if p ∈ pending ∧ pending.Nodup ∧ req ≤ S.need p ∧ req ≤ available ∧
      (S.grant p req).safetyCheck (available - req) pending
  then some (available - req, S.grant p req)
  else none

/-- **The request algorithm grants exactly the safe requests within the claim
and the free resources.** -/
theorem request_eq_some_iff {available : R → ℕ} {pending : List P} {p : P} {req : R → ℕ}
    {available' : R → ℕ} {S' : System P R} :
    request S available pending p req = some (available', S') ↔
      p ∈ pending ∧ pending.Nodup ∧ req ≤ S.need p ∧ req ≤ available ∧
        (S.grant p req).Safe (available - req) pending ∧
        available' = available - req ∧ S' = S.grant p req := by
  unfold request
  split
  next hgrant =>
    simp only [Option.some.injEq, Prod.mk.injEq]
    obtain ⟨hp, hnd, hneed, havail, hcheck⟩ := hgrant
    constructor
    · rintro ⟨rfl, rfl⟩
      exact ⟨hp, hnd, hneed, havail, (safetyCheck_iff _ _).mp hcheck, rfl, rfl⟩
    · rintro ⟨-, -, -, -, -, rfl, rfl⟩
      exact ⟨rfl, rfl⟩
  next hrefuse =>
    simp only [reduceCtorEq, false_iff]
    rintro ⟨hp, hnd, hneed, havail, hsafe, -, -⟩
    exact hrefuse ⟨hp, hnd, hneed, havail, (safetyCheck_iff _ _).mpr hsafe⟩

/-- Granted requests lead to safe states. -/
theorem request_safe {available : R → ℕ} {pending : List P} {p : P} {req : R → ℕ}
    {available' : R → ℕ} {S' : System P R}
    (h : request S available pending p req = some (available', S')) :
    S'.Safe available' pending := by
  obtain ⟨-, -, -, -, hsafe, rfl, rfl⟩ := request_eq_some_iff.mp h
  exact hsafe

/-! ## Safety as deadlock-detection reducibility -/

/-- The banker's safety check succeeds exactly when the pending list has no
repetitions and deadlock detection with the remaining needs as requests reports
no process. -/
theorem safetyCheck_eq_true_iff_detect_eq_nil (S : System P R) (work : R → ℕ)
    (pending : List P) :
    S.safetyCheck work pending = true ↔
      pending.Nodup ∧ S.toDetectionState.detect work pending = [] :=
  (safetyCheck_iff work pending).trans (S.safe_iff_detect_eq_nil work pending)

end System

end Cslib.Algorithms.Concurrency.Banker
