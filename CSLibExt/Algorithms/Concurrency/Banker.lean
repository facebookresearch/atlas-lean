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

/-- `SafeSeq S work σ`: starting with `work` free, each process of `σ` in turn
can be given its remaining need, finish, and release its allocation. -/
def SafeSeq : (R → ℕ) → List P → Prop
  | _, [] => True
  | work, p :: rest => S.need p ≤ work ∧ SafeSeq (work + S.alloc p) rest

@[simp] theorem safeSeq_nil (work : R → ℕ) : S.SafeSeq work [] := trivial

@[simp] theorem safeSeq_cons (work : R → ℕ) (p : P) (rest : List P) :
    S.SafeSeq work (p :: rest) ↔ S.need p ≤ work ∧ S.SafeSeq (work + S.alloc p) rest :=
  Iff.rfl

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

/-- Letting a member of a safe sequence finish first leaves the rest of the
sequence safe. This is why the greedy safety check is complete. -/
theorem SafeSeq.erase {work : R → ℕ} {σ : List P} {p : P} (h : S.SafeSeq work σ)
    (hp : p ∈ σ) : S.SafeSeq (work + S.alloc p) (σ.erase p) := by
  induction σ generalizing work with
  | nil => simp at hp
  | cons q rest ih =>
      by_cases hqp : q = p
      · subst hqp
        simpa using h.2
      · rw [List.erase_cons_tail (by simpa using hqp)]
        refine ⟨h.1.trans fun r => Nat.le_add_right _ _, ?_⟩
        have hp' : p ∈ rest := (List.mem_cons.mp hp).resolve_left (Ne.symm hqp)
        have := ih h.2 hp'
        rwa [add_right_comm] at this

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

/-- The banker's safety algorithm with explicit fuel: let some pending process
whose remaining need fits in the free resources finish, release its
allocation, and repeat; succeed when no process is left. -/
def safetyCheckAux : ℕ → (R → ℕ) → List P → Bool
  | 0, _, pending => pending.isEmpty
  | fuel + 1, work, pending =>
      match pending.find? (fun p => decide (S.need p ≤ work)) with
      | none => pending.isEmpty
      | some p => safetyCheckAux fuel (work + S.alloc p) (pending.erase p)

/-- The banker's safety algorithm: reject a pending list with repetitions,
then at most one round per pending process. -/
def safetyCheck (work : R → ℕ) (pending : List P) : Bool :=
  decide pending.Nodup && S.safetyCheckAux pending.length work pending

variable {S}

theorem safetyCheckAux_iff (fuel : ℕ) (work : R → ℕ) (pending : List P)
    (hlen : pending.length = fuel) (hnd : pending.Nodup) :
    S.safetyCheckAux fuel work pending = true ↔ S.Safe work pending := by
  induction fuel generalizing work pending with
  | zero =>
      rw [List.length_eq_zero_iff.mp hlen]
      simpa [safetyCheckAux] using safe_nil work
  | succ fuel ih =>
    rw [safetyCheckAux]
    split
    next hnone =>
      rw [List.find?_eq_none] at hnone
      constructor
      · intro hempty
        rw [List.isEmpty_iff.mp hempty]
        exact safe_nil work
      · intro hsafe
        by_contra hne
        rw [Bool.not_eq_true, List.isEmpty_eq_false_iff] at hne
        obtain ⟨p, hp, hfit⟩ := hsafe.exists_runnable hne
        exact hnone p hp (decide_eq_true hfit)
    next p hsome =>
      have hp := List.mem_of_find?_eq_some hsome
      have hfit : S.need p ≤ work := by simpa using List.find?_some hsome
      rw [safe_iff_safe_erase hnd hp hfit]
      refine ih _ _ ?_ (hnd.erase p)
      rw [List.length_erase_of_mem hp, hlen]
      rfl

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

end System

end Cslib.Algorithms.Concurrency.Banker
