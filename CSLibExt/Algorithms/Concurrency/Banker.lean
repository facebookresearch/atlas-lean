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

/-- **Claims and allocations of processes.** A system with processes $P$ and resource types
$R$ consists of two maps $\mathrm{claim}, \mathrm{alloc} : P \to (R \to \mathbb{N})$, where
$\mathrm{claim}(p)$ is the maximum demand of process $p$ for each resource type and
$\mathrm{alloc}(p)$ is the amount of each resource type currently allocated to $p$. No
inequality between the two is required. -/
@[ext]
structure System (P R : Type*) where
  /-- The maximum demand of each process. -/
  claim : P → R → ℕ
  /-- The resources currently allocated to each process. -/
  alloc : P → R → ℕ

namespace System

variable (S : System P R)

/-- **Remaining need.** The remaining need of a process $p$ in a system $S$ is the resource
vector $\mathrm{claim}(p) - \mathrm{alloc}(p)$: the maximum claim of $p$ minus its current
allocation, computed for each resource type by truncated subtraction of natural numbers, so it
is $0$ for every resource type where the allocation exceeds the claim. -/
def need (p : P) : R → ℕ := S.claim p - S.alloc p

/-- **Safe sequence.** Let $S$ be a system with processes $P$ and resource types $R$, where
process $p$ has maximum claim $\mathrm{claim}(p)$ and allocation $\mathrm{alloc}(p)$ in
$R \to \mathbb{N}$. A list $p_1, \dots, p_k$ of processes is a safe sequence from the free
resource vector $w : R \to \mathbb{N}$ when, for each $i$, the remaining need
$\mathrm{claim}(p_i) - \mathrm{alloc}(p_i)$ (truncated at zero) is at most
$w + \mathrm{alloc}(p_1) + \cdots + \mathrm{alloc}(p_{i-1})$ componentwise. In particular
the empty list is a safe sequence from every $w$.

Thus each process in turn can be given its remaining need from what is free, finish, and
release its allocation. -/
def SafeSeq : (R → ℕ) → List P → Prop
  | _, [] => True
  | work, p :: rest => S.need p ≤ work ∧ SafeSeq (work + S.alloc p) rest

@[simp] theorem safeSeq_nil (work : R → ℕ) : S.SafeSeq work [] := trivial

@[simp] theorem safeSeq_cons (work : R → ℕ) (p : P) (rest : List P) :
    S.SafeSeq work (p :: rest) ↔ S.need p ≤ work ∧ S.SafeSeq (work + S.alloc p) rest :=
  Iff.rfl

/-- **Safe state.** Let $S$ be a system of claims and allocations with processes $P$ and
resource types $R$. A list of pending processes is safe from the free resource vector
$w : R \to \mathbb{N}$ when it has no repetitions and some permutation of it is a safe sequence
from $w$: the pending processes can all finish, one after another, in some order. -/
def Safe (work : R → ℕ) (pending : List P) : Prop :=
  pending.Nodup ∧ ∃ σ, σ.Perm pending ∧ S.SafeSeq work σ

variable {S}

/-- **Safe sequences are monotone in the free resources.** Let $S$ be a system of processes with
maximum claims and current allocations, and let $\sigma$ be a list of processes. If $\sigma$ is a
safe sequence for $S$ from a vector $w$ of free resources (a natural number for each resource
type), and $w \le w'$ componentwise, then $\sigma$ is also a safe sequence for $S$ from $w'$. -/
theorem SafeSeq.mono {work work' : R → ℕ} (hle : work ≤ work') {σ : List P}
    (h : S.SafeSeq work σ) : S.SafeSeq work' σ := by
  induction σ generalizing work work' with
  | nil => trivial
  | cons p rest ih =>
      exact ⟨h.1.trans hle, ih (fun r => Nat.add_le_add_right (hle r) _) h.2⟩

variable [DecidableEq P]

/-- **Removing a process from a safe sequence.** Let $S$ be a system of processes with maximum
claims and current allocations, let $w$ be a vector of free resources (a natural number for
each resource type), and let $\sigma$ be a list of processes that is a safe sequence for $S$
from $w$. If $p$ occurs in $\sigma$, then the list obtained from $\sigma$ by deleting the first
occurrence of $p$ is a safe sequence for $S$ from $w + \mathrm{alloc}(p)$, where
$\mathrm{alloc}(p)$ is the current allocation of $p$ and the sum is taken componentwise.

In other words, letting a member of a safe sequence finish first and release its allocation
leaves the rest of the sequence safe. This is why the greedy safety check is complete. -/
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
/-- **A safe state is not deadlocked.** Let $S$ be a system of processes with maximum claims and
current allocations, let $w$ be a vector of free resources (a natural number for each resource
type), and let $L$ be a nonempty list of pending processes. If $S$ is safe from $w$ for $L$, then
some process $p$ in $L$ has remaining need $\mathrm{need}(p) \le w$ componentwise, so it can be
given its whole remaining need. -/
theorem Safe.exists_runnable {work : R → ℕ} {pending : List P} (h : S.Safe work pending)
    (hne : pending ≠ []) : ∃ p ∈ pending, S.need p ≤ work := by
  obtain ⟨-, σ, hperm, hsafe⟩ := h
  cases σ with
  | nil => exact absurd (List.Perm.nil_eq hperm).symm hne
  | cons p rest => exact ⟨p, hperm.subset (List.mem_cons_self ..), hsafe.1⟩

/-- **Letting a process that fits finish preserves safety.** Let $S$ be a system of processes
with maximum claims and current allocations, $w$ a vector of free resources (a natural number
for each resource type) and $L$ a list of pending processes without repetitions. If $p$ occurs in
$L$ and its remaining need $\mathrm{need}(p)$ in $S$ satisfies $\mathrm{need}(p) \le w$
componentwise, then $S$ is safe from $w$ for $L$ if and only if $S$ is safe from
$w + \mathrm{alloc}(p)$ for the list obtained from $L$ by removing $p$, where
$\mathrm{alloc}(p)$ is the current allocation of $p$ and the sum is taken componentwise. -/
theorem safe_iff_safe_erase {work : R → ℕ} {pending : List P} {p : P} (hnd : pending.Nodup)
    (hp : p ∈ pending) (hfit : S.need p ≤ work) :
    S.Safe work pending ↔ S.Safe (work + S.alloc p) (pending.erase p) := by
  constructor
  · rintro ⟨-, σ, hperm, hsafe⟩
    exact ⟨hnd.erase p, σ.erase p, hperm.erase p, hsafe.erase (hperm.mem_iff.mpr hp)⟩
  · rintro ⟨-, σ, hperm, hsafe⟩
    exact ⟨hnd, p :: σ, ((hperm.cons p).trans (List.perm_cons_erase hp).symm), hfit, hsafe⟩

variable (S) [Fintype R]

/-- **Banker's safety algorithm with fuel.** Let $S$ be a system with processes $P$ and a
finite set $R$ of resource types, where process $p$ has maximum claim $\mathrm{claim}(p)$ and
allocation $\mathrm{alloc}(p)$ in $R \to \mathbb{N}$. Given a fuel $n \in \mathbb{N}$, a free
resource vector $w : R \to \mathbb{N}$ and a list of pending processes, the algorithm succeeds
if the list is empty. Otherwise, if $n > 0$ and some pending process $q$ has remaining need
$\mathrm{claim}(q) - \mathrm{alloc}(q)$ (truncated at zero) at most $w$ componentwise, it takes
the first such process $p$ in the list, removes that occurrence of $p$ from the list, adds
$\mathrm{alloc}(p)$ to $w$ and continues with fuel $n - 1$; if $n = 0$ or no pending process
fits, it fails. -/
def safetyCheckAux : ℕ → (R → ℕ) → List P → Bool
  | 0, _, pending => pending.isEmpty
  | fuel + 1, work, pending =>
      match pending.find? (fun p => decide (S.need p ≤ work)) with
      | none => pending.isEmpty
      | some p => safetyCheckAux fuel (work + S.alloc p) (pending.erase p)

/-- **Banker's safety algorithm.** Let $S$ be a system of claims and allocations with processes
$P$ and a finite set $R$ of resource types. Given a free resource vector $w : R \to \mathbb{N}$
and a list of pending processes, the algorithm fails if the list has a repetition. Otherwise it
runs the safety algorithm with fuel equal to the length of the list: it repeatedly lets the
first pending process whose remaining need (claim minus allocation, truncated at zero) is at
most the free resources componentwise finish and adds its allocation to the free resources,
for at most one round per pending process, and it succeeds exactly when no pending process is
left at the end. -/
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

/-- **Correctness of the safety algorithm.** For every system $S$ of claims and allocations over
a finite set $R$ of resource types, every free resource vector $w : R \to \mathbb{N}$ and every
list of pending processes, the banker's safety algorithm succeeds on $w$ and the list if and
only if the list is a safe state from $w$. -/
theorem safetyCheck_iff (work : R → ℕ) (pending : List P) :
    S.safetyCheck work pending = true ↔ S.Safe work pending := by
  by_cases hnd : pending.Nodup
  · simp only [safetyCheck, hnd, decide_true, Bool.true_and]
    exact safetyCheckAux_iff _ work pending rfl hnd
  · simp only [safetyCheck, hnd, decide_false, Bool.false_and, Bool.false_eq_true, false_iff]
    exact fun h => hnd h.1

/-! ## Requests -/

/-- **Granting a request.** For a system $S$ of processes with maximum claims and current
allocations, a process $p$ and a resource vector $r$ (a natural number for each resource type),
the system obtained by granting $r$ to $p$ has the same maximum claims as $S$, gives $p$ the
allocation $\mathrm{alloc}(p) + r$ (componentwise sum, where $\mathrm{alloc}(p)$ is the current
allocation of $p$ in $S$), and leaves the allocation of every other process unchanged. -/
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
/-- **Remaining need after a grant.** For a system $S$ of processes with maximum claims and
current allocations, a process $p$ and a resource vector $r$ (a natural number for each resource
type), the remaining need of $p$ in the system obtained by granting $r$ to $p$ equals
$\mathrm{need}(p) - r$, where $\mathrm{need}(p)$ is the remaining need of $p$ in $S$ and the
subtraction is truncated subtraction of natural numbers, taken componentwise. -/
@[simp] theorem need_grant_self (S : System P R) (p : P) (req : R → ℕ) :
    (S.grant p req).need p = S.need p - req := by
  funext r
  simp [need, Nat.sub_sub]

/-- **Resource-request algorithm.** Let $S$ be a system of claims and allocations with processes
$P$ and a finite set $R$ of resource types, let $a : R \to \mathbb{N}$ be the vector of free
resources, $L$ a list of pending processes, $p$ a process and $r : R \to \mathbb{N}$ the
resources that $p$ requests. The request is granted when $p$ occurs in $L$, $L$ has no
repetitions, $r \le \mathrm{need}(p)$ and $r \le a$ componentwise, where $\mathrm{need}(p)$ is
the remaining need of $p$ in $S$, and the banker's safety algorithm succeeds for the system
obtained from $S$ by granting $r$ to $p$, from the free vector $a - r$ (componentwise truncated
subtraction) and the list $L$. A granted request returns the free vector $a - r$ and that
system; otherwise the algorithm returns no result.

No result covers the error case of the textbook algorithm (a request beyond the remaining
claim), the cases where the process must wait, and malformed input (a requester that is not
pending, or a pending list with repetitions). -/
def request (S : System P R) (available : R → ℕ) (pending : List P) (p : P)
    (req : R → ℕ) : Option ((R → ℕ) × System P R) :=
  if p ∈ pending ∧ pending.Nodup ∧ req ≤ S.need p ∧ req ≤ available ∧
      (S.grant p req).safetyCheck (available - req) pending
  then some (available - req, S.grant p req)
  else none

/-- **The request algorithm grants exactly the safe requests within the claim
and the free resources.** Let $S$ be a system of claims and allocations with processes $P$ and a
finite set $R$ of resource types, let $a : R \to \mathbb{N}$ be the vector of free resources, $L$
a list of pending processes, $p$ a process and $r : R \to \mathbb{N}$ the resources that $p$
requests. Write $\mathrm{need}(p)$ for the remaining need of $p$ in $S$, $T$ for the system
obtained from $S$ by granting $r$ to $p$, and $a - r$ for componentwise truncated subtraction.
The resource-request algorithm grants the request and returns the free vector $a'$ and the
system $S'$ if and only if $p$ occurs in $L$, $L$ has no repetitions, both
$r \le \mathrm{need}(p)$ and $r \le a$ hold componentwise, $T$ is safe from $a - r$ for $L$,
$a' = a - r$, and $S' = T$. -/
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

/-- **Granted requests lead to safe states.** Let $S$ be a system of processes with maximum
claims and current allocations, $a$ the vector of free resources, $L$ the list of pending
processes, $p$ a process and $r$ a resource vector. If the resource-request algorithm grants the
request of $r$ by $p$, returning the free vector $a'$ and the system $S'$, then $S'$ is safe from
$a'$ for $L$. -/
theorem request_safe {available : R → ℕ} {pending : List P} {p : P} {req : R → ℕ}
    {available' : R → ℕ} {S' : System P R}
    (h : request S available pending p req = some (available', S')) :
    S'.Safe available' pending := by
  obtain ⟨-, -, -, -, hsafe, rfl, rfl⟩ := request_eq_some_iff.mp h
  exact hsafe

end System

end Cslib.Algorithms.Concurrency.Banker
