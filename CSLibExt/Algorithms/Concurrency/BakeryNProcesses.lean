/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Cslib.Foundations.Semantics.LTS.Basic
public import Mathlib.Data.Fintype.Basic
public import Mathlib.Logic.Function.Basic
public import Mathlib.Order.Fin.Basic

/-!
# Lamport's bakery algorithm for `N` processes: mutual exclusion

The mutual exclusion algorithm of L. Lamport, *A New Solution of Dijkstra's Concurrent
Programming Problem*, Comm. ACM 17(8), 1974, 453–455, as a CSLib labelled transition system
(`Cslib.LTS`) whose label is the process taking the step, and a proof that no two processes are
ever in their critical sections at the same time (`mutual_exclusion`).

**Model.**

* *Processes and memory:* `N` processes `0, …, N - 1` (Lamport's `1, …, N`) share the arrays
  `choosing` and `number`; process `i` writes only `choosing[i]` and `number[i]` and reads the
  entries of the others.
* *Synchrony:* none. Steps of different processes interleave in any order, with no assumption
  on relative speeds and no fairness (only safety is proved).
* *Atomicity:* each step performs one read or one write of one shared entry (atomic registers).
  This is **weaker than Lamport's result**, which allows a read overlapping a write to return an
  arbitrary value (safe registers). The maximum is computed by reading the entries one at a
  time, in any order, as the paper allows.
* *Failures:* a process may fail at any point; it then returns to its noncritical section with
  `choosing[i] = 0` and `number[i] = 0` in one atomic step. Lamport also allows a period during
  which reads of a failed processor's memory return arbitrary values; that is not modelled.
* *Messages:* none; communication is through shared memory only.

**Program of process `i`** (Lamport's labels in brackets; the busy-waiting re-reads that leave
the state unchanged are omitted, as they cannot affect safety):

* `ncs` → `doorway univ 0`: set `choosing[i] := 1` [L1];
* `doorway U m`: read `number[k]` for some unread `k ∈ U`, keeping the running maximum `m`;
  when all are read, go to `write m`;
* `write m`: set `number[i] := 1 + m`;
* `exit`: set `choosing[i] := 0`, then run the loop from index `0`;
* `l2 j` with `j < N`: proceed when `choosing[j] = 0` [L2];
* `l3 j`: proceed to `l2 (j + 1)` unless `number[j] ≠ 0` and `(number[j], j) < (number[i], i)`
  [L3];
* `l2 N`: enter the critical section `cs`; leaving it sets `number[i] := 0`.

The proof follows Lamport's Assertion 2: a process in its critical section has a smaller
`(number, name)` pair than every other process holding a ticket.

## Relation to `CSLibExt.Algorithms.Concurrency.Bakery`

That module models two processes without failures and states mutual exclusion as the LTL
formula `□¬(cs0 ∧ cs1)` on infinite runs (`Bakery.bakery_mutex`). This module covers `N`
processes and crash-resets, states mutual exclusion for reachable states (`mutual_exclusion`)
and also proves Lamport's Assertion 2 (`before_of_cs`).
-/

@[expose] public section

namespace Cslib.Algorithms.Concurrency.BakeryNProcesses

variable {N : ℕ}

/-- **Lamport's order on (ticket, name) pairs**: `(n, i) < (m, k)` when `n < m`, or `n = m` and
`i < k` (Lamport 1974, p. 454). -/
def Before (n : ℕ) (i : Fin N) (m : ℕ) (k : Fin N) : Prop :=
  n < m ∨ (n = m ∧ i < k)

/-- **Program counter of a bakery process.** `doorway U m`: choosing, with the entries `U` still
to read and running maximum `m`; `write m`: about to write the ticket `1 + m`; `exit`: about to
reset `choosing`; `l2 j` and `l3 j`: at statements L2 and L3 of the loop, for index `j`. -/
inductive ProgramCounter (N : ℕ)
  | ncs
  | doorway (U : Finset (Fin N)) (m : ℕ)
  | write (m : ℕ)
  | exit
  | l2 (j : ℕ)
  | l3 (j : ℕ)
  | cs

/-- **State of the bakery algorithm**: program counters and the shared arrays. -/
structure State (N : ℕ) where
  /-- The program counter of each process. -/
  pc : Fin N → ProgramCounter N
  /-- The shared array `choosing` (`true` for Lamport's `1`). -/
  choosing : Fin N → Bool
  /-- The shared array `number`. -/
  number : Fin N → ℕ

/-- **Initial state of the bakery algorithm**: every process in its noncritical section, all
entries zero (Lamport 1974: execution begins in the noncritical section; the arrays are
initially zero). -/
def init : State N := ⟨fun _ => .ncs, fun _ => false, fun _ => 0⟩

/-- **One atomic action of process `p`** in state `s`: its new program counter and its new
values of `choosing[p]` and `number[p]`. -/
inductive LocalStep (s : State N) (p : Fin N) : ProgramCounter N → Bool → ℕ → Prop
  | enter : s.pc p = .ncs → LocalStep s p (.doorway Finset.univ 0) true (s.number p)
  | read (U : Finset (Fin N)) (m : ℕ) (k : Fin N) : s.pc p = .doorway U m → k ∈ U →
      LocalStep s p (.doorway (U.erase k) (max m (s.number k))) (s.choosing p) (s.number p)
  | endRead (m : ℕ) : s.pc p = .doorway ∅ m → LocalStep s p (.write m) (s.choosing p) (s.number p)
  | write (m : ℕ) : s.pc p = .write m → LocalStep s p .exit (s.choosing p) (m + 1)
  | exit : s.pc p = .exit → LocalStep s p (.l2 0) false (s.number p)
  | l2 (j : ℕ) (hj : j < N) : s.pc p = .l2 j → s.choosing ⟨j, hj⟩ = false →
      LocalStep s p (.l3 j) (s.choosing p) (s.number p)
  | l3 (j : ℕ) (hj : j < N) : s.pc p = .l3 j →
      ¬ (s.number ⟨j, hj⟩ ≠ 0 ∧ Before (s.number ⟨j, hj⟩) ⟨j, hj⟩ (s.number p) p) →
      LocalStep s p (.l2 (j + 1)) (s.choosing p) (s.number p)
  | enterCS : s.pc p = .l2 N → LocalStep s p .cs (s.choosing p) (s.number p)
  | leave : s.pc p = .cs → LocalStep s p .ncs (s.choosing p) 0
  | fail : LocalStep s p .ncs false 0

/-- **Update by one process**: the state after process `p` sets its program counter,
`choosing[p]` and `number[p]`. -/
def setLocal (s : State N) (p : Fin N) (c : ProgramCounter N) (b : Bool) (n : ℕ) : State N :=
  ⟨Function.update s.pc p c, Function.update s.choosing p b, Function.update s.number p n⟩

/-- **The bakery algorithm as a CSLib labelled transition system**; the label is the process
that takes the step. -/
def lts : Cslib.LTS (State N) (Fin N) :=
  ⟨fun s p s' => ∃ c b n, LocalStep s p c b n ∧ s' = setLocal s p c b n⟩

/-- **Holding a ticket**: the process has written `number[i]` and has not left its critical
section or failed. Lamport's "in the bakery" starts one step later, when `choosing[i]` is
reset. -/
def HasTicket : ProgramCounter N → Prop
  | .exit | .l2 _ | .l3 _ | .cs => True
  | _ => False

/-- **In the doorway**: the process has set `choosing[i]` and not yet reset it (Lamport 1974,
p. 454). -/
def InDoorway : ProgramCounter N → Prop
  | .doorway _ _ | .write _ | .exit => True
  | _ => False

/-- **Waiting or critical**: the process is in the loop L2–L3 or in its critical section. -/
def Waiting : ProgramCounter N → Prop
  | .l2 _ | .l3 _ | .cs => True
  | _ => False

/-- **Process `i` is ahead of process `k`**: `k` is in its noncritical section; or `k` is
choosing and either has still to read `number[i]` or its running maximum already bounds
`number[i]`; or `k` holds a ticket and `(number[i], i) < (number[k], k)`. For `k ≠ i`, whatever
`k` does next, it does not overtake `i` (`aheadOf_step_other`). For `k = i` a process's own step
can falsify it: from `write 0` with `number[i] = 0`, the write step moves to `exit` with
`number[i] = 1`, and `Before` is strict. -/
def AheadOf (s : State N) (i k : Fin N) : Prop :=
  match s.pc k with
  | .ncs => True
  | .doorway U m => i ∈ U ∨ s.number i ≤ m
  | .write m => s.number i ≤ m
  | _ => Before (s.number i) i (s.number k) k

/-- **The per-process invariant of the bakery algorithm.** -/
structure LocalInv (s : State N) (i : Fin N) : Prop where
  number_pos : 0 < s.number i ↔ HasTicket (s.pc i)
  choosing_eq : s.choosing i = true ↔ InDoorway (s.pc i)
  l2 : ∀ j, s.pc i = .l2 j → j ≤ N ∧ ∀ k : Fin N, k.val < j → k ≠ i → AheadOf s i k
  l3 : ∀ j, s.pc i = .l3 j → j < N ∧ (∀ k : Fin N, k.val < j → k ≠ i → AheadOf s i k) ∧
    ∀ k : Fin N, k.val = j → k ≠ i → AheadOf s i k ∨ Waiting (s.pc k)
  cs : s.pc i = .cs → ∀ k, k ≠ i → AheadOf s i k

theorem before_asymm {n m : ℕ} {i k : Fin N} (h : Before n i m k) : ¬ Before m k n i := by
  unfold Before at *
  omega

theorem before_of_not {n m : ℕ} {i k : Fin N} (hik : i ≠ k) (h : ¬ Before m k n i) :
    Before n i m k := by
  have := Fin.val_ne_of_ne hik
  unfold Before at *
  rw [Fin.lt_def] at *
  omega

theorem aheadOf_setLocal_of_ne {s : State N} {p i k : Fin N} {c : ProgramCounter N} {b : Bool}
    {n : ℕ}
    (hi : i ≠ p) (hk : k ≠ p) : AheadOf (setLocal s p c b n) i k ↔ AheadOf s i k := by
  simp only [AheadOf, setLocal, Function.update_of_ne hi, Function.update_of_ne hk]

theorem aheadOf_setLocal_self {s : State N} {i k : Fin N} {c : ProgramCounter N} {b : Bool}
    (hk : k ≠ i) : AheadOf (setLocal s i c b (s.number i)) i k ↔ AheadOf s i k := by
  simp only [AheadOf, setLocal, Function.update_of_ne hk, Function.update_eq_self]

theorem aheadOf_step_other {s : State N} {p i : Fin N} {c : ProgramCounter N} {b : Bool} {n : ℕ}
    (hi : i ≠ p) (h : LocalStep s p c b n) (hb : AheadOf s i p) :
    AheadOf (setLocal s p c b n) i p := by
  cases h with
  | enter hp => simp [AheadOf, setLocal]
  | read U m k hp hk =>
    simp only [AheadOf, hp] at hb
    simp only [AheadOf, setLocal, Function.update_self, Function.update_of_ne hi]
    rcases hb with hU | hle
    · by_cases hik : i = k
      · subst hik; exact Or.inr (le_max_right _ _)
      · exact Or.inl (Finset.mem_erase.mpr ⟨hik, hU⟩)
    · exact Or.inr (le_max_of_le_left hle)
  | endRead m hp =>
    simp only [AheadOf, hp] at hb
    simp only [AheadOf, setLocal, Function.update_self, Function.update_of_ne hi]
    simpa using hb
  | write m hp =>
    simp only [AheadOf, hp] at hb
    simp only [AheadOf, setLocal, Function.update_self, Function.update_of_ne hi]
    exact Or.inl (by omega)
  | exit hp =>
    simp only [AheadOf, hp] at hb
    simpa [AheadOf, setLocal, Function.update_of_ne hi] using hb
  | l2 j hj hp _ =>
    simp only [AheadOf, hp] at hb
    simpa [AheadOf, setLocal, Function.update_of_ne hi] using hb
  | l3 j hj hp _ =>
    simp only [AheadOf, hp] at hb
    simpa [AheadOf, setLocal, Function.update_of_ne hi] using hb
  | enterCS hp =>
    simp only [AheadOf, hp] at hb
    simpa [AheadOf, setLocal, Function.update_of_ne hi] using hb
  | leave hp => simp [AheadOf, setLocal]
  | fail => simp [AheadOf, setLocal]

theorem waiting_step_other {s : State N} {p i : Fin N} {c : ProgramCounter N} {b : Bool} {n : ℕ}
    (h : LocalStep s p c b n) (hw : Waiting (s.pc p)) :
    AheadOf (setLocal s p c b n) i p ∨ Waiting ((setLocal s p c b n).pc p) := by
  cases h with
  | enter hp => simp [hp, Waiting] at hw
  | read U m k hp hk => simp [hp, Waiting] at hw
  | endRead m hp => simp [hp, Waiting] at hw
  | write m hp => simp [hp, Waiting] at hw
  | exit hp => simp [hp, Waiting] at hw
  | l2 j hj hp _ => exact Or.inr (by simp [setLocal, Waiting])
  | l3 j hj hp _ => exact Or.inr (by simp [setLocal, Waiting])
  | enterCS hp => exact Or.inr (by simp [setLocal, Waiting])
  | leave hp => exact Or.inl (by simp [AheadOf, setLocal])
  | fail => exact Or.inl (by simp [AheadOf, setLocal])

/-- **A step of another process preserves the invariant of process `i`.** -/
theorem localInv_step_other {s : State N} {p i : Fin N} {c : ProgramCounter N} {b : Bool} {n : ℕ}
    (hi : i ≠ p) (h : LocalStep s p c b n) (hs : LocalInv s i) :
    LocalInv (setLocal s p c b n) i := by
  have hpc : (setLocal s p c b n).pc i = s.pc i := Function.update_of_ne hi _ _
  have hch : (setLocal s p c b n).choosing i = s.choosing i := Function.update_of_ne hi _ _
  have hnum : (setLocal s p c b n).number i = s.number i := Function.update_of_ne hi _ _
  have hbef : ∀ k, AheadOf s i k → AheadOf (setLocal s p c b n) i k := by
    intro k hk
    by_cases hkp : k = p
    · subst hkp; exact aheadOf_step_other hi h hk
    · exact (aheadOf_setLocal_of_ne hi hkp).mpr hk
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · rw [hpc, hnum]; exact hs.number_pos
  · rw [hpc, hch]; exact hs.choosing_eq
  · intro j hj
    rw [hpc] at hj
    obtain ⟨hjN, hlt⟩ := hs.l2 j hj
    exact ⟨hjN, fun k hk hki => hbef k (hlt k hk hki)⟩
  · intro j hj
    rw [hpc] at hj
    obtain ⟨hjN, hlt, hcur⟩ := hs.l3 j hj
    refine ⟨hjN, fun k hk hki => hbef k (hlt k hk hki), fun k hk hki => ?_⟩
    rcases hcur k hk hki with hb | hw
    · exact Or.inl (hbef k hb)
    · by_cases hkp : k = p
      · subst hkp; exact waiting_step_other h hw
      · right
        simpa [setLocal, Function.update_of_ne hkp] using hw
  · intro hcs k hki
    rw [hpc] at hcs
    exact hbef k (hs.cs hcs k hki)

/-- **A step of process `i` preserves its own invariant**, given the invariants of all
processes. -/
theorem localInv_step_self {s : State N} {i : Fin N} {c : ProgramCounter N} {b : Bool} {n : ℕ}
    (h : LocalStep s i c b n) (hs : ∀ k, LocalInv s k) : LocalInv (setLocal s i c b n) i := by
  have hi := hs i
  cases h with
  | enter hp =>
    have h0 : s.number i = 0 := by
      have := hi.number_pos; rw [hp] at this; simp [HasTicket] at this; omega
    refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;> simp [setLocal, HasTicket, InDoorway, h0]
  | read U m k hp hk =>
    have h1 := hi.number_pos; have h2 := hi.choosing_eq
    rw [hp] at h1 h2
    refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;> simp_all [setLocal, HasTicket, InDoorway]
  | endRead m hp =>
    have h1 := hi.number_pos; have h2 := hi.choosing_eq
    rw [hp] at h1 h2
    refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;> simp_all [setLocal, HasTicket, InDoorway]
  | write m hp =>
    have h2 := hi.choosing_eq
    rw [hp] at h2
    refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;> simp_all [setLocal, HasTicket, InDoorway]
  | exit hp =>
    have h1 := hi.number_pos
    rw [hp] at h1
    refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;> simp_all [setLocal, HasTicket, InDoorway]
  | l2 j hj hp hfree =>
    obtain ⟨-, hlt⟩ := hi.l2 j hp
    have h1 := hi.number_pos; have h2 := hi.choosing_eq
    rw [hp] at h1 h2
    refine ⟨by simpa [setLocal, HasTicket] using h1, by simpa [setLocal, InDoorway] using h2,
      by simp [setLocal], fun j' hj' => ?_, by simp [setLocal]⟩
    simp only [setLocal, Function.update_self, ProgramCounter.l3.injEq] at hj'
    subst hj'
    refine ⟨hj, fun k hk hki => (aheadOf_setLocal_self hki).mpr (hlt k hk hki), fun k hk hki => ?_⟩
    have hk' : k = ⟨j, hj⟩ := Fin.ext hk
    subst hk'
    have hkpc : (setLocal s i (.l3 j) (s.choosing i) (s.number i)).pc ⟨j, hj⟩ = s.pc ⟨j, hj⟩ :=
      Function.update_of_ne hki _ _
    have hfl := (hs ⟨j, hj⟩).choosing_eq
    rw [hfree] at hfl
    rw [hkpc, aheadOf_setLocal_self hki]
    cases hpk : s.pc ⟨j, hj⟩ <;> simp_all [AheadOf, Waiting, InDoorway]
  | l3 j hj hp hpass =>
    obtain ⟨hjN, hlt, hcur⟩ := hi.l3 j hp
    have h1 := hi.number_pos; have h2 := hi.choosing_eq
    rw [hp] at h1 h2
    refine ⟨by simpa [setLocal, HasTicket] using h1, by simpa [setLocal, InDoorway] using h2,
      fun j' hj' => ?_, by simp [setLocal], by simp [setLocal]⟩
    simp only [setLocal, Function.update_self, ProgramCounter.l2.injEq] at hj'
    subst hj'
    refine ⟨hjN, fun k hk hki => (aheadOf_setLocal_self hki).mpr ?_⟩
    rcases Nat.lt_succ_iff_lt_or_eq.mp hk with hk | hk
    · exact hlt k hk hki
    · have hk' : k = ⟨j, hj⟩ := Fin.ext hk
      subst hk'
      rcases hcur _ hk hki with hb | hw
      · exact hb
      · have hpos := (hs ⟨j, hj⟩).number_pos
        have hticket : HasTicket (s.pc ⟨j, hj⟩) := by
          cases hpk : s.pc ⟨j, hj⟩ <;> simp_all [Waiting, HasTicket]
        have hne : s.number ⟨j, hj⟩ ≠ 0 := by have := hpos.mpr hticket; omega
        have hbefore := before_of_not (Ne.symm hki) (fun hb => hpass ⟨hne, hb⟩)
        cases hpk : s.pc ⟨j, hj⟩ <;> simp_all [AheadOf, Waiting, HasTicket]
  | enterCS hp =>
    obtain ⟨-, hlt⟩ := hi.l2 N hp
    have h1 := hi.number_pos; have h2 := hi.choosing_eq
    rw [hp] at h1 h2
    refine ⟨by simpa [setLocal, HasTicket] using h1, by simpa [setLocal, InDoorway] using h2,
      by simp [setLocal], by simp [setLocal],
      fun _ k hki => (aheadOf_setLocal_self hki).mpr (hlt k k.isLt hki)⟩
  | leave hp =>
    have h2 := hi.choosing_eq
    rw [hp] at h2
    refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;> simp_all [setLocal, HasTicket, InDoorway]
  | fail =>
    refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;> simp [setLocal, HasTicket, InDoorway]

/-- **The bakery invariant holds in every reachable state.** -/
theorem localInv_of_canReach {s : State N} (h : lts.CanReach init s) : ∀ i, LocalInv s i := by
  obtain ⟨μs, hμs⟩ := h
  refine Cslib.LTS.mtrInv_of_trInv (lts := lts) (p := fun s => ∀ i, LocalInv s i) ?_ _ _ _ hμs ?_
  · rintro s p s' ⟨c, b, n, hloc, rfl⟩ hs i
    by_cases hip : i = p
    · subst hip; exact localInv_step_self hloc hs
    · exact localInv_step_other hip hloc (hs i)
  · intro i
    refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;> simp [init, HasTicket, InDoorway]

/-- **Mutual exclusion for the bakery algorithm** (Lamport 1974, condition 1 on p. 454: "At any
time, at most one computer may be in its critical section"; Assertion 2 on p. 454 and the remark
after Assertion 3 on p. 455). In every reachable state, two processes in their critical sections are
the same process. Proved for atomic reads and writes and atomic crash-resets, which is weaker than
Lamport's result for reads that may return arbitrary values when they overlap a write. -/
theorem mutual_exclusion {s : State N} (h : lts.CanReach init s) {i k : Fin N}
    (hi : s.pc i = .cs) (hk : s.pc k = .cs) : i = k := by
  by_contra hik
  have hinv := localInv_of_canReach h
  have h1 := (hinv i).cs hi k (Ne.symm hik)
  have h2 := (hinv k).cs hk i hik
  simp only [AheadOf, hi, hk] at h1 h2
  exact before_asymm h1 h2

/-- **Assertion 2 of the bakery proof** (Lamport 1974, p. 454): if process `i` is in its
critical section and process `k ≠ i` holds a ticket, then `(number[i], i) < (number[k], k)`.
Holding a ticket covers Lamport's "in the bakery" and also the last doorway step, after
`number[k]` is written and before `choosing[k]` is reset. Proved with atomic registers, which is
weaker than Lamport's setting. -/
theorem before_of_cs {s : State N} (h : lts.CanReach init s) {i k : Fin N}
    (hi : s.pc i = .cs) (hk : HasTicket (s.pc k)) (hik : k ≠ i) :
    Before (s.number i) i (s.number k) k := by
  have hb := (localInv_of_canReach h i).cs hi k hik
  unfold AheadOf at hb
  cases hpk : s.pc k <;> simp_all [HasTicket]

end Cslib.Algorithms.Concurrency.BakeryNProcesses
