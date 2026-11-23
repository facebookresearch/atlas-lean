/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Lamport's bakery algorithm
-/
module

public import CSLibExt.Logics.LTL.Basic
public import CSLibExt.Foundations.Semantics.LTS.OmegaRun

/-!
# Lamport's bakery algorithm: mutual exclusion

Lamport, *A new solution of Dijkstra's concurrent programming problem*, CACM
17(8), 1974, for two processes `p0 < p1`. Process `i`, with the other process
`j`, cycles through:

* `ncs`: leave the noncritical section, raising `choosing[i]`;
* `read`: read `number[j]` into a local register `tmp[i]`;
* `write`: take the ticket `number[i] := tmp[i] + 1`;
* `doorway`: lower `choosing[i]`;
* `waitChoosing`: wait while `choosing[j]`;
* `waitNumber`: wait until `number[j] = 0` or `(number[i], i) < (number[j], j)`
  lexicographically;
* `critical`: the critical section;
* `exit`: return the ticket, `number[i] := 0`.

Reading the other ticket and writing one's own are separate steps, as in
Lamport's algorithm, where the maximum is not computed atomically; this is what
the `choosing` flags are for (without the `waitChoosing` check, both processes
can read `0`, take ticket `1`, and enter together). Tickets are unbounded natural
numbers.

Atomicity: each step reads or writes one shared register atomically, with
sequentially consistent memory, and the `waitChoosing` and `waitNumber` guards
are evaluated atomically. Lamport's paper proves the algorithm even for
registers whose reads may overlap writes and return arbitrary values; that
stronger model is not covered here.

The system is the interleaving of the two processes: one LTS step is one move
of one process (`bakery`). The main theorem `bakery_mutex` is mutual exclusion
as the LTL formula `□¬(cs0 ∧ cs1)` on every infinite run from the initial
state. It follows from the inductive invariant `Inv`, whose key clause is: a
process in its critical section comes before the other process in the ticket
order whenever the latter holds a ticket and is not returning it at `exit`
(`Inv.before`).
-/

@[expose] public section

namespace Cslib.Algorithms.Concurrency.Bakery

open Cslib.LTL

/-- The two processes. -/
inductive Proc
  | p0
  | p1
  deriving DecidableEq

/-- The other process. -/
def Proc.other : Proc → Proc
  | .p0 => .p1
  | .p1 => .p0

@[simp] theorem Proc.other_other (i : Proc) : i.other.other = i := by cases i <;> rfl

@[simp] theorem Proc.other_ne (i : Proc) : i.other ≠ i := by cases i <;> decide

@[simp] theorem Proc.ne_other (i : Proc) : i ≠ i.other := by cases i <;> decide

theorem Proc.eq_or_eq_other (i j : Proc) : j = i ∨ j = i.other := by
  cases i <;> cases j <;> simp [Proc.other]

/-- Program counters, in execution order. -/
inductive PC
  | ncs
  | read
  | write
  | doorway
  | waitChoosing
  | waitNumber
  | critical
  | exit
  deriving DecidableEq

/-- Global state: program counters, `choosing` flags, tickets, and the local
registers holding the ticket read from the other process. -/
structure State where
  /-- The program counter of each process. -/
  pc : Proc → PC
  /-- The `choosing` flag of each process. -/
  choosing : Proc → Bool
  /-- The ticket of each process; `0` when it holds none. -/
  number : Proc → ℕ
  /-- The local register holding the ticket read from the other process. -/
  tmp : Proc → ℕ

/-- The lexicographic ticket order `(number[i], i) < (number[j], j)`, with
`p0 < p1` breaking ties. -/
def Before (s : State) (i j : Proc) : Prop :=
  s.number i < s.number j ∨ (s.number i = s.number j ∧ i = .p0 ∧ j = .p1)

instance (s : State) (i j : Proc) : Decidable (Before s i j) :=
  inferInstanceAs (Decidable (_ ∨ _))

/-- Whether process `i` may enter its critical section: the other process holds
no ticket, or `i`'s ticket comes first. -/
def CanEnter (s : State) (i : Proc) : Prop :=
  s.number i.other = 0 ∨ Before s i i.other

instance (s : State) (i : Proc) : Decidable (CanEnter s i) :=
  inferInstanceAs (Decidable (_ ∨ _))

/-- One move of process `i`. -/
def step (i : Proc) (s : State) : State :=
  match s.pc i with
  | .ncs =>
      ⟨Function.update s.pc i .read, Function.update s.choosing i true, s.number, s.tmp⟩
  | .read =>
      ⟨Function.update s.pc i .write, s.choosing, s.number,
        Function.update s.tmp i (s.number i.other)⟩
  | .write =>
      ⟨Function.update s.pc i .doorway, s.choosing,
        Function.update s.number i (s.tmp i + 1), s.tmp⟩
  | .doorway =>
      ⟨Function.update s.pc i .waitChoosing, Function.update s.choosing i false, s.number,
        s.tmp⟩
  | .waitChoosing =>
      if s.choosing i.other then s
      else ⟨Function.update s.pc i .waitNumber, s.choosing, s.number, s.tmp⟩
  | .waitNumber =>
      if CanEnter s i then ⟨Function.update s.pc i .critical, s.choosing, s.number, s.tmp⟩
      else s
  | .critical => ⟨Function.update s.pc i .exit, s.choosing, s.number, s.tmp⟩
  | .exit => ⟨Function.update s.pc i .ncs, s.choosing, Function.update s.number i 0, s.tmp⟩

/-- The bakery algorithm as a labelled transition system; the label is the
process that moves. -/
def bakery : Cslib.LTS State Proc := ⟨fun s i t => t = step i s⟩

/-- Both processes in their noncritical sections, no tickets, no flags. -/
def initial : State := ⟨fun _ => .ncs, fun _ => false, fun _ => 0, fun _ => 0⟩

/-! ## The invariant -/

/-- Program counters during which `choosing` is raised. -/
def Choosing (pc : PC) : Prop := pc = .read ∨ pc = .write ∨ pc = .doorway

/-- Program counters during which a ticket is held. -/
def Holding (pc : PC) : Prop :=
  pc = .doorway ∨ pc = .waitChoosing ∨ pc = .waitNumber ∨ pc = .critical ∨ pc = .exit

/-- Program counters after the `choosing` check. -/
def Checked (pc : PC) : Prop := pc = .waitNumber ∨ pc = .critical

/-- The inductive invariant, for each process `i` against the other:
`choosing` and ticket-holding follow the program counter; a process past the
`choosing` check is not overtaken by a later `read` of the other; and a process
in its critical section comes first, unless the other holds no ticket or is
returning it. -/
structure Inv (s : State) : Prop where
  choosing : ∀ i, s.choosing i = true ↔ Choosing (s.pc i)
  holding : ∀ i, s.number i ≠ 0 ↔ Holding (s.pc i)
  read_after : ∀ i, Checked (s.pc i) → s.pc i.other = .write → s.number i ≤ s.tmp i.other
  before : ∀ i, s.pc i = .critical → Holding (s.pc i.other) → s.pc i.other ≠ .exit →
    Before s i i.other

theorem inv_initial : Inv initial where
  choosing i := by simp [initial, Choosing]
  holding i := by simp [initial, Holding]
  read_after i := by simp [initial, Checked]
  before i := by simp [initial]

section Preservation

variable (p : Proc) (s : State)

theorem update_other {α : Type*} (f : Proc → α) (a : α) :
    Function.update f p a p.other = f p.other :=
  Function.update_of_ne (Proc.other_ne p) a f

attribute [local simp] Function.update_self update_other Choosing Holding Checked Before CanEnter

/-- The invariant is preserved by every move. -/
theorem inv_step {p : Proc} {s : State} (h : Inv s) : Inv (step p s) := by
  obtain ⟨hc, hh, hr, hb⟩ := h
  have hcp := hc p
  have hco := hc p.other
  have hhp := hh p
  have hho := hh p.other
  have hrp := hr p
  have hro := hr p.other
  have hbp := hb p
  have hbo := hb p.other
  simp only [Proc.other_other] at hro hbo
  clear hc hh hr hb
  cases hpc : s.pc p with
  | ncs =>
      simp only [step, hpc]
      refine ⟨fun i => ?_, fun i => ?_, fun i => ?_, fun i => ?_⟩ <;>
        rcases Proc.eq_or_eq_other p i with rfl | rfl <;> simp_all
  | read =>
      simp only [step, hpc]
      refine ⟨fun i => ?_, fun i => ?_, fun i => ?_, fun i => ?_⟩ <;>
        rcases Proc.eq_or_eq_other p i with rfl | rfl <;> simp_all
  | write =>
      -- the new ticket exceeds that of a process past the `choosing` check
      simp only [step, hpc]
      refine ⟨fun i => ?_, fun i => ?_, fun i => ?_, fun i => ?_⟩ <;>
        rcases Proc.eq_or_eq_other p i with rfl | rfl <;> first
        | (simp_all; done)
        | (simp_all only [ne_eq, Proc.other_ne, not_false_eq_true, Function.update_of_ne,
            Holding, Proc.other_other, Function.update_self, reduceCtorEq, or_self, or_false,
            Before, forall_const]
           intro hcrit
           have := hro (Or.inr hcrit)
           omega)
  | doorway =>
      simp only [step, hpc]
      refine ⟨fun i => ?_, fun i => ?_, fun i => ?_, fun i => ?_⟩ <;>
        rcases Proc.eq_or_eq_other p i with rfl | rfl <;> simp_all
  | waitChoosing =>
      simp only [step, hpc]
      split
      · refine ⟨fun i => ?_, fun i => ?_, fun i => ?_, fun i => ?_⟩ <;>
          rcases Proc.eq_or_eq_other p i with rfl | rfl <;> simp_all
      · refine ⟨fun i => ?_, fun i => ?_, fun i => ?_, fun i => ?_⟩ <;>
          rcases Proc.eq_or_eq_other p i with rfl | rfl <;> simp_all
  | waitNumber =>
      -- entry: the guard and ticket-holding give priority over the other process
      simp only [step, hpc]
      split
      next hguard =>
        refine ⟨fun i => ?_, fun i => ?_, fun i => ?_, fun i => ?_⟩ <;>
          rcases Proc.eq_or_eq_other p i with rfl | rfl <;> first
          | (simp_all; done)
          | (simp only [Function.update_self, update_other]
             intro _ hhold _
             rcases hguard with h0 | hfirst
             · exact absurd h0 (hho.mpr hhold)
             · exact hfirst)
      · refine ⟨fun i => ?_, fun i => ?_, fun i => ?_, fun i => ?_⟩ <;>
          rcases Proc.eq_or_eq_other p i with rfl | rfl <;> simp_all
  | critical =>
      simp only [step, hpc]
      refine ⟨fun i => ?_, fun i => ?_, fun i => ?_, fun i => ?_⟩ <;>
        rcases Proc.eq_or_eq_other p i with rfl | rfl <;> simp_all
  | exit =>
      simp only [step, hpc]
      refine ⟨fun i => ?_, fun i => ?_, fun i => ?_, fun i => ?_⟩ <;>
        rcases Proc.eq_or_eq_other p i with rfl | rfl <;> simp_all

end Preservation

theorem inv_of_step {s t : State} (h : Inv s) (hstep : bakery.UnlabelledTr s t) : Inv t := by
  obtain ⟨p, rfl⟩ := hstep
  exact inv_step h

/-- The invariant excludes both processes from the critical section: each
would have to come first. -/
theorem mutex_of_inv {s : State} (h : Inv s) :
    ¬ (s.pc .p0 = .critical ∧ s.pc .p1 = .critical) := by
  rintro ⟨h0, h1⟩
  have b0 := h.before .p0 h0 (by simp [Proc.other, h1, Holding]) (by simp [Proc.other, h1])
  have b1 := h.before .p1 h1 (by simp [Proc.other, h0, Holding]) (by simp [Proc.other, h0])
  simp [Before, Proc.other] at b0 b1
  omega

/-! ## Mutual exclusion in LTL -/

/-- LTL atoms: each process is in its critical section. -/
inductive Atom
  | cs0
  | cs1
  deriving DecidableEq

/-- The valuation of the atoms. -/
def valuation (s : State) : Atom → Prop
  | .cs0 => s.pc .p0 = .critical
  | .cs1 => s.pc .p1 = .critical

/-- **Mutual exclusion for the bakery algorithm**: on every infinite run from
the initial state, `□¬(cs0 ∧ cs1)`. -/
theorem bakery_mutex :
    ForallRuns bakery valuation initial
      (Formula.always (.not (.and (.atom .cs0) (.atom .cs1)))) := by
  intro run hr0 hrun
  have hInv : ∀ k, Inv (run k) :=
    Cslib.LTS.forall_state_of_invariant hrun (by rw [hr0]; exact inv_initial)
      (fun _ _ hs hstep => inv_of_step hs hstep)
  rw [Satisfies.always_iff]
  intro k
  change ¬ (SatisfiesAt valuation run k (.atom .cs0) ∧ SatisfiesAt valuation run k (.atom .cs1))
  rintro ⟨h0, h1⟩
  rw [Satisfies.atomAt_iff] at h0 h1
  exact mutex_of_inv (hInv k) ⟨h0, h1⟩

end Cslib.Algorithms.Concurrency.Bakery
