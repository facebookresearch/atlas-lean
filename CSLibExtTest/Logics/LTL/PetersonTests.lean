/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.Logics.LTL.Induction

@[expose] public section

set_option autoImplicit false

namespace Cslib.LTL.PetersonTests

/-!
# Peterson's mutual-exclusion algorithm in LTL

Two processes repeatedly try to enter their critical sections.  Process
`i` (with the other process `j`) runs:

* `idle`: decide to try, move to `setFlag`;
* `setFlag`: set `flag[i]`, move to `setTurn`;
* `setTurn`: set `turn := j` (yield to the other), move to `wait`;
* `wait`: spin while `flag[j] ∧ turn = j`, else enter `critical`;
* `critical`: leave for `clear`;
* `clear`: clear `flag[i]`, return to `idle`.

A step of the LTS is a single move of a single process, so the system
is the asynchronous interleaving of the two programs.  The `last`
component records the process that moved most recently; the LTL atoms
`step0`/`step1` talk about it, which lets the fairness hypothesis
(each process moves infinitely often, `□◇ step0 ∧ □◇ step1`) be an
LTL formula.  Safety is `□¬(cs0 ∧ cs1)`; liveness is `□◇ cs0 ∧ □◇ cs1`
under fairness.
-/

/-- The two processes. -/
inductive Proc where
  | p0
  | p1
  deriving DecidableEq, Repr

/-- The other process. -/
def Proc.other : Proc → Proc
  | .p0 => .p1
  | .p1 => .p0

theorem Proc.other_other (p : Proc) : p.other.other = p := by
  cases p <;> rfl

theorem Proc.ne_other (p : Proc) : p ≠ p.other := by
  cases p <;> decide

theorem Proc.eq_other_of_ne {a b : Proc} (h : a ≠ b) : a = b.other := by
  cases a <;> cases b <;> simp [Proc.other] at h ⊢

/-- Program counters, in execution order. -/
inductive PC where
  | idle
  | setFlag
  | setTurn
  | wait
  | critical
  | clear
  deriving DecidableEq, Repr

/-- Global state: both program counters, both flags, the `turn`
variable, and the process that moved last. -/
structure State where
  pc0 : PC
  pc1 : PC
  flag0 : Bool
  flag1 : Bool
  turn : Proc
  last : Proc
  deriving DecidableEq, Repr

/-- One move of process 0. -/
def move0 : State → State
  | ⟨.idle, pc1, f0, f1, t, _⟩ => ⟨.setFlag, pc1, f0, f1, t, .p0⟩
  | ⟨.setFlag, pc1, _, f1, t, _⟩ => ⟨.setTurn, pc1, true, f1, t, .p0⟩
  | ⟨.setTurn, pc1, f0, f1, _, _⟩ => ⟨.wait, pc1, f0, f1, .p1, .p0⟩
  | ⟨.wait, pc1, f0, f1, t, _⟩ =>
      if f1 = true ∧ t = .p1 then ⟨.wait, pc1, f0, f1, t, .p0⟩
      else ⟨.critical, pc1, f0, f1, t, .p0⟩
  | ⟨.critical, pc1, f0, f1, t, _⟩ => ⟨.clear, pc1, f0, f1, t, .p0⟩
  | ⟨.clear, pc1, _, f1, t, _⟩ => ⟨.idle, pc1, false, f1, t, .p0⟩

/-- One move of process 1. -/
def move1 : State → State
  | ⟨pc0, .idle, f0, f1, t, _⟩ => ⟨pc0, .setFlag, f0, f1, t, .p1⟩
  | ⟨pc0, .setFlag, f0, _, t, _⟩ => ⟨pc0, .setTurn, f0, true, t, .p1⟩
  | ⟨pc0, .setTurn, f0, f1, _, _⟩ => ⟨pc0, .wait, f0, f1, .p0, .p1⟩
  | ⟨pc0, .wait, f0, f1, t, _⟩ =>
      if f0 = true ∧ t = .p0 then ⟨pc0, .wait, f0, f1, t, .p1⟩
      else ⟨pc0, .critical, f0, f1, t, .p1⟩
  | ⟨pc0, .critical, f0, f1, t, _⟩ => ⟨pc0, .clear, f0, f1, t, .p1⟩
  | ⟨pc0, .clear, f0, _, t, _⟩ => ⟨pc0, .idle, f0, false, t, .p1⟩

/-- One move of the given process. -/
def nextState (p : Proc) (s : State) : State :=
  match p with
  | .p0 => move0 s
  | .p1 => move1 s

theorem nextState_p0_wait_stay {pc1 : PC} {f0 f1 : Bool} {t l : Proc}
    (hc : f1 = true ∧ t = .p1) :
    nextState .p0 ⟨.wait, pc1, f0, f1, t, l⟩ = ⟨.wait, pc1, f0, f1, t, .p0⟩ := by
  change (if f1 = true ∧ t = Proc.p1 then (⟨.wait, pc1, f0, f1, t, .p0⟩ : State)
    else ⟨.critical, pc1, f0, f1, t, .p0⟩) = _
  rw [ite_eq_left hc]

theorem nextState_p0_wait_enter {pc1 : PC} {f0 f1 : Bool} {t l : Proc}
    (hc : ¬ (f1 = true ∧ t = .p1)) :
    nextState .p0 ⟨.wait, pc1, f0, f1, t, l⟩ = ⟨.critical, pc1, f0, f1, t, .p0⟩ := by
  change (if f1 = true ∧ t = Proc.p1 then (⟨.wait, pc1, f0, f1, t, .p0⟩ : State)
    else ⟨.critical, pc1, f0, f1, t, .p0⟩) = _
  rw [ite_eq_right hc]

theorem nextState_p1_wait_stay {pc0 : PC} {f0 f1 : Bool} {t l : Proc}
    (hc : f0 = true ∧ t = .p0) :
    nextState .p1 ⟨pc0, .wait, f0, f1, t, l⟩ = ⟨pc0, .wait, f0, f1, t, .p1⟩ := by
  change (if f0 = true ∧ t = Proc.p0 then (⟨pc0, .wait, f0, f1, t, .p1⟩ : State)
    else ⟨pc0, .critical, f0, f1, t, .p1⟩) = _
  rw [ite_eq_left hc]

theorem nextState_p1_wait_enter {pc0 : PC} {f0 f1 : Bool} {t l : Proc}
    (hc : ¬ (f0 = true ∧ t = .p0)) :
    nextState .p1 ⟨pc0, .wait, f0, f1, t, l⟩ = ⟨pc0, .critical, f0, f1, t, .p1⟩ := by
  change (if f0 = true ∧ t = Proc.p0 then (⟨pc0, .wait, f0, f1, t, .p1⟩ : State)
    else ⟨pc0, .critical, f0, f1, t, .p1⟩) = _
  rw [ite_eq_right hc]

/-- Peterson's algorithm as a labelled transition system; the label is
the process that moves. -/
def peterson : _root_.Cslib.LTS State Proc := ⟨fun s p t => t = nextState p s⟩

/-- Both processes idle, both flags down. -/
def initial : State := ⟨.idle, .idle, false, false, .p0, .p0⟩

/-- The program counter of a process. -/
def pcOf (p : Proc) (s : State) : PC :=
  match p with
  | .p0 => s.pc0
  | .p1 => s.pc1

/-- The flag of a process. -/
def flagOf (p : Proc) (s : State) : Bool :=
  match p with
  | .p0 => s.flag0
  | .p1 => s.flag1

/-- How a program counter advances when its process moves: at `wait`
the process proceeds unless the other process has its flag up and the
turn. -/
def advance (p : Proc) (pc : PC) (otherFlag : Bool) (turn : Proc) : PC :=
  match pc with
  | .idle => .setFlag
  | .setFlag => .setTurn
  | .setTurn => .wait
  | .wait => if otherFlag = true ∧ turn = p.other then .wait else .critical
  | .critical => .clear
  | .clear => .idle

theorem advance_wait (p : Proc) (f : Bool) (t : Proc) :
    advance p .wait f t = if f = true ∧ t = p.other then .wait else .critical :=
  rfl

theorem nextState_last (p : Proc) (s : State) : (nextState p s).last = p := by
  cases p with
  | p0 =>
      obtain ⟨pc0, pc1, f0, f1, t, l⟩ := s
      cases pc0 with
      | wait =>
          by_cases hc : f1 = true ∧ t = Proc.p1
          · rw [nextState_p0_wait_stay hc]
          · rw [nextState_p0_wait_enter hc]
      | idle => rfl
      | setFlag => rfl
      | setTurn => rfl
      | critical => rfl
      | clear => rfl
  | p1 =>
      obtain ⟨pc0, pc1, f0, f1, t, l⟩ := s
      cases pc1 with
      | wait =>
          by_cases hc : f0 = true ∧ t = Proc.p0
          · rw [nextState_p1_wait_stay hc]
          · rw [nextState_p1_wait_enter hc]
      | idle => rfl
      | setFlag => rfl
      | setTurn => rfl
      | critical => rfl
      | clear => rfl

theorem nextState_pcOf_self (p : Proc) (s : State) :
    pcOf p (nextState p s) =
      advance p (pcOf p s) (flagOf p.other s) s.turn := by
  cases p with
  | p0 =>
      obtain ⟨pc0, pc1, f0, f1, t, l⟩ := s
      cases pc0 with
      | wait =>
          by_cases hc : f1 = true ∧ t = Proc.p1
          · rw [nextState_p0_wait_stay hc]
            change PC.wait = if f1 = true ∧ t = Proc.p1 then PC.wait else PC.critical
            rw [ite_eq_left hc]
          · rw [nextState_p0_wait_enter hc]
            change PC.critical =
              if f1 = true ∧ t = Proc.p1 then PC.wait else PC.critical
            rw [ite_eq_right hc]
      | idle => rfl
      | setFlag => rfl
      | setTurn => rfl
      | critical => rfl
      | clear => rfl
  | p1 =>
      obtain ⟨pc0, pc1, f0, f1, t, l⟩ := s
      cases pc1 with
      | wait =>
          by_cases hc : f0 = true ∧ t = Proc.p0
          · rw [nextState_p1_wait_stay hc]
            change PC.wait = if f0 = true ∧ t = Proc.p0 then PC.wait else PC.critical
            rw [ite_eq_left hc]
          · rw [nextState_p1_wait_enter hc]
            change PC.critical =
              if f0 = true ∧ t = Proc.p0 then PC.wait else PC.critical
            rw [ite_eq_right hc]
      | idle => rfl
      | setFlag => rfl
      | setTurn => rfl
      | critical => rfl
      | clear => rfl

theorem nextState_pcOf_other (p : Proc) (s : State) :
    pcOf p.other (nextState p s) = pcOf p.other s := by
  cases p with
  | p0 =>
      obtain ⟨pc0, pc1, f0, f1, t, l⟩ := s
      cases pc0 with
      | wait =>
          by_cases hc : f1 = true ∧ t = Proc.p1
          · rw [nextState_p0_wait_stay hc]
            rfl
          · rw [nextState_p0_wait_enter hc]
            rfl
      | idle => rfl
      | setFlag => rfl
      | setTurn => rfl
      | critical => rfl
      | clear => rfl
  | p1 =>
      obtain ⟨pc0, pc1, f0, f1, t, l⟩ := s
      cases pc1 with
      | wait =>
          by_cases hc : f0 = true ∧ t = Proc.p0
          · rw [nextState_p1_wait_stay hc]
            rfl
          · rw [nextState_p1_wait_enter hc]
            rfl
      | idle => rfl
      | setFlag => rfl
      | setTurn => rfl
      | critical => rfl
      | clear => rfl

theorem nextState_flagOf_other (p : Proc) (s : State) :
    flagOf p.other (nextState p s) = flagOf p.other s := by
  cases p with
  | p0 =>
      obtain ⟨pc0, pc1, f0, f1, t, l⟩ := s
      cases pc0 with
      | wait =>
          by_cases hc : f1 = true ∧ t = Proc.p1
          · rw [nextState_p0_wait_stay hc]
            rfl
          · rw [nextState_p0_wait_enter hc]
            rfl
      | idle => rfl
      | setFlag => rfl
      | setTurn => rfl
      | critical => rfl
      | clear => rfl
  | p1 =>
      obtain ⟨pc0, pc1, f0, f1, t, l⟩ := s
      cases pc1 with
      | wait =>
          by_cases hc : f0 = true ∧ t = Proc.p0
          · rw [nextState_p1_wait_stay hc]
            rfl
          · rw [nextState_p1_wait_enter hc]
            rfl
      | idle => rfl
      | setFlag => rfl
      | setTurn => rfl
      | critical => rfl
      | clear => rfl

theorem nextState_turn (p : Proc) (s : State) :
    (nextState p s).turn =
      if pcOf p s = .setTurn then p.other else s.turn := by
  cases p with
  | p0 =>
      obtain ⟨pc0, pc1, f0, f1, t, l⟩ := s
      cases pc0 with
      | wait =>
          by_cases hc : f1 = true ∧ t = Proc.p1
          · rw [nextState_p0_wait_stay hc]
            rfl
          · rw [nextState_p0_wait_enter hc]
            rfl
      | idle => rfl
      | setFlag => rfl
      | setTurn => rfl
      | critical => rfl
      | clear => rfl
  | p1 =>
      obtain ⟨pc0, pc1, f0, f1, t, l⟩ := s
      cases pc1 with
      | wait =>
          by_cases hc : f0 = true ∧ t = Proc.p0
          · rw [nextState_p1_wait_stay hc]
            rfl
          · rw [nextState_p1_wait_enter hc]
            rfl
      | idle => rfl
      | setFlag => rfl
      | setTurn => rfl
      | critical => rfl
      | clear => rfl

/-- Distance from a program counter to `{wait, critical}` along the
program cycle, counted in own moves. -/
def distToWait : PC → ℕ
  | .wait => 0
  | .critical => 0
  | .setTurn => 1
  | .setFlag => 2
  | .idle => 3
  | .clear => 4

/-- Distance from a program counter to `setTurn` along the program
cycle, counted in own moves (leaving `wait` for `critical`). -/
def distToSetTurn : PC → ℕ
  | .setTurn => 0
  | .setFlag => 1
  | .idle => 2
  | .clear => 3
  | .critical => 4
  | .wait => 5

theorem distToWait_advance_lt {p : Proc} {pc : PC} {f : Bool} {t : Proc}
    (hpc : pc ≠ .wait ∧ pc ≠ .critical) :
    distToWait (advance p pc f t) < distToWait pc := by
  cases pc <;> simp [advance, distToWait] at hpc ⊢

theorem distToSetTurn_advance_lt {q : Proc} {pc : PC} (hpc : pc ≠ .setTurn) :
    distToSetTurn (advance q pc true q) < distToSetTurn pc := by
  cases pc with
  | setTurn => exact (hpc rfl).elim
  | idle => simp [advance, distToSetTurn]
  | setFlag => simp [advance, distToSetTurn]
  | clear => simp [advance, distToSetTurn]
  | critical => simp [advance, distToSetTurn]
  | wait =>
      rw [advance_wait]
      rw [ite_eq_right (fun h => Proc.ne_other q h.2)]
      decide

/-- LTL atoms: in the critical section, flag raised, moved last. -/
inductive Atom where
  | cs0
  | cs1
  | flag0
  | flag1
  | step0
  | step1
  deriving DecidableEq, Repr

/-- The valuation of the atoms on states. -/
def valuation (s : State) : Atom → Prop
  | .cs0 => s.pc0 = .critical
  | .cs1 => s.pc1 = .critical
  | .flag0 => s.flag0 = true
  | .flag1 => s.flag1 = true
  | .step0 => s.last = .p0
  | .step1 => s.last = .p1

/-- The program counters at which the process's flag is raised: the
flag is set by the `setFlag` step (landing at `setTurn`) and cleared
by the `clear` step (landing at `idle`). -/
def flagRegion (pc : PC) : Prop :=
  pc = .setTurn ∨ pc = .wait ∨ pc = .critical ∨ pc = .clear

/-- Program counters from which a process must still pass its
`setTurn` step (thereby yielding the turn) before it can threaten the
other's critical section. -/
def early (pc : PC) : Prop :=
  pc = .idle ∨ pc = .setFlag ∨ pc = .setTurn

theorem early_of_not_flagRegion {pc : PC} (h : ¬ flagRegion pc) : early pc := by
  cases pc <;> simp [flagRegion, early] at h ⊢

theorem not_early_critical {pc : PC} (h : pc = .critical) : ¬ early pc := by
  rw [h]
  simp [early]

/-- The safety invariant.  The flag components tie each flag to its
program counter.  The critical components say that a process in its
critical section is protected: either it has the turn, or the other
process has not yet passed the point where it yields the turn. -/
def Inv (s : State) : Prop :=
  (s.flag0 = true ↔ flagRegion s.pc0) ∧
  (s.flag1 = true ↔ flagRegion s.pc1) ∧
  (s.pc0 = .critical → s.turn = .p0 ∨ early s.pc1) ∧
  (s.pc1 = .critical → s.turn = .p1 ∨ early s.pc0)

theorem flagOf_of_inv {s : State} (h : Inv s) (p : Proc) :
    flagOf p s = true ↔ flagRegion (pcOf p s) := by
  cases p with
  | p0 => exact h.1
  | p1 => exact h.2.1

theorem inv_initial : Inv initial := by
  simp [Inv, initial, flagRegion, early]

/-- The invariant is preserved by every move.  The only case needing
real argument is entry into the critical section: the `wait` guard
gives `¬(flag ∧ turn = other)`, so either the entering process has
the turn, or the other's flag is down, which by the flag components
puts the other at `idle` or `setFlag`, hence `early`. -/
theorem inv_nextState (p : Proc) {s : State} (h : Inv s) :
    Inv (nextState p s) := by
  obtain ⟨hI0, hI1, hC0, hC1⟩ := h
  cases p with
  | p0 =>
      obtain ⟨pc0, pc1, f0, f1, t, l⟩ := s
      cases pc0 with
      | idle =>
          change Inv ⟨.setFlag, pc1, f0, f1, t, .p0⟩
          refine ⟨?_, ?_, ?_, ?_⟩ <;>
            simp [flagRegion, early] at hI0 hI1 hC0 hC1 ⊢ <;> assumption
      | setFlag =>
          change Inv ⟨.setTurn, pc1, true, f1, t, .p0⟩
          refine ⟨?_, ?_, ?_, ?_⟩ <;>
            simp [flagRegion, early] at hI0 hI1 hC0 hC1 ⊢; assumption
      | setTurn =>
          change Inv ⟨.wait, pc1, f0, f1, .p1, .p0⟩
          refine ⟨?_, ?_, ?_, ?_⟩ <;>
            simp [flagRegion, early] at hI0 hI1 hC0 hC1 ⊢ <;> assumption
      | wait =>
          by_cases hc : f1 = true ∧ t = Proc.p1
          · rw [nextState_p0_wait_stay hc]
            refine ⟨?_, ?_, ?_, ?_⟩ <;>
              simp [flagRegion, early] at hI0 hI1 hC0 hC1 ⊢ <;> assumption
          · have hC0' : t = Proc.p0 ∨ early pc1 := by
              cases t with
              | p0 => exact Or.inl rfl
              | p1 =>
                  refine Or.inr (early_of_not_flagRegion ?_)
                  change f1 = true ↔ flagRegion pc1 at hI1
                  rw [← hI1]
                  intro hf1
                  exact hc ⟨hf1, rfl⟩
            rw [nextState_p0_wait_enter hc]
            refine ⟨?_, ?_, fun _ => hC0', ?_⟩ <;>
              simp [flagRegion, early] at hI0 hI1 hC0 hC1 ⊢ <;> assumption
      | critical =>
          change Inv ⟨.clear, pc1, f0, f1, t, .p0⟩
          refine ⟨?_, ?_, ?_, ?_⟩ <;>
            simp [flagRegion, early] at hI0 hI1 hC0 hC1 ⊢ <;> assumption
      | clear =>
          change Inv ⟨.idle, pc1, false, f1, t, .p0⟩
          refine ⟨?_, ?_, ?_, ?_⟩ <;>
            simp [flagRegion, early] at hI0 hI1 hC0 hC1 ⊢; assumption
  | p1 =>
      obtain ⟨pc0, pc1, f0, f1, t, l⟩ := s
      cases pc1 with
      | idle =>
          change Inv ⟨pc0, .setFlag, f0, f1, t, .p1⟩
          refine ⟨?_, ?_, ?_, ?_⟩ <;>
            simp [flagRegion, early] at hI0 hI1 hC0 hC1 ⊢ <;> assumption
      | setFlag =>
          change Inv ⟨pc0, .setTurn, f0, true, t, .p1⟩
          refine ⟨?_, ?_, ?_, ?_⟩ <;>
            simp [flagRegion, early] at hI0 hI1 hC0 hC1 ⊢; assumption
      | setTurn =>
          change Inv ⟨pc0, .wait, f0, f1, .p0, .p1⟩
          refine ⟨?_, ?_, ?_, ?_⟩ <;>
            simp [flagRegion, early] at hI0 hI1 hC0 hC1 ⊢ <;> assumption
      | wait =>
          by_cases hc : f0 = true ∧ t = Proc.p0
          · rw [nextState_p1_wait_stay hc]
            refine ⟨?_, ?_, ?_, ?_⟩ <;>
              simp [flagRegion, early] at hI0 hI1 hC0 hC1 ⊢ <;> assumption
          · have hC1' : t = Proc.p1 ∨ early pc0 := by
              cases t with
              | p1 => exact Or.inl rfl
              | p0 =>
                  refine Or.inr (early_of_not_flagRegion ?_)
                  change f0 = true ↔ flagRegion pc0 at hI0
                  rw [← hI0]
                  intro hf0
                  exact hc ⟨hf0, rfl⟩
            rw [nextState_p1_wait_enter hc]
            refine ⟨?_, ?_, ?_, fun _ => hC1'⟩ <;>
              simp [flagRegion, early] at hI0 hI1 hC0 hC1 ⊢ <;> assumption
      | critical =>
          change Inv ⟨pc0, .clear, f0, f1, t, .p1⟩
          refine ⟨?_, ?_, ?_, ?_⟩ <;>
            simp [flagRegion, early] at hI0 hI1 hC0 hC1 ⊢ <;> assumption
      | clear =>
          change Inv ⟨pc0, .idle, f0, false, t, .p1⟩
          refine ⟨?_, ?_, ?_, ?_⟩ <;>
            simp [flagRegion, early] at hI0 hI1 hC0 hC1 ⊢; assumption

theorem inv_step {s t : State} (h : Inv s) (hstep : peterson.UnlabelledTr s t) :
    Inv t := by
  have hstep' : ∃ p, t = nextState p s := hstep
  obtain ⟨p, hp⟩ := hstep'
  rw [hp]
  exact inv_nextState p h

theorem mutex_of_inv {s : State} (h : Inv s) :
    ¬ (s.pc0 = .critical ∧ s.pc1 = .critical) := by
  rintro ⟨h0, h1⟩
  obtain ⟨_, _, hC0, hC1⟩ := h
  rcases hC0 h0 with ht | he
  · rcases hC1 h1 with ht1 | he1
    · rw [ht] at ht1
      exact absurd ht1 (by decide)
    · exact not_early_critical h0 he1
  · exact not_early_critical h1 he

/-- Mutual exclusion: on every infinite run from the initial state,
the two processes are never in their critical sections together. -/
theorem peterson_safety :
    ForallRuns peterson valuation initial
      (Formula.always (.not (.and (.atom .cs0) (.atom .cs1)))) := by
  intro run hr0 hrun
  have hInv : ∀ k, Inv (run k) :=
    Cslib.LTS.forall_state_of_invariant hrun (by rw [hr0]; exact inv_initial)
      (fun _ _ hs hstep => inv_step hs hstep)
  rw [Satisfies.always_iff]
  intro k
  change ¬ (SatisfiesAt valuation run k (.atom .cs0) ∧
    SatisfiesAt valuation run k (.atom .cs1))
  rintro ⟨h0, h1⟩
  rw [Satisfies.atomAt_iff] at h0 h1
  exact mutex_of_inv (hInv k) ⟨h0, h1⟩

/-- Fairness as an LTL formula: each process moves infinitely often
(`□◇ step0 ∧ □◇ step1`, where `stepI` records that process `i` made
the most recent move). -/
def fairFormula : Formula Atom :=
  .and (Formula.always (Formula.eventually (.atom .step0)))
    (Formula.always (Formula.eventually (.atom .step1)))

/-- Liveness as an LTL formula: each process is in its critical
section infinitely often. -/
def liveFormula : Formula Atom :=
  .and (Formula.always (Formula.eventually (.atom .cs0)))
    (Formula.always (Formula.eventually (.atom .cs1)))

theorem eq_wait_or_crit_of_distToWait_eq_zero {pc : PC}
    (h : distToWait pc = 0) : pc = .wait ∨ pc = .critical := by
  cases pc <;> simp [distToWait] at h ⊢

theorem eq_setTurn_of_distToSetTurn_eq_zero {pc : PC}
    (h : distToSetTurn pc = 0) : pc = .setTurn := by
  cases pc <;> simp [distToSetTurn] at h ⊢

/-- An infinite run comes with a choice of mover at each step. -/
theorem mover_of_omegaRun {run : ℕ → State} (hrun : Cslib.LTS.OmegaRun (lts := peterson) run) :
    ∃ mover : ℕ → Proc, ∀ i, run (i + 1) = nextState (mover i) (run i) := by
  have h : ∀ i, ∃ p, run (i + 1) = nextState p (run i) := hrun
  exact ⟨fun i => Classical.choose (h i),
    fun i => Classical.choose_spec (h i)⟩

/-- The LTL fairness formula says exactly that each process is the
mover at arbitrarily late steps. -/
theorem fair_of_ltl {run : ℕ → State} {mover : ℕ → Proc}
    (hmover : ∀ i, run (i + 1) = nextState (mover i) (run i))
    (hfair : Satisfies valuation run fairFormula) (p : Proc) (k : ℕ) :
    ∃ m, k ≤ m ∧ mover m = p := by
  have hfair' : Satisfies valuation run
      (.and (Formula.always (Formula.eventually (.atom .step0)))
        (Formula.always (Formula.eventually (.atom .step1)))) := hfair
  obtain ⟨hf0, hf1⟩ := Satisfies.and_iff.mp hfair'
  cases p with
  | p0 =>
      rw [Satisfies.always_iff] at hf0
      obtain ⟨j, hj⟩ := satisfiesAt_eventually.mp (hf0 (k + 1))
      rw [Satisfies.atomAt_iff] at hj
      change (run (k + 1 + j)).last = Proc.p0 at hj
      have e : k + 1 + j = k + j + 1 := by omega
      rw [e, hmover (k + j), nextState_last] at hj
      exact ⟨k + j, by omega, hj⟩
  | p1 =>
      rw [Satisfies.always_iff] at hf1
      obtain ⟨j, hj⟩ := satisfiesAt_eventually.mp (hf1 (k + 1))
      rw [Satisfies.atomAt_iff] at hj
      change (run (k + 1 + j)).last = Proc.p1 at hj
      have e : k + 1 + j = k + j + 1 := by omega
      rw [e, hmover (k + j), nextState_last] at hj
      exact ⟨k + j, by omega, hj⟩

section Liveness

variable {run : ℕ → State} {mover : ℕ → Proc}

theorem pcOf_succ_of_mover (hmover : ∀ i, run (i + 1) = nextState (mover i) (run i)) {p : Proc} {m : ℕ} (h : mover m = p) :
    pcOf p (run (m + 1)) =
      advance p (pcOf p (run m)) (flagOf p.other (run m)) (run m).turn := by
  rw [hmover m, h]
  exact nextState_pcOf_self _ _

theorem pcOf_succ_of_mover_ne (hmover : ∀ i, run (i + 1) = nextState (mover i) (run i)) {p : Proc} {m : ℕ} (h : mover m ≠ p) :
    pcOf p (run (m + 1)) = pcOf p (run m) := by
  rw [hmover m]
  have e : mover m = p.other := Proc.eq_other_of_ne h
  rw [e]
  have hpc := nextState_pcOf_other p.other (run m)
  rwa [Proc.other_other] at hpc

theorem flagOf_succ_of_mover_ne (hmover : ∀ i, run (i + 1) = nextState (mover i) (run i)) {p : Proc} {m : ℕ} (h : mover m ≠ p) :
    flagOf p (run (m + 1)) = flagOf p (run m) := by
  rw [hmover m]
  have e : mover m = p.other := Proc.eq_other_of_ne h
  rw [e]
  have hf := nextState_flagOf_other p.other (run m)
  rwa [Proc.other_other] at hf

theorem turn_succ (hmover : ∀ i, run (i + 1) = nextState (mover i) (run i)) {m : ℕ} :
    (run (m + 1)).turn =
      if pcOf (mover m) (run m) = .setTurn then (mover m).other
      else (run m).turn := by
  rw [hmover m]
  exact nextState_turn _ _

/-- Bounded form of `exists_nextMove`: given a move of `p` in
`[k, k + d)`, the first such move still sees `p`'s program counter
and flag from time `k`. -/
theorem exists_nextMove_aux
    (hmover : ∀ i, run (i + 1) = nextState (mover i) (run i)) {p : Proc} :
    ∀ (d k : ℕ), (∃ m, k ≤ m ∧ m < k + d ∧ mover m = p) →
      ∃ m, k ≤ m ∧ mover m = p ∧ pcOf p (run m) = pcOf p (run k) ∧
        flagOf p (run m) = flagOf p (run k) := by
  intro d
  induction d with
  | zero =>
      intro k h
      obtain ⟨m, hm1, hm2, -⟩ := h
      exact False.elim (by omega)
  | succ d ih =>
      intro k h
      obtain ⟨m0, hm1, hm2, hm3⟩ := h
      by_cases hk : mover k = p
      · exact ⟨k, Nat.le_refl k, hk, rfl, rfl⟩
      · have hne : m0 ≠ k := by
          rintro rfl
          exact hk hm3
        obtain ⟨m, h1, h2, h3, h4⟩ :=
          ih (k + 1) ⟨m0, by omega, by omega, hm3⟩
        exact ⟨m, by omega, h2,
          by rw [h3, pcOf_succ_of_mover_ne hmover hk],
          by rw [h4, flagOf_succ_of_mover_ne hmover hk]⟩

/-- The next move of a process after `k` still sees the process's own
program counter and flag from time `k`. -/
theorem exists_nextMove
    (hmover : ∀ i, run (i + 1) = nextState (mover i) (run i))
    (hfair : ∀ (p : Proc) (k : ℕ), ∃ m, k ≤ m ∧ mover m = p)
    (p : Proc) (k : ℕ) :
    ∃ m, k ≤ m ∧ mover m = p ∧ pcOf p (run m) = pcOf p (run k) ∧
      flagOf p (run m) = flagOf p (run k) := by
  obtain ⟨m0, hm1, hm2⟩ := hfair p k
  exact exists_nextMove_aux hmover (m0 - k + 1) k ⟨m0, hm1, by omega, hm2⟩

theorem exists_wait_or_crit_aux
    (hmover : ∀ i, run (i + 1) = nextState (mover i) (run i))
    (hfair : ∀ (p : Proc) (k : ℕ), ∃ m, k ≤ m ∧ mover m = p)
    (p : Proc) :
    ∀ (d k : ℕ), distToWait (pcOf p (run k)) ≤ d →
      ∃ m, k ≤ m ∧ (pcOf p (run m) = .wait ∨ pcOf p (run m) = .critical) := by
  intro d
  induction d with
  | zero =>
      intro k hk
      exact ⟨k, Nat.le_refl k,
        eq_wait_or_crit_of_distToWait_eq_zero (Nat.le_zero.mp hk)⟩
  | succ d ih =>
      intro k hk
      by_cases hwc : pcOf p (run k) = .wait ∨ pcOf p (run k) = .critical
      · exact ⟨k, Nat.le_refl k, hwc⟩
      · obtain ⟨m, hkm, hmvm, hpcm, -⟩ := exists_nextMove hmover hfair p k
        have hdist : distToWait (pcOf p (run (m + 1))) ≤ d := by
          have hlt : distToWait (pcOf p (run (m + 1))) <
              distToWait (pcOf p (run m)) := by
            rw [pcOf_succ_of_mover hmover hmvm]
            apply distToWait_advance_lt
            rw [hpcm]
            exact ⟨fun h1 => hwc (Or.inl h1), fun h2 => hwc (Or.inr h2)⟩
          have hk' : distToWait (pcOf p (run m)) ≤ d + 1 := by
            rwa [hpcm]
          omega
        obtain ⟨m', hm'1, hm'2⟩ := ih (m + 1) hdist
        exact ⟨m', by omega, hm'2⟩

/-- Under fairness, a process eventually reaches `wait` or its
critical section. -/
theorem exists_wait_or_crit
    (hmover : ∀ i, run (i + 1) = nextState (mover i) (run i))
    (hfair : ∀ (p : Proc) (k : ℕ), ∃ m, k ≤ m ∧ mover m = p)
    (p : Proc) (k : ℕ) :
    ∃ m, k ≤ m ∧ (pcOf p (run m) = .wait ∨ pcOf p (run m) = .critical) :=
  exists_wait_or_crit_aux hmover hfair p (distToWait (pcOf p (run k))) k
    (Nat.le_refl _)

/-- If `p`'s flag stays up and the turn stays with the other process
`q = p.other` from time `k` on, then `q` cannot spin at its `wait`
(its guard needs `turn = p`), so `q`'s own moves walk it around the
program cycle to a `setTurn` move. -/
theorem exists_setTurn_move_aux
    (hmover : ∀ i, run (i + 1) = nextState (mover i) (run i))
    (hfair : ∀ (p : Proc) (k : ℕ), ∃ m, k ≤ m ∧ mover m = p)
    (p : Proc) {k : ℕ}
    (hflag : ∀ m, k ≤ m → flagOf p (run m) = true)
    (hturn : ∀ m, k ≤ m → (run m).turn = p.other) :
    ∀ (d m : ℕ), k ≤ m → distToSetTurn (pcOf p.other (run m)) ≤ d →
      ∃ m', m ≤ m' ∧ mover m' = p.other ∧
        pcOf p.other (run m') = .setTurn := by
  intro d
  induction d with
  | zero =>
      intro m _ hd
      have hpc : pcOf p.other (run m) = .setTurn :=
        eq_setTurn_of_distToSetTurn_eq_zero (Nat.le_zero.mp hd)
      obtain ⟨m', hm'1, hm'2, hm'3, -⟩ := exists_nextMove hmover hfair p.other m
      exact ⟨m', hm'1, hm'2, by rw [hm'3]; exact hpc⟩
  | succ d ih =>
      intro m hkm hd
      by_cases hst : pcOf p.other (run m) = .setTurn
      · obtain ⟨m', hm'1, hm'2, hm'3, -⟩ := exists_nextMove hmover hfair p.other m
        exact ⟨m', hm'1, hm'2, by rw [hm'3]; exact hst⟩
      · obtain ⟨m1, hm11, hm12, hm13, -⟩ := exists_nextMove hmover hfair p.other m
        have hdist : distToSetTurn (pcOf p.other (run (m1 + 1))) ≤ d := by
          have hlt : distToSetTurn (pcOf p.other (run (m1 + 1))) <
              distToSetTurn (pcOf p.other (run m1)) := by
            rw [pcOf_succ_of_mover hmover hm12]
            have e1 : flagOf p.other.other (run m1) = true := by
              rw [Proc.other_other]
              exact hflag m1 (by omega)
            have e2 : (run m1).turn = p.other := hturn m1 (by omega)
            rw [e1, e2]
            apply distToSetTurn_advance_lt
            rw [hm13]
            exact hst
          have hd' : distToSetTurn (pcOf p.other (run m1)) ≤ d + 1 := by
            rwa [hm13]
          omega
        obtain ⟨m', hm'1, hm'2, hm'3⟩ := ih (m1 + 1) (by omega) hdist
        exact ⟨m', by omega, hm'2, hm'3⟩

/-- A waiting process eventually enters its critical section.  Proof:
if it never entered, it would wait forever with its flag up.  If the
turn is ever in its favour, it stays so (only the other process's
`setTurn` moves can change the turn then, and they set it in its
favour), so its next move enters.  Otherwise the turn stays with the
other process, which is then walked to a `setTurn` move by
`exists_setTurn_move_aux`, and that move gives the turn to the
waiter: contradiction. -/
theorem exists_crit_of_wait
    (hmover : ∀ i, run (i + 1) = nextState (mover i) (run i))
    (hfair : ∀ (p : Proc) (k : ℕ), ∃ m, k ≤ m ∧ mover m = p)
    (hInv : ∀ k, Inv (run k))
    (p : Proc) {k : ℕ} (hk : pcOf p (run k) = .wait) :
    ∃ m, k ≤ m ∧ pcOf p (run m) = .critical := by
  by_contra hcon
  have hcon' : ∀ m, k ≤ m → pcOf p (run m) ≠ .critical :=
    fun m hm hpc => hcon ⟨m, hm, hpc⟩
  have hwait : ∀ m, k ≤ m → pcOf p (run m) = .wait := by
    intro m hm
    induction m, hm using Nat.le_induction with
    | base => exact hk
    | succ m hm ih =>
        by_cases hmv : mover m = p
        · have hnext : pcOf p (run (m + 1)) =
              advance p (pcOf p (run m)) (flagOf p.other (run m)) (run m).turn :=
            pcOf_succ_of_mover hmover hmv
          rw [ih, advance_wait] at hnext
          by_cases hc : flagOf p.other (run m) = true ∧ (run m).turn = p.other
          · rwa [ite_eq_left hc] at hnext
          · rw [ite_eq_right hc] at hnext
            exact absurd hnext (hcon' (m + 1) (by omega))
        · rw [pcOf_succ_of_mover_ne hmover hmv]
          exact ih
  have hflag : ∀ m, k ≤ m → flagOf p (run m) = true := by
    intro m hm
    exact (flagOf_of_inv (hInv m) p).mpr (by rw [hwait m hm]; simp [flagRegion])
  by_cases hturn : ∃ m, k ≤ m ∧ (run m).turn = p
  · obtain ⟨m0, hm0k, hm0t⟩ := hturn
    have hstay : ∀ m, m0 ≤ m → (run m).turn = p := by
      intro m hm
      induction m, hm using Nat.le_induction with
      | base => exact hm0t
      | succ m hm ih =>
          rw [turn_succ hmover]
          by_cases hst : pcOf (mover m) (run m) = .setTurn
          · rw [ite_eq_left hst]
            have hne : mover m ≠ p := by
              intro hpp
              rw [hpp, hwait m (by omega)] at hst
              simp at hst
            have e : mover m = p.other := Proc.eq_other_of_ne hne
            rw [e]
            exact Proc.other_other p
          · rw [ite_eq_right hst]
            exact ih
    obtain ⟨m1, hm1k, hm1p⟩ := hfair p m0
    have hnext : pcOf p (run (m1 + 1)) =
        advance p (pcOf p (run m1)) (flagOf p.other (run m1)) (run m1).turn :=
      pcOf_succ_of_mover hmover hm1p
    rw [hwait m1 (by omega), hstay m1 hm1k, advance_wait] at hnext
    rw [ite_eq_right (fun h => Proc.ne_other p h.2)] at hnext
    exact hcon' (m1 + 1) (by omega) hnext
  · have hturn' : ∀ m, k ≤ m → (run m).turn ≠ p :=
      fun m hm ht => hturn ⟨m, hm, ht⟩
    have hturnq : ∀ m, k ≤ m → (run m).turn = p.other :=
      fun m hm => Proc.eq_other_of_ne (hturn' m hm)
    obtain ⟨m', hm'k, hm'2, hm'3⟩ := exists_setTurn_move_aux hmover hfair p
      hflag hturnq (distToSetTurn (pcOf p.other (run k))) k (Nat.le_refl k)
      (Nat.le_refl _)
    have htp : (run (m' + 1)).turn = p := by
      rw [turn_succ hmover, hm'2, ite_eq_left hm'3]
      exact Proc.other_other p
    exact hturn' (m' + 1) (by omega) htp

/-- Under fairness, each process reaches its critical section from
any position. -/
theorem exists_critical
    (hmover : ∀ i, run (i + 1) = nextState (mover i) (run i))
    (hfair : ∀ (p : Proc) (k : ℕ), ∃ m, k ≤ m ∧ mover m = p)
    (hInv : ∀ k, Inv (run k))
    (p : Proc) (k : ℕ) :
    ∃ m, k ≤ m ∧ pcOf p (run m) = .critical := by
  obtain ⟨m, hkm, hwc⟩ := exists_wait_or_crit hmover hfair p k
  rcases hwc with hw | hc
  · obtain ⟨m', hm'1, hm'2⟩ := exists_crit_of_wait hmover hfair hInv p hw
    exact ⟨m', by omega, hm'2⟩
  · exact ⟨m, hkm, hc⟩

end Liveness

/-- Liveness of Peterson's algorithm: on every fair infinite run
from the initial state, each process is in its critical section
infinitely often (`□◇ cs0 ∧ □◇ cs1`). -/
theorem peterson_liveness {run : ℕ → State} (hr0 : run 0 = initial)
    (hrun : Cslib.LTS.OmegaRun (lts := peterson) run)
    (hfair : Satisfies valuation run fairFormula) :
    Satisfies valuation run liveFormula := by
  obtain ⟨mover, hmover⟩ := mover_of_omegaRun hrun
  have hInv : ∀ k, Inv (run k) :=
    Cslib.LTS.forall_state_of_invariant hrun (by rw [hr0]; exact inv_initial)
      (fun _ _ hs hstep => inv_step hs hstep)
  have hfair' : ∀ (p : Proc) (k : ℕ), ∃ m, k ≤ m ∧ mover m = p :=
    fun p k => fair_of_ltl hmover hfair p k
  have key : ∀ (p : Proc) (k : ℕ), ∃ m, k ≤ m ∧ pcOf p (run m) = .critical :=
    fun p k => exists_critical hmover hfair' hInv p k
  have live_of : ∀ (p : Proc) (a : Atom),
      (∀ s, pcOf p s = .critical → valuation s a) →
      Satisfies valuation run
        (Formula.always (Formula.eventually (.atom a))) := by
    intro p a ha
    rw [Satisfies.always_iff]
    intro k
    rw [satisfiesAt_eventually]
    obtain ⟨m, hkm, hm⟩ := key p k
    refine ⟨m - k, ?_⟩
    rw [Satisfies.atomAt_iff]
    apply ha
    have e : k + (m - k) = m := by omega
    rwa [e]
  have hlive : Satisfies valuation run
      (.and (Formula.always (Formula.eventually (.atom .cs0)))
        (Formula.always (Formula.eventually (.atom .cs1)))) :=
    ⟨live_of .p0 .cs0 (fun _ hs => hs), live_of .p1 .cs1 (fun _ hs => hs)⟩
  exact hlive

/-- Response form of liveness: a process that has raised its flag
eventually reaches its critical section.  This is immediate from
`peterson_liveness`, which gives a critical-section visit after
every position. -/
theorem peterson_response {run : ℕ → State} (hr0 : run 0 = initial)
    (hrun : Cslib.LTS.OmegaRun (lts := peterson) run)
    (hfair : Satisfies valuation run fairFormula) :
    Satisfies valuation run
        (Formula.always (Formula.imp (.atom .flag0)
          (Formula.eventually (.atom .cs0)))) ∧
      Satisfies valuation run
        (Formula.always (Formula.imp (.atom .flag1)
          (Formula.eventually (.atom .cs1)))) := by
  have hlive := peterson_liveness hr0 hrun hfair
  have hlive' : Satisfies valuation run
      (.and (Formula.always (Formula.eventually (.atom .cs0)))
        (Formula.always (Formula.eventually (.atom .cs1)))) := hlive
  obtain ⟨hl0, hl1⟩ := Satisfies.and_iff.mp hlive'
  constructor
  · rw [Satisfies.always_iff] at hl0 ⊢
    intro k
    change Satisfies valuation (Semantics.shiftSeq run k)
      (Formula.imp (.atom .flag0) (Formula.eventually (.atom .cs0)))
    rw [Satisfies.imp_iff]
    intro _
    exact hl0 k
  · rw [Satisfies.always_iff] at hl1 ⊢
    intro k
    change Satisfies valuation (Semantics.shiftSeq run k)
      (Formula.imp (.atom .flag1) (Formula.eventually (.atom .cs1)))
    rw [Satisfies.imp_iff]
    intro _
    exact hl1 k

#print axioms Cslib.LTL.temporal_induction
#print axioms Cslib.LTL.Satisfies.always_imp
#print axioms peterson_safety
#print axioms peterson_liveness

end Cslib.LTL.PetersonTests
