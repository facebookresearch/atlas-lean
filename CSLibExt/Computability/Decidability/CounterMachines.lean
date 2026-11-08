/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.Computability.Decidability.TuringReducible

@[expose] public section

/-!
# Counter machines

Counter machines (Minsky machines: M. L. Minsky, *Computation: Finite and
Infinite Machines*, Prentice-Hall, 1967, §11; Shepherdson–Sturgis, "Computability
of recursive functions", *Journal of the ACM* 10 (1963), 217–255) have a finite
list of instructions over registers holding natural numbers: increment,
saturating decrement, and jump-if-zero. They are one of the standard models
in the Church–Turing equivalence; the equivalence with Turing machines is
registered as a wanted theorem in
`WantedExt/TheoryOfComputation/CounterMachineEquivalence.lean`.
-/

set_option autoImplicit false

namespace Cslib.Decidability

/-- A **counter-machine instruction**: increment a register, decrement a
register (saturating at `0`), or jump if a register is zero.
Source: Minsky, *Computation: Finite and Infinite Machines*, 1967, §11. -/
inductive CounterInstr where
  | inc : ℕ → CounterInstr
  | dec : ℕ → CounterInstr
  | jz : ℕ → ℕ → CounterInstr

/-- A **counter-machine state**: program counter plus register contents.
Source: Minsky, *Computation: Finite and Infinite Machines*, 1967, §11. -/
structure CounterState where
  /-- The program counter. -/
  pc : ℕ
  /-- The register contents. -/
  regs : ℕ → ℕ

/-- One step of a counter machine. The step is sticky at halting states
(program counter past the end of the program), so iteration never fails.
Source: Minsky, *Computation: Finite and Infinite Machines*, 1967, §11. -/
def counterStep (prog : List CounterInstr) (s : CounterState) : CounterState :=
  match prog[s.pc]? with
  | none => s
  | some (.inc r) =>
      { pc := s.pc + 1, regs := Function.update s.regs r (s.regs r + 1) }
  | some (.dec r) =>
      { pc := s.pc + 1, regs := Function.update s.regs r (s.regs r - 1) }
  | some (.jz r q) =>
      { pc := if s.regs r = 0 then q else s.pc + 1, regs := s.regs }

/-- The initial counter-machine state on the given inputs (in registers `0, 1, …`).
Source: Minsky, *Computation: Finite and Infinite Machines*, 1967, §11. -/
def counterInit (inputs : List ℕ) : CounterState :=
  { pc := 0, regs := fun i ↦ inputs.getD i 0 }

/-- Bounded execution of a counter machine: `t` steps from the initial state.
Source: Minsky, *Computation: Finite and Infinite Machines*, 1967, §11. -/
def counterExecN (prog : List CounterInstr) (t : ℕ) (s : CounterState) : CounterState :=
  (counterStep prog)^[t] s

/-- The output of a counter machine: the contents of register `0` once halted,
undefined while still running.
Source: Minsky, *Computation: Finite and Infinite Machines*, 1967, §11. -/
def counterEval (prog : List CounterInstr) (inputs : List ℕ) : Part ℕ :=
  Nat.rfindOpt fun t ↦
    let s := counterExecN prog t (counterInit inputs)
    if prog.length ≤ s.pc then some (s.regs 0) else Option.none

/-- **A counter step is sticky at halting states**: past the end of the
program the state does not change.
Source: Minsky, *Computation: Finite and Infinite Machines*, 1967, §11. -/
theorem counterStep_sticky {prog : List CounterInstr} {s : CounterState}
    (h : prog.length ≤ s.pc) : counterStep prog s = s := by
  unfold counterStep
  rw [List.getElem?_eq_none_iff.2 h]

/-- **Bounded execution is stable once halted**: one more step changes nothing.
Source: Minsky, *Computation: Finite and Infinite Machines*, 1967, §11. -/
theorem counterExecN_stable {prog : List CounterInstr} {t : ℕ} {s : CounterState}
    (h : prog.length ≤ (counterExecN prog t s).pc) :
    counterExecN prog (t + 1) s = counterExecN prog t s := by
  simp only [counterExecN, Function.iterate_succ_apply']
  exact counterStep_sticky h

/-- **Bounded execution stays at its halted value.**
Source: Minsky, *Computation: Finite and Infinite Machines*, 1967, §11. -/
theorem counterExecN_eq_of_halted {prog : List CounterInstr} {t₁ t₂ : ℕ}
    {s : CounterState}
    (h : prog.length ≤ (counterExecN prog t₁ s).pc) (hle : t₁ ≤ t₂) :
    counterExecN prog t₂ s = counterExecN prog t₁ s := by
  obtain ⟨k, rfl⟩ : ∃ k, t₂ = t₁ + k := ⟨t₂ - t₁, by omega⟩
  clear hle
  induction k with
  | zero => simp
  | succ k ih =>
    have hstable : counterExecN prog (t₁ + k + 1) s =
        counterExecN prog (t₁ + k) s := by
      apply counterExecN_stable
      rw [ih]; exact h
    rw [show t₁ + (k + 1) = t₁ + k + 1 from by omega, hstable, ih]

/-- **Output membership for counter machines**: if the machine has halted by
step `t` with output `y` in register `0`, then `y` is the evaluation result.
Source: Minsky, *Computation: Finite and Infinite Machines*, 1967, §11. -/
theorem mem_counterEval_of_halted {prog : List CounterInstr} {inputs : List ℕ}
    {y : ℕ} {t : ℕ}
    (hhalt : prog.length ≤ (counterExecN prog t (counterInit inputs)).pc)
    (hout : (counterExecN prog t (counterInit inputs)).regs 0 = y) :
    y ∈ counterEval prog inputs := by
  have hmono : ∀ {a m n : ℕ}, m ≤ n →
      a ∈ (let s := counterExecN prog m (counterInit inputs)
        if prog.length ≤ s.pc then some (s.regs 0) else Option.none) →
      a ∈ (let s := counterExecN prog n (counterInit inputs)
        if prog.length ≤ s.pc then some (s.regs 0) else Option.none) := by
    intro a m n hmn ham
    dsimp only at ham ⊢
    by_cases hm : prog.length ≤ (counterExecN prog m (counterInit inputs)).pc
    · rw [ite_eq_left hm] at ham
      obtain rfl : (counterExecN prog m (counterInit inputs)).regs 0 = a :=
        Option.some_inj.1 (Option.mem_def.1 ham)
      rw [ite_eq_left (by
        rw [counterExecN_eq_of_halted hm hmn]; exact hm)]
      rw [counterExecN_eq_of_halted hm hmn]
      exact Option.mem_def.2 rfl
    · rw [ite_eq_right hm] at ham
      exact absurd ham (by simp)
  apply (Nat.rfindOpt_mono hmono).2 ⟨t, ?_⟩
  dsimp only
  rw [ite_eq_left hhalt, hout]
  exact Option.mem_def.2 rfl

/-- A predicate is **counter-machine decidable** when a counter machine
computes its characteristic function.
Source: Minsky, *Computation: Finite and Infinite Machines*, 1967, §11. -/
def CounterDecidable (P : ℕ → Prop) : Prop :=
  ∃ prog : List CounterInstr, ∀ n, counterEval prog [n] = charFun P n

end Cslib.Decidability
