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

/-- **Counter-machine instructions.** A counter-machine instruction is one of: increment register
$r$, decrement register $r$, or jump to instruction $q$ if register $r$ is zero, where the
register index $r$ and the jump target $q$ are natural numbers.

Decrementing a register that holds $0$ leaves it at $0$.

Source: Minsky, *Computation: Finite and Infinite Machines*, 1967, §11. -/
inductive CounterInstr where
  | inc : ℕ → CounterInstr
  | dec : ℕ → CounterInstr
  | jz : ℕ → ℕ → CounterInstr

/-- **Counter-machine states.** A counter-machine state consists of a program counter, which is a
natural number, and the register contents, a function assigning a natural number to every
register index $i \in \mathbb{N}$.

Source: Minsky, *Computation: Finite and Infinite Machines*, 1967, §11. -/
structure CounterState where
  /-- The program counter. -/
  pc : ℕ
  /-- The register contents. -/
  regs : ℕ → ℕ

/-- **One step of a counter machine.** Let $p$ be a counter-machine program, a list of
instructions indexed from $0$, and let $s$ be a state with program counter $c$. If $c$ is at
least the length of $p$ (the machine has halted), the step leaves $s$ unchanged. Otherwise it
executes instruction $c$ of $p$: increment register $r$ adds $1$ to register $r$ and sets the
program counter to $c + 1$; decrement register $r$ subtracts $1$ from register $r$ if it is
positive, leaves it at $0$ otherwise, and sets the program counter to $c + 1$; jump to $q$ if
register $r$ is zero leaves the registers unchanged and sets the program counter to $q$ if
register $r$ holds $0$ and to $c + 1$ otherwise.

Because halted states are fixed, the step can be iterated any number of times.

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

/-- **Initial state of a counter machine.** The initial counter-machine state on a list of inputs
$x_0, \dots, x_{k-1}$ has program counter $0$, register $i$ holding $x_i$ for each $i < k$, and
every other register holding $0$.

Source: Minsky, *Computation: Finite and Infinite Machines*, 1967, §11. -/
def counterInit (inputs : List ℕ) : CounterState :=
  { pc := 0, regs := fun i ↦ inputs.getD i 0 }

/-- **Bounded execution of a counter machine.** For a counter-machine program $p$, a natural
number $t$ and a state $s$, the execution of $p$ for $t$ steps from $s$ is the state obtained from
$s$ by applying $t$ single steps of $p$.

Source: Minsky, *Computation: Finite and Infinite Machines*, 1967, §11. -/
def counterExecN (prog : List CounterInstr) (t : ℕ) (s : CounterState) : CounterState :=
  (counterStep prog)^[t] s

/-- **Output of a counter machine.** The output of a counter-machine program $p$ on a list of
inputs is the partial natural number obtained as follows: run $p$ from the initial state on those
inputs; if for some number $t$ of steps the program counter is at least the length of $p$ (the
machine has halted), the output is the content of register $0$ after the least such $t$; if no
such $t$ exists, the output is undefined.

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

/-- **Counter-machine execution is stable once halted.** Let $p$ be a counter-machine program,
$s$ a state and $t$ a natural number. If the state reached from $s$ after $t$ steps of $p$ has
program counter at least the length of $p$, then the state reached from $s$ after $t + 1$ steps
equals the state reached after $t$ steps.

Source: Minsky, *Computation: Finite and Infinite Machines*, 1967, §11. -/
theorem counterExecN_stable {prog : List CounterInstr} {t : ℕ} {s : CounterState}
    (h : prog.length ≤ (counterExecN prog t s).pc) :
    counterExecN prog (t + 1) s = counterExecN prog t s := by
  simp only [counterExecN, Function.iterate_succ_apply']
  exact counterStep_sticky h

/-- **Counter-machine execution is constant after halting.** Let $p$ be a counter-machine
program, $s$ a state, and $t_1 \le t_2$ natural numbers. If the state reached from $s$ after
$t_1$ steps of $p$ has program counter at least the length of $p$, then the state reached from $s$
after $t_2$ steps equals the state reached after $t_1$ steps.

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

/-- **Output membership for counter machines.** Let $P$ be a counter-machine program, let $x$ be
a list of natural-number inputs, and let $t$ and $y$ be natural numbers. If the state reached
after $t$ steps of $P$ from the initial state on $x$ has program counter at least the length
of $P$ (so the machine has halted) and register $0$ holds $y$ in that state, then the output
of $P$ on $x$ is defined and equals $y$.

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

/-- **Counter-machine decidable predicates.** A predicate $P$ on the natural numbers is
counter-machine decidable when some counter-machine program computes its characteristic
function: for every natural number $n$, the output of the program on the single input $n$ is
defined and equals $1$ if $P(n)$ holds and $0$ otherwise.

Source: Minsky, *Computation: Finite and Infinite Machines*, 1967, §11. -/
def CounterDecidable (P : ℕ → Prop) : Prop :=
  ∃ prog : List CounterInstr, ∀ n, counterEval prog [n] = charFun P n

end Cslib.Decidability
