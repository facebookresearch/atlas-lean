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
# RAM machines

Random-access machines (A. V. Aho, J. E. Hopcroft, and J. D. Ullman, *The
Design and Analysis of Computer Algorithms*, Addison-Wesley, 1974, §1.2)
have an accumulator, a program counter, and an unbounded array of registers,
with direct and indirect addressing. They are one of the standard models in
the Church–Turing equivalence; the equivalence with Turing machines is
registered as a wanted theorem in
`WantedExt/TheoryOfComputation/RAMMachineEquivalence.lean`.
-/

set_option autoImplicit false

namespace Cslib.Decidability

/-- **RAM addressing mode.** An addressing mode of a random-access machine specifies an operand
by a natural number $n$ in one of three ways: immediate (the operand is the value $n$ itself),
direct (the operand is the contents of register $n$), or indirect (the operand is the contents
of the register whose index is the contents of register $n$).

Source: Aho–Hopcroft–Ullman, *The Design and Analysis of Computer Algorithms*, 1974, §1.2. -/
inductive RAMAddr where
  | imm : ℕ → RAMAddr
  | dir : ℕ → RAMAddr
  | ind : ℕ → RAMAddr

/-- **RAM store destination.** A store destination of a random-access machine names, by a
natural number $n$, the register into which the accumulator is stored: either register $n$
itself (direct) or the register whose index is the contents of register $n$ (indirect).

An immediate operand is not a valid store destination.

Source: Aho–Hopcroft–Ullman, *The Design and Analysis of Computer Algorithms*, 1974, §1.2. -/
inductive RAMDest where
  | dir : ℕ → RAMDest
  | ind : ℕ → RAMDest

/-- **RAM instruction.** An instruction of a random-access machine is one of the following: load
an operand into the accumulator; store the accumulator into a store destination; add an operand
to the accumulator; subtract an operand from the accumulator, truncating at $0$; jump to
instruction $q$; jump to instruction $q$ if the accumulator is $0$; halt. Here an operand is given
by a RAM addressing mode, a store destination is a RAM store destination, and the jump target $q$
is a natural number.

Source: Aho–Hopcroft–Ullman, *The Design and Analysis of Computer Algorithms*, 1974, §1.2. -/
inductive RAMInstr where
  | load : RAMAddr → RAMInstr
  | store : RAMDest → RAMInstr
  | add : RAMAddr → RAMInstr
  | sub : RAMAddr → RAMInstr
  | jump : ℕ → RAMInstr
  | jz : ℕ → RAMInstr
  | halt : RAMInstr

/-- **RAM state.** A state of a random-access machine consists of a program counter in
$\mathbb{N}$, an accumulator value in $\mathbb{N}$, and register contents, a function
$\mathbb{N} \to \mathbb{N}$ giving the contents of each register.

Source: Aho–Hopcroft–Ullman, *The Design and Analysis of Computer Algorithms*, 1974, §1.2. -/
structure RAMState where
  /-- The program counter. -/
  pc : ℕ
  /-- The accumulator. -/
  acc : ℕ
  /-- The register contents. -/
  regs : ℕ → ℕ

/-- **Value of a RAM operand.** In a RAM state with register contents $r$, an operand resolves to
a natural number: the immediate operand $n$ resolves to $n$ itself, the direct operand $n$ to
the contents $r(n)$ of register $n$, and the indirect operand $n$ to $r(r(n))$.

Source: Aho–Hopcroft–Ullman, *The Design and Analysis of Computer Algorithms*, 1974, §1.2. -/
def ramResolve (s : RAMState) (a : RAMAddr) : ℕ :=
  match a with
  | .imm n => n
  | .dir r => s.regs r
  | .ind r => s.regs (s.regs r)

/-- **Register written by a RAM store.** In a RAM state with register contents $r$, a store
destination resolves to a register index: the direct destination $n$ resolves to $n$, and the
indirect destination $n$ resolves to the contents $r(n)$ of register $n$.

Source: Aho–Hopcroft–Ullman, *The Design and Analysis of Computer Algorithms*, 1974, §1.2. -/
def ramDestIndex (s : RAMState) (d : RAMDest) : ℕ :=
  match d with
  | .dir r => r
  | .ind r => s.regs r

/-- **One step of a RAM machine.** Let $P = (P_0, \dots, P_{\ell-1})$ be a program of length
$\ell$ and $s$ a state with program counter $p$, accumulator $a$ and register contents $r$. If
$p \ge \ell$, the step leaves $s$ unchanged. Otherwise it executes $P_p$, where $v$ denotes
the value of the instruction's operand in $s$: a load sets the accumulator to $v$, an add sets
it to $a + v$, a subtract sets it to $\max(a - v, 0)$, and a store writes $a$ into the
register that its destination resolves to in $s$; each of these also increases the program
counter by $1$. A jump to $q$ sets the program counter to $q$; a jump-if-zero to $q$ sets it
to $q$ if $a = 0$ and to $p + 1$ otherwise; a halt sets it to $\ell$. Nothing else changes.

In particular, once the program counter is at least $\ell$ (for instance after a halt), every
further step leaves the state unchanged.

Source: Aho–Hopcroft–Ullman, *The Design and Analysis of Computer Algorithms*, 1974, §1.2. -/
def ramStep (prog : List RAMInstr) (s : RAMState) : RAMState :=
  match prog[s.pc]? with
  | none => s
  | some (.load a) => { s with pc := s.pc + 1, acc := ramResolve s a }
  | some (.store d) =>
      let regs' := Function.update s.regs (ramDestIndex s d) s.acc
      { s with pc := s.pc + 1, regs := regs' }
  | some (.add a) => { s with pc := s.pc + 1, acc := s.acc + ramResolve s a }
  | some (.sub a) => { s with pc := s.pc + 1, acc := s.acc - ramResolve s a }
  | some (.jump q) => { s with pc := q }
  | some (.jz q) => { s with pc := if s.acc = 0 then q else s.pc + 1 }
  | some .halt => { s with pc := prog.length }

/-- **Initial RAM state.** The initial state on inputs $x_0, \dots, x_{k-1}$ has program counter
$0$ and accumulator $0$; register $i$ holds $x_i$ for $i < k$, and every other register holds
$0$.

Source: Aho–Hopcroft–Ullman, *The Design and Analysis of Computer Algorithms*, 1974, §1.2. -/
def ramInit (inputs : List ℕ) : RAMState :=
  { pc := 0, acc := 0, regs := fun i ↦ inputs.getD i 0 }

/-- **Bounded execution of a RAM machine.** For a program $P$, a natural number $t$ and a state
$s$, the state after $t$ steps of $P$ from $s$ is obtained by applying one step of $P$ to $s$
exactly $t$ times.

Source: Aho–Hopcroft–Ullman, *The Design and Analysis of Computer Algorithms*, 1974, §1.2. -/
def ramExecN (prog : List RAMInstr) (t : ℕ) (s : RAMState) : RAMState :=
  (ramStep prog)^[t] s

/-- **Output of a RAM machine.** Let $P$ be a program of length $\ell$ and $x_0, \dots, x_{k-1}$
inputs. Run $P$ from the initial state on these inputs. If for some $t$ the program counter
after $t$ steps is at least $\ell$, the output of $P$ on these inputs is the accumulator after
the least such number of steps; otherwise the output is undefined.

Source: Aho–Hopcroft–Ullman, *The Design and Analysis of Computer Algorithms*, 1974, §1.2. -/
def ramEval (prog : List RAMInstr) (inputs : List ℕ) : Part ℕ :=
  Nat.rfindOpt fun t ↦
    let s := ramExecN prog t (ramInit inputs)
    if prog.length ≤ s.pc then some s.acc else Option.none

/-- **A RAM step is sticky at halting states.** If the program counter of a state $s$ is at
least the length of a program $P$, then one step of $P$ leaves $s$ unchanged.

A halt instruction sets the program counter to the length of the program, so once a halt has
been executed the state no longer changes.

Source: Aho–Hopcroft–Ullman, *The Design and Analysis of Computer Algorithms*, 1974, §1.2. -/
theorem ramStep_sticky {prog : List RAMInstr} {s : RAMState}
    (h : prog.length ≤ s.pc) : ramStep prog s = s := by
  unfold ramStep
  rw [List.getElem?_eq_none_iff.2 h]

/-- **RAM execution is stable once halted.** Let $P$ be a program of length $\ell$, $s$ a state
and $t$ a natural number. If the program counter after $t$ steps of $P$ from $s$ is at least
$\ell$, then the state after $t + 1$ steps of $P$ from $s$ equals the state after $t$ steps.

Source: Aho–Hopcroft–Ullman, *The Design and Analysis of Computer Algorithms*, 1974, §1.2. -/
theorem ramExecN_stable {prog : List RAMInstr} {t : ℕ} {s : RAMState}
    (h : prog.length ≤ (ramExecN prog t s).pc) :
    ramExecN prog (t + 1) s = ramExecN prog t s := by
  simp only [ramExecN, Function.iterate_succ_apply']
  exact ramStep_sticky h

/-- **RAM execution stays at its halted state.** Let $P$ be a program of length $\ell$, $s$ a
state and $t_1 \le t_2$ natural numbers. If the program counter after $t_1$ steps of $P$ from
$s$ is at least $\ell$, then the state after $t_2$ steps of $P$ from $s$ equals the state after
$t_1$ steps.

Source: Aho–Hopcroft–Ullman, *The Design and Analysis of Computer Algorithms*, 1974, §1.2. -/
theorem ramExecN_eq_of_halted {prog : List RAMInstr} {t₁ t₂ : ℕ} {s : RAMState}
    (h : prog.length ≤ (ramExecN prog t₁ s).pc) (hle : t₁ ≤ t₂) :
    ramExecN prog t₂ s = ramExecN prog t₁ s := by
  obtain ⟨k, rfl⟩ : ∃ k, t₂ = t₁ + k := ⟨t₂ - t₁, by omega⟩
  clear hle
  induction k with
  | zero => simp
  | succ k ih =>
    have hstable : ramExecN prog (t₁ + k + 1) s =
        ramExecN prog (t₁ + k) s := by
      apply ramExecN_stable
      rw [ih]; exact h
    rw [show t₁ + (k + 1) = t₁ + k + 1 from by omega, hstable, ih]

/-- **Output membership for RAM machines.** Let $P$ be a program of length $\ell$, let
$x_0, \dots, x_{k-1}$ be inputs and let $t$ and $y$ be natural numbers. If, after $t$ steps of
$P$ from the initial state on these inputs, the program counter is at least $\ell$ and the
accumulator equals $y$, then the output of $P$ on these inputs is defined and equals $y$.

Source: Aho–Hopcroft–Ullman, *The Design and Analysis of Computer Algorithms*, 1974, §1.2. -/
theorem mem_ramEval_of_halted {prog : List RAMInstr} {inputs : List ℕ} {y : ℕ}
    {t : ℕ}
    (hhalt : prog.length ≤ (ramExecN prog t (ramInit inputs)).pc)
    (hout : (ramExecN prog t (ramInit inputs)).acc = y) :
    y ∈ ramEval prog inputs := by
  have hmono : ∀ {a m n : ℕ}, m ≤ n →
      a ∈ (let s := ramExecN prog m (ramInit inputs)
        if prog.length ≤ s.pc then some s.acc else Option.none) →
      a ∈ (let s := ramExecN prog n (ramInit inputs)
        if prog.length ≤ s.pc then some s.acc else Option.none) := by
    intro a m n hmn ham
    dsimp only at ham ⊢
    by_cases hm : prog.length ≤ (ramExecN prog m (ramInit inputs)).pc
    · rw [ite_eq_left hm] at ham
      obtain rfl : (ramExecN prog m (ramInit inputs)).acc = a :=
        Option.some_inj.1 (Option.mem_def.1 ham)
      rw [ite_eq_left (by
        rw [ramExecN_eq_of_halted hm hmn]; exact hm)]
      rw [ramExecN_eq_of_halted hm hmn]
      exact Option.mem_def.2 rfl
    · rw [ite_eq_right hm] at ham
      exact absurd ham (by simp)
  apply (Nat.rfindOpt_mono hmono).2 ⟨t, ?_⟩
  dsimp only
  rw [ite_eq_left hhalt, hout]
  exact Option.mem_def.2 rfl

/-- **RAM-decidable predicate.** A predicate $P$ on the natural numbers is RAM decidable when
there is a RAM program, a finite list of RAM instructions, such that for every natural number $n$
the program, started with $n$ in register $0$ and with the accumulator, the program counter and
every other register at $0$, halts (its program counter reaches or passes the end of the
program) with $1$ in the accumulator if $P(n)$ holds and with $0$ in the accumulator otherwise;
that is, its RAM evaluation on the single input $n$ equals the characteristic function of $P$
at $n$.

Source: Aho–Hopcroft–Ullman, *The Design and Analysis of Computer Algorithms*, 1974, §1.2. -/
def RAMDecidable (P : ℕ → Prop) : Prop :=
  ∃ prog : List RAMInstr, ∀ n, ramEval prog [n] = charFun P n

end Cslib.Decidability
