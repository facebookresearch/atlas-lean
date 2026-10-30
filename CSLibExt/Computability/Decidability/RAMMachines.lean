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

/-- A **RAM addressing mode**: immediate (the literal value `n` itself),
direct (the contents of register `n`), or indirect (the contents of the
register whose index is the contents of register `n`, i.e. `regs (regs n)`).
The earlier version of this file mislabelled the immediate mode `dir` and
the direct mode `ind`, and had no indirect mode; the three modes below are
the Aho–Hopcroft–Ullman modes.
Source: Aho–Hopcroft–Ullman, *The Design and Analysis of Computer Algorithms*, 1974, §1.2. -/
inductive RAMAddr where
  | imm : ℕ → RAMAddr
  | dir : ℕ → RAMAddr
  | ind : ℕ → RAMAddr

/-- A **RAM destination**: where a `store` writes the accumulator — either a
statically named register, or the register whose index is the contents of a
register (indirect store). The immediate mode is not a valid store
destination.
Source: Aho–Hopcroft–Ullman, *The Design and Analysis of Computer Algorithms*, 1974, §1.2. -/
inductive RAMDest where
  | dir : ℕ → RAMDest
  | ind : ℕ → RAMDest

/-- A **RAM instruction**: load, store, add, saturating subtract, unconditional
jump, jump-if-accumulator-zero, and halt. `store` takes a `RAMDest`, so
both direct and indirect stores are available.
Source: Aho–Hopcroft–Ullman, *The Design and Analysis of Computer Algorithms*, 1974, §1.2. -/
inductive RAMInstr where
  | load : RAMAddr → RAMInstr
  | store : RAMDest → RAMInstr
  | add : RAMAddr → RAMInstr
  | sub : RAMAddr → RAMInstr
  | jump : ℕ → RAMInstr
  | jz : ℕ → RAMInstr
  | halt : RAMInstr

/-- A **RAM state**: program counter, accumulator, and register contents.
Source: Aho–Hopcroft–Ullman, *The Design and Analysis of Computer Algorithms*, 1974, §1.2. -/
structure RAMState where
  /-- The program counter. -/
  pc : ℕ
  /-- The accumulator. -/
  acc : ℕ
  /-- The register contents. -/
  regs : ℕ → ℕ

/-- Resolve a RAM operand to a value in the given state: immediate is the
literal, direct is the register contents, indirect is two register
dereferences.
Source: Aho–Hopcroft–Ullman, *The Design and Analysis of Computer Algorithms*, 1974, §1.2. -/
def ramResolve (s : RAMState) (a : RAMAddr) : ℕ :=
  match a with
  | .imm n => n
  | .dir r => s.regs r
  | .ind r => s.regs (s.regs r)

/-- Resolve a RAM store destination to the register index it writes: direct
is the named register, indirect is the contents of the named register.
Source: Aho–Hopcroft–Ullman, *The Design and Analysis of Computer Algorithms*, 1974, §1.2. -/
def ramDestIndex (s : RAMState) (d : RAMDest) : ℕ :=
  match d with
  | .dir r => r
  | .ind r => s.regs r

/-- One step of a RAM machine. The step is sticky at halting states
(program counter past the end of the program, or a `halt` instruction),
so iteration never fails.
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

/-- The initial RAM state on the given inputs (in registers `0, 1, …`).
Source: Aho–Hopcroft–Ullman, *The Design and Analysis of Computer Algorithms*, 1974, §1.2. -/
def ramInit (inputs : List ℕ) : RAMState :=
  { pc := 0, acc := 0, regs := fun i ↦ inputs.getD i 0 }

/-- Bounded execution of a RAM machine: `t` steps from the initial state.
Source: Aho–Hopcroft–Ullman, *The Design and Analysis of Computer Algorithms*, 1974, §1.2. -/
def ramExecN (prog : List RAMInstr) (t : ℕ) (s : RAMState) : RAMState :=
  (ramStep prog)^[t] s

/-- The output of a RAM machine: the accumulator once halted, undefined
while still running.
Source: Aho–Hopcroft–Ullman, *The Design and Analysis of Computer Algorithms*, 1974, §1.2. -/
def ramEval (prog : List RAMInstr) (inputs : List ℕ) : Part ℕ :=
  Nat.rfindOpt fun t ↦
    let s := ramExecN prog t (ramInit inputs)
    if prog.length ≤ s.pc then some s.acc else Option.none

/-- **A RAM step is sticky at halting states**: past the end of the program
the state does not change (a `halt` instruction jumps to the end, so it is
sticky too).
Source: Aho–Hopcroft–Ullman, *The Design and Analysis of Computer Algorithms*, 1974, §1.2. -/
theorem ramStep_sticky {prog : List RAMInstr} {s : RAMState}
    (h : prog.length ≤ s.pc) : ramStep prog s = s := by
  unfold ramStep
  rw [List.getElem?_eq_none_iff.2 h]

/-- **Bounded execution is stable once halted**: one more step changes nothing.
Source: Aho–Hopcroft–Ullman, *The Design and Analysis of Computer Algorithms*, 1974, §1.2. -/
theorem ramExecN_stable {prog : List RAMInstr} {t : ℕ} {s : RAMState}
    (h : prog.length ≤ (ramExecN prog t s).pc) :
    ramExecN prog (t + 1) s = ramExecN prog t s := by
  simp only [ramExecN, Function.iterate_succ_apply']
  exact ramStep_sticky h

/-- **Bounded execution stays at its halted value.**
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

/-- **Output membership for RAM machines**: if the machine has halted by step
`t` with accumulator `y`, then `y` is the evaluation result.
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

/-- A predicate is **RAM decidable** when a RAM machine computes its
characteristic function.
Source: Aho–Hopcroft–Ullman, *The Design and Analysis of Computer Algorithms*, 1974, §1.2. -/
def RAMDecidable (P : ℕ → Prop) : Prop :=
  ∃ prog : List RAMInstr, ∀ n, ramEval prog [n] = charFun P n

end Cslib.Decidability
