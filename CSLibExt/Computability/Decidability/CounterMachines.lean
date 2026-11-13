/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.Computability.Decidability.TuringReducible
public import Cslib.Computability.URM.Execution

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

## Relation to upstream URM

Configurations, input and output follow CSLib's unlimited register machines
(`Cslib.URM`, the Shepherdson–Sturgis model): `CounterState.equivURM` identifies
`CounterState` with `Cslib.URM.State`, `counterInit` is `URM.State.init`, halting
(program counter past the end) is `URM.State.isHalted`, and the output in register
`0` is `URM.Regs.output`. The instruction sets differ, so programs do not
translate instruction by instruction: `inc r` is URM `S r`
(`urmStep_of_counterStep_inc`), and `jz r q` is URM `J r z q` against any register
`z` holding `0` (`urmStep_of_counterStep_jz`), but Minsky's saturating `dec r` has
no URM counterpart (URM has zero, successor, transfer and jump-if-equal), and URM
`T` and `J` with two arbitrary registers have no counter counterpart. The
execution here is a total, sticky step function iterated by `counterExecN`, where
upstream uses the step relation `URM.Step`. `CounterDecidable` is characterized by
bounded runs in `counterDecidable_iff`.
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

/-- **Evaluation results are halted outputs**: `y` is the result of a counter
machine exactly when some bounded run has halted with `y` in register `0`.
Source: Minsky, *Computation: Finite and Infinite Machines*, 1967, §11. -/
theorem mem_counterEval_iff {prog : List CounterInstr} {inputs : List ℕ} {y : ℕ} :
    y ∈ counterEval prog inputs ↔ ∃ t,
      prog.length ≤ (counterExecN prog t (counterInit inputs)).pc ∧
        (counterExecN prog t (counterInit inputs)).regs 0 = y := by
  refine ⟨fun h ↦ ?_, fun ⟨t, hhalt, hout⟩ ↦ mem_counterEval_of_halted hhalt hout⟩
  obtain ⟨t, ht⟩ := Nat.rfindOpt_spec h
  dsimp only at ht
  by_cases hh : prog.length ≤ (counterExecN prog t (counterInit inputs)).pc
  · rw [ite_eq_left hh] at ht
    exact ⟨t, hh, Option.some_inj.1 (Option.mem_def.1 ht)⟩
  · rw [ite_eq_right hh] at ht
    exact absurd ht (by simp)

open Classical in
/-- **Counter-machine decidability by bounded runs**: `P` is counter-machine
decidable exactly when one program, on every input `n`, halts after finitely many
steps with `1` in register `0` if `P n` holds and `0` otherwise.
Source: Minsky, *Computation: Finite and Infinite Machines*, 1967, §11. -/
theorem counterDecidable_iff {P : ℕ → Prop} :
    CounterDecidable P ↔ ∃ prog : List CounterInstr, ∀ n, ∃ t,
      prog.length ≤ (counterExecN prog t (counterInit [n])).pc ∧
        (counterExecN prog t (counterInit [n])).regs 0 = if P n then 1 else 0 := by
  have key : ∀ (prog : List CounterInstr) (n : ℕ),
      counterEval prog [n] = charFun P n ↔ (if P n then 1 else 0) ∈ counterEval prog [n] := by
    intro prog n
    simp only [charFun]
    exact Part.eq_some_iff
  simp only [CounterDecidable, key, mem_counterEval_iff]

/-! ### Relation to upstream URM configurations -/

/-- **Counter-machine configurations are upstream URM configurations**: both are a
program counter and a register file `ℕ → ℕ` (`Cslib.URM.State`).
Source: Shepherdson–Sturgis, *Journal of the ACM* 10 (1963), 217–255. -/
def CounterState.equivURM : CounterState ≃ URM.State where
  toFun s := ⟨s.pc, s.regs⟩
  invFun s := ⟨s.pc, s.regs⟩
  left_inv _ := rfl
  right_inv _ := rfl

/-- **The input convention is upstream's**: the initial counter-machine state is
`URM.State.init`, with the inputs in registers `0, 1, …`. -/
theorem CounterState.equivURM_counterInit (inputs : List ℕ) :
    CounterState.equivURM (counterInit inputs) = URM.State.init inputs := rfl

/-- **The halting convention is upstream's**: the URM image of a counter state is
halted (`URM.State.isHalted`) for a URM program `q` exactly when the program counter is
past the end of `q`, the counter-machine halting test `prog.length ≤ s.pc` for a
program `prog` of the same length. -/
theorem CounterState.isHalted_equivURM_iff {s : CounterState} {q : URM.Program} :
    (CounterState.equivURM s).isHalted q ↔ q.length ≤ s.pc := Iff.rfl

/-- **The output convention is upstream's**: register `0` is `URM.Regs.output`. -/
theorem CounterState.output_equivURM (s : CounterState) :
    (CounterState.equivURM s).regs.output = s.regs 0 := rfl

/-- **`inc r` is URM `S r`**: where the counter program has `inc r` and a URM
program has `S r` at the current program counter, one counter step is one
upstream `URM.Step`. -/
theorem urmStep_of_counterStep_inc {prog : List CounterInstr} {q : URM.Program}
    {s : CounterState} {r : ℕ} (hp : prog[s.pc]? = some (.inc r))
    (hq : q[s.pc]? = some (.S r)) :
    URM.Step q (CounterState.equivURM s) (CounterState.equivURM (counterStep prog s)) := by
  have h := URM.Step.succ (p := q) (s := CounterState.equivURM s) hq
  simp only [counterStep, hp]
  exact h

/-- **`jz r j` is URM `J r z j` against a zero register**: where the counter
program has `jz r j`, a URM program has `J r z j` at the current program counter,
and register `z` holds `0`, one counter step is one upstream `URM.Step`. -/
theorem urmStep_of_counterStep_jz {prog : List CounterInstr} {q : URM.Program}
    {s : CounterState} {r z j : ℕ} (hp : prog[s.pc]? = some (.jz r j))
    (hq : q[s.pc]? = some (.J r z j)) (hz : s.regs z = 0) :
    URM.Step q (CounterState.equivURM s) (CounterState.equivURM (counterStep prog s)) := by
  simp only [counterStep, hp]
  by_cases h0 : s.regs r = 0
  · rw [ite_eq_left h0]
    exact URM.Step.jump_eq (s := CounterState.equivURM s) hq
      (by simp [URM.Regs.read, CounterState.equivURM, h0, hz])
  · rw [ite_eq_right h0]
    exact URM.Step.jump_ne (s := CounterState.equivURM s) hq
      (by simpa [URM.Regs.read, CounterState.equivURM, hz] using h0)

end Cslib.Decidability
