/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Cslib.Computability.URM.Computable
public import CSLibExt.Computability.Machines.Turing.SingleTape.Bridge
public import CSLibExt.Computability.Decidability.TuringReducible
public import Mathlib.Computability.Partrec
public import Mathlib.Computability.RE

/-!
# URM programs compute partial recursive functions

Unlimited register machines (`Cslib.URM`: instructions `Z`, `S`, `T`, `J` on registers
`ℕ → ℕ`) compute exactly the partial recursive functions in one direction: every
URM-computable partial function `ℕ →. ℕ` is `Nat.Partrec`. The converse direction --
compiling a partial recursive function to a URM program -- is registered as
`partrec_to_urm` in
`WantedExt/TheoryOfComputation/PartrecToURM.lean`.

The proof follows the single-tape bridge in `ToRecursive`: a URM program's registers are
coded as a list of length `R + 1`, where `R` is the sum of the maximal registers of the
program's instructions, so every register the program can touch is represented. One coded
step (`codedStep`) is primitive recursive, bounded execution (`execN`) is primitive
recursive by iteration, and the output is read off by unbounded search
(`Nat.Partrec.rfindOpt`) over the first halting step. The coded step agrees with the
machine step (`codedStep_of_step`, `step_of_codedStep`), and reached coded states are
exactly the machine's reachable states (`execN_toCoded_steps`).

## Main definitions

- `Cslib.URM.encodeInstr`: a code for a URM instruction as a natural number, by pairing the
  instruction tag with the paired arguments.
- `Cslib.URM.codedStep`: one URM step on coded states `(pc, regs)`, where `regs` is the
  list of the first `R + 1` register contents.
- `Cslib.URM.Decidable`, `Cslib.URM.Recognizable`: a predicate is URM-decidable
  (URM-recognizable) when a URM program outputs `1`/`0` according to the predicate
  (halts exactly on the predicate).

## Main results

- `Cslib.URM.partrec_of_computable`: a URM-computable partial function `ℕ →. ℕ` is
  partial recursive.
- `Cslib.URM.Decidable.computablePred`, `Cslib.URM.Recognizable.rePred`: URM-decidable
  predicates are `ComputablePred`, URM-recognizable predicates are `REPred`.
- `Cslib.URM.Decidable.singleTapeDecidable`, `Cslib.URM.Decidable.tm2Decidable`,
  `Cslib.URM.Recognizable.singleTapeRecognizable`,
  `Cslib.URM.Recognizable.tm2Recognizable`: URM-decidable/recognizable predicates are
  decidable/recognizable by single-tape and multi-stack Turing machines.

## References

* M. Sipser, *Introduction to the Theory of Computation*, 3rd ed., Cengage, 2013, §3.1
  (unlimited register machines compute the same class as Turing machines, there called
  the Church--Turing thesis).
* R. I. Soare, *Recursively Enumerable Sets and Degrees*, Springer, 1987, Ch. I §2
  (unlimited register machines and partial recursive functions).
* J. C. Shepherdson and H. E. Sturgis, *Computability of Recursive Functions*, Journal of
  the ACM 10 (1963), 217--255 (the URM model).
-/

@[expose] public section

set_option autoImplicit false

open Computability Nat.Partrec

namespace Cslib.URM

/-- **Code of a URM instruction** as a natural number: the instruction tag paired with the
paired arguments, `Z n ↦ pair 0 n`, `S n ↦ pair 1 n`, `T m n ↦ pair 2 (pair m n)`,
`J m n q ↦ pair 3 (pair m (pair n q))`. -/
def encodeInstr : Instr → ℕ
  | .Z n => Nat.pair 0 n
  | .S n => Nat.pair 1 n
  | .T m n => Nat.pair 2 (Nat.pair m n)
  | .J m n q => Nat.pair 3 (Nat.pair m (Nat.pair n q))

/-- The tag of the code of an instruction. -/
theorem encodeInstr_unpair_fst (instr : Instr) :
    (encodeInstr instr).unpair.1 = match instr with
      | .Z _ => 0 | .S _ => 1 | .T _ _ => 2 | .J _ _ _ => 3 := by
  cases instr <;> simp [encodeInstr, Nat.unpair_pair]

/-- The payload of the code of an instruction. -/
theorem encodeInstr_unpair_snd (instr : Instr) :
    (encodeInstr instr).unpair.2 = match instr with
      | .Z n => n | .S n => n | .T m n => Nat.pair m n
      | .J m n q => Nat.pair m (Nat.pair n q) := by
  cases instr <;> simp [encodeInstr, Nat.unpair_pair]

/-- **One coded URM step.** The state is given by its program counter `pc` and its
register list `regs` (the first `R + 1` register contents). The program is given as the list
`codes` of instruction codes. A halted state (`pc` past the end of the program) has no
successor; an unknown tag (which never occurs for a genuine instruction code) also has none. -/
def codedStep (codes : List ℕ) (pc : ℕ) (regs : List ℕ) : Option (ℕ × List ℕ) :=
  if pc < codes.length then
    if (codes.getD pc 0).unpair.1 = 0 then
      some (pc + 1, regs.set (codes.getD pc 0).unpair.2 0)
    else if (codes.getD pc 0).unpair.1 = 1 then
      some (pc + 1, regs.set (codes.getD pc 0).unpair.2
        (regs.getD (codes.getD pc 0).unpair.2 0 + 1))
    else if (codes.getD pc 0).unpair.1 = 2 then
      some (pc + 1, regs.set (codes.getD pc 0).unpair.2.unpair.2
        (regs.getD (codes.getD pc 0).unpair.2.unpair.1 0))
    else if (codes.getD pc 0).unpair.1 = 3 then
      some ((if regs.getD (codes.getD pc 0).unpair.2.unpair.1 0 =
          regs.getD (codes.getD pc 0).unpair.2.unpair.2.unpair.1 0
        then (codes.getD pc 0).unpair.2.unpair.2.unpair.2 else pc + 1), regs)
    else Option.none
  else Option.none

/-- **The coded step is primitive recursive**, for any fixed list of instruction codes. -/
theorem primrec_codedStep (codes : List ℕ) :
    Primrec fun s : ℕ × List ℕ ↦ codedStep codes s.1 s.2 := by
  have hget : Primrec fun s : ℕ × List ℕ ↦ codes.getD s.1 0 :=
    (Primrec.list_getD 0).comp (Primrec.const codes) Primrec.fst
  have htag : Primrec fun s : ℕ × List ℕ ↦ (codes.getD s.1 0).unpair.1 :=
    (Primrec.fst.comp Primrec.unpair).comp hget
  have hpayload : Primrec fun s : ℕ × List ℕ ↦ (codes.getD s.1 0).unpair.2 :=
    (Primrec.snd.comp Primrec.unpair).comp hget
  have hZ : Primrec fun s : ℕ × List ℕ ↦
      some (s.1 + 1, s.2.set (codes.getD s.1 0).unpair.2 0) :=
    Primrec.option_some.comp (Primrec.pair (Primrec.succ.comp Primrec.fst)
      (Primrec₂.comp Primrec.list_set Primrec.snd
        (Primrec.pair hpayload (Primrec.const 0))))
  have hS : Primrec fun s : ℕ × List ℕ ↦ some
      (s.1 + 1, s.2.set (codes.getD s.1 0).unpair.2
        (s.2.getD (codes.getD s.1 0).unpair.2 0 + 1)) :=
    Primrec.option_some.comp (Primrec.pair (Primrec.succ.comp Primrec.fst)
      (Primrec₂.comp Primrec.list_set Primrec.snd
        (Primrec.pair hpayload
          (Primrec.succ.comp ((Primrec.list_getD 0).comp Primrec.snd hpayload)))))
  have hm : Primrec fun s : ℕ × List ℕ ↦ (codes.getD s.1 0).unpair.2.unpair.1 :=
    (Primrec.fst.comp Primrec.unpair).comp hpayload
  have hn : Primrec fun s : ℕ × List ℕ ↦ (codes.getD s.1 0).unpair.2.unpair.2 :=
    (Primrec.snd.comp Primrec.unpair).comp hpayload
  have hT : Primrec fun s : ℕ × List ℕ ↦ some
      (s.1 + 1, s.2.set (codes.getD s.1 0).unpair.2.unpair.2
        (s.2.getD (codes.getD s.1 0).unpair.2.unpair.1 0)) :=
    Primrec.option_some.comp (Primrec.pair (Primrec.succ.comp Primrec.fst)
      (Primrec₂.comp Primrec.list_set Primrec.snd
        (Primrec.pair hn ((Primrec.list_getD 0).comp Primrec.snd hm))))
  have hnJ : Primrec fun s : ℕ × List ℕ ↦
      (codes.getD s.1 0).unpair.2.unpair.2.unpair.1 :=
    (Primrec.fst.comp Primrec.unpair).comp hn
  have hqJ : Primrec fun s : ℕ × List ℕ ↦
      (codes.getD s.1 0).unpair.2.unpair.2.unpair.2 :=
    (Primrec.snd.comp Primrec.unpair).comp hn
  have hgetDm : Primrec fun s : ℕ × List ℕ ↦
      s.2.getD (codes.getD s.1 0).unpair.2.unpair.1 0 :=
    (Primrec.list_getD 0).comp Primrec.snd hm
  have hgetDn : Primrec fun s : ℕ × List ℕ ↦
      s.2.getD (codes.getD s.1 0).unpair.2.unpair.2.unpair.1 0 :=
    (Primrec.list_getD 0).comp Primrec.snd hnJ
  have hJ : Primrec fun s : ℕ × List ℕ ↦ some
      ((if s.2.getD (codes.getD s.1 0).unpair.2.unpair.1 0 =
          s.2.getD (codes.getD s.1 0).unpair.2.unpair.2.unpair.1 0
        then (codes.getD s.1 0).unpair.2.unpair.2.unpair.2 else s.1 + 1), s.2) :=
    Primrec.option_some.comp (Primrec.pair
      (Primrec.ite (Primrec.eq.comp hgetDm hgetDn) hqJ
        (Primrec.succ.comp Primrec.fst)) Primrec.snd)
  have hcomb : Primrec (fun s : ℕ × List ℕ ↦
      if s.1 < codes.length then
        (if (codes.getD s.1 0).unpair.1 = 0 then
          some (s.1 + 1, s.2.set (codes.getD s.1 0).unpair.2 0)
        else if (codes.getD s.1 0).unpair.1 = 1 then
          some (s.1 + 1, s.2.set (codes.getD s.1 0).unpair.2
            (s.2.getD (codes.getD s.1 0).unpair.2 0 + 1))
        else if (codes.getD s.1 0).unpair.1 = 2 then
          some (s.1 + 1, s.2.set (codes.getD s.1 0).unpair.2.unpair.2
            (s.2.getD (codes.getD s.1 0).unpair.2.unpair.1 0))
        else if (codes.getD s.1 0).unpair.1 = 3 then
          some ((if s.2.getD (codes.getD s.1 0).unpair.2.unpair.1 0 =
              s.2.getD (codes.getD s.1 0).unpair.2.unpair.2.unpair.1 0
            then (codes.getD s.1 0).unpair.2.unpair.2.unpair.2 else s.1 + 1), s.2)
        else Option.none)
      else Option.none) :=
    Primrec.ite (Primrec.nat_lt.comp Primrec.fst (Primrec.const codes.length))
      (Primrec.ite (Primrec.eq.comp htag (Primrec.const 0)) hZ
        (Primrec.ite (Primrec.eq.comp htag (Primrec.const 1)) hS
          (Primrec.ite (Primrec.eq.comp htag (Primrec.const 2)) hT
            (Primrec.ite (Primrec.eq.comp htag (Primrec.const 3)) hJ
              (Primrec.const Option.none)))))
      (Primrec.const Option.none)
  refine Primrec.of_eq hcomb fun s ↦ by
    obtain ⟨pc, regs⟩ := s
    change (if pc < codes.length then
        (if (codes.getD pc 0).unpair.1 = 0 then
          some (pc + 1, regs.set (codes.getD pc 0).unpair.2 0)
        else if (codes.getD pc 0).unpair.1 = 1 then
          some (pc + 1, regs.set (codes.getD pc 0).unpair.2
            (regs.getD (codes.getD pc 0).unpair.2 0 + 1))
        else if (codes.getD pc 0).unpair.1 = 2 then
          some (pc + 1, regs.set (codes.getD pc 0).unpair.2.unpair.2
            (regs.getD (codes.getD pc 0).unpair.2.unpair.1 0))
        else if (codes.getD pc 0).unpair.1 = 3 then
          some ((if regs.getD (codes.getD pc 0).unpair.2.unpair.1 0 =
              regs.getD (codes.getD pc 0).unpair.2.unpair.2.unpair.1 0
            then (codes.getD pc 0).unpair.2.unpair.2.unpair.2 else pc + 1), regs)
        else Option.none)
      else Option.none) = codedStep codes pc regs
    simp only [codedStep]

/-! ### Coded states -/

section Coded

variable (p : Program)

/-- **Register bound** of a program: the sum of the maximal registers of its instructions.
Every register an instruction of `p` can read or write is at most `R`. -/
def regBound : ℕ := (p.map Instr.maxRegister).sum

/-- The register list of a register state: the contents of registers `0, …, R`. -/
abbrev toRegs (σ : Regs) : List ℕ := (List.range (regBound p + 1)).map σ

/-- The coded state of a machine state: the program counter and the register list. -/
abbrev toCoded (s : State) : ℕ × List ℕ := (s.pc, toRegs p s.regs)

/-- The machine state of a coded state: registers read through `List.getD` with default `0`. -/
abbrev ofCoded (c : ℕ × List ℕ) : State := ⟨c.1, fun n ↦ c.2.getD n 0⟩

/-- The register list has length `R + 1`. -/
theorem length_toRegs (σ : Regs) : (toRegs p σ).length = regBound p + 1 := by
  simp [toRegs]

/-- Reading the register list returns the register contents up to `R`, and `0` beyond. -/
theorem getD_toRegs (σ : Regs) (n : ℕ) :
    (toRegs p σ).getD n 0 = if n ≤ regBound p then σ n else 0 := by
  rw [toRegs, List.getD_eq_getElem?_getD, List.getElem?_map]
  by_cases h : n < regBound p + 1
  · have h' : (List.range (regBound p + 1))[n]? = some n := List.getElem?_range h
    rw [h']
    simp only [Option.map_some, Option.getD_some]
    rw [ite_eq_left (by omega : n ≤ regBound p)]
  · have h' : (List.range (regBound p + 1))[n]? = Option.none :=
      List.getElem?_eq_none_iff.2 (by rw [List.length_range]; omega)
    rw [h']; simp [show ¬ n ≤ regBound p by omega]

/-- Updating a register is `List.set` on the register list, for registers within the bound. -/
theorem toRegs_update (σ : Regs) {n v : ℕ} (hn : n ≤ regBound p) :
    toRegs p (Function.update σ n v) = (toRegs p σ).set n v := by
  rw [List.ext_getElem?_iff]
  intro i
  have hset : ((toRegs p σ).set n v)[i]? =
      if n = i then (if n < (toRegs p σ).length then some v else Option.none)
      else (toRegs p σ)[i]? := by
    rw [List.getElem?_set]
  by_cases hi : i < regBound p + 1
  · have e1 : (List.range (regBound p + 1))[i]? = some i := List.getElem?_range hi
    have lhs : (toRegs p (Function.update σ n v))[i]? =
        some (Function.update σ n v i) := by
      simp [toRegs, List.getElem?_map, e1]
    have rhs : ((toRegs p σ).set n v)[i]? =
        if i = n then some v else some (σ i) := by
      rw [hset]
      by_cases h : i = n
      · subst h
        simp [length_toRegs, hi]
      · simp [h, ne_comm.mp h, toRegs, List.getElem?_map, e1]
    rw [lhs, rhs]
    by_cases h : i = n
    · subst h
      simp [Function.update]
    · simp [Function.update, h]
  · have e1 : (List.range (regBound p + 1))[i]? = Option.none :=
      List.getElem?_eq_none_iff.2 (by rw [List.length_range]; omega)
    have hne : i ≠ n := by omega
    have lhs : (toRegs p (Function.update σ n v))[i]? = Option.none := by
      simp [toRegs, List.getElem?_map, e1]
    have rhs : ((toRegs p σ).set n v)[i]? = Option.none := by
      rw [hset, ite_eq_right (fun h' ↦ hne h'.symm)]
      simp [toRegs, List.getElem?_map, e1]
    rw [lhs, rhs]

/-- The maximal register of an instruction of `p` is at most the register bound. -/
theorem maxRegister_le_regBound {instr : Instr} (h : instr ∈ p) :
    instr.maxRegister ≤ regBound p := by
  apply List.single_le_sum (fun _ _ ↦ Nat.zero_le _)
  exact List.mem_map_of_mem h

/-- The register written by an instruction of `p` is at most the register bound. -/
theorem writesTo_le_regBound {instr : Instr} {n : ℕ} (h : instr ∈ p)
    (hw : instr.writesTo = some n) : n ≤ regBound p := by
  have h1 := maxRegister_le_regBound p h
  cases instr with
  | Z m =>
    simp [Instr.writesTo] at hw; subst hw; simpa [Instr.maxRegister] using h1
  | S m =>
    simp [Instr.writesTo] at hw; subst hw; simpa [Instr.maxRegister] using h1
  | T m k =>
    simp [Instr.writesTo] at hw; subst hw
    have hkm : k ≤ max m k := Nat.le_max_right m k
    simp [Instr.maxRegister] at h1; omega
  | J m k q =>
    simp [Instr.writesTo] at hw

/-- The registers read by an instruction of `p` are at most the register bound. -/
theorem reads_le_regBound {instr : Instr} {n : ℕ} (h : instr ∈ p)
    (hr : n ∈ instr.readsFrom) : n ≤ regBound p := by
  have h1 := maxRegister_le_regBound p h
  cases instr with
  | Z m =>
    simp [Instr.readsFrom] at hr
  | S m =>
    simp [Instr.readsFrom] at hr; subst hr; simpa [Instr.maxRegister] using h1
  | T m k =>
    simp [Instr.readsFrom] at hr; subst hr
    simp [Instr.maxRegister] at h1; omega
  | J m k q =>
    simp [Instr.readsFrom] at hr
    rcases hr with rfl | rfl <;> simp [Instr.maxRegister] at h1 <;> omega

/-- The coded state of the state coded back is the coded state, when the register list
has length `R + 1`. -/
theorem toCoded_ofCoded {c : ℕ × List ℕ} (hlen : c.2.length = regBound p + 1) :
    toCoded p (ofCoded c) = c := by
  obtain ⟨pc, regs⟩ := c
  change regs.length = regBound p + 1 at hlen
  simp only [toCoded, ofCoded]
  congr 1
  apply List.ext_getElem
  · rw [length_toRegs]; exact hlen.symm
  · intro i hi hi'
    simp only [toRegs, List.getElem_map, List.getElem_range, hi]
    exact List.getD_eq_getElem regs 0 hi'

end Coded

/-! ### The coded step agrees with the machine step -/

section StepAgree

variable {p : Program}

/-- The program counter of a state that can step is in range. -/
theorem pc_lt_of_step {s s' : State} (h : Step p s s') : s.pc < p.length := by
  cases h with
  | zero hi | succ hi | transfer hi | jump_eq hi _ | jump_ne hi _ =>
    by_contra hc
    simp only [not_lt] at hc
    rw [List.getElem?_eq_none_iff.2 hc] at hi
    simp at hi

/-- The coded instruction at the program counter is the code of the instruction there. -/
theorem getD_codes {pc : ℕ} {instr : Instr} (hi : p[pc]? = some instr) :
    (p.map encodeInstr).getD pc 0 = encodeInstr instr := by
  rw [List.getD_eq_getElem?_getD, List.getElem?_map, hi]
  rfl

/-- **A machine step is a coded step**: the coded step of the coded state is the coded
successor state. -/
theorem codedStep_of_step {s s' : State} (h : Step p s s') :
    codedStep (p.map encodeInstr) (toCoded p s).1 (toCoded p s).2 =
      some (toCoded p s') := by
  have hlt : s.pc < p.length := pc_lt_of_step h
  have hlen : (p.map encodeInstr).length = p.length := by simp
  have hlt' : s.pc < (p.map encodeInstr).length := by rw [hlen]; exact hlt
  change codedStep (p.map encodeInstr) s.pc (toRegs p s.regs) = some (toCoded p s')
  unfold codedStep
  rw [ite_eq_left hlt']
  cases h with
  | zero hi =>
    rename_i n
    have hni : n ≤ regBound p := writesTo_le_regBound p (List.mem_of_getElem? hi) rfl
    have htag : ((p.map encodeInstr).getD s.pc 0).unpair.1 = 0 := by
      rw [getD_codes hi]; simp [encodeInstr]
    have hpay : ((p.map encodeInstr).getD s.pc 0).unpair.2 = n := by
      rw [getD_codes hi]; simp [encodeInstr]
    rw [ite_eq_left htag, hpay]
    simp only [toCoded, Regs.write]
    rw [toRegs_update p s.regs hni]
  | succ hi =>
    rename_i n
    have hni : n ≤ regBound p := writesTo_le_regBound p (List.mem_of_getElem? hi) rfl
    have hnot0 : ¬ ((p.map encodeInstr).getD s.pc 0).unpair.1 = 0 := by
      rw [getD_codes hi]; simp [encodeInstr]
    have htag : ((p.map encodeInstr).getD s.pc 0).unpair.1 = 1 := by
      rw [getD_codes hi]; simp [encodeInstr]
    have hpay : ((p.map encodeInstr).getD s.pc 0).unpair.2 = n := by
      rw [getD_codes hi]; simp [encodeInstr]
    have hget : (toRegs p s.regs).getD n 0 = s.regs n := by
      rw [getD_toRegs, ite_eq_left hni]
    rw [ite_eq_right hnot0, ite_eq_left htag, hpay, hget]
    simp only [toCoded, Regs.write, Regs.read]
    rw [toRegs_update p s.regs hni]
  | transfer hi =>
    rename_i m n
    have hm : m ≤ regBound p := reads_le_regBound p (List.mem_of_getElem? hi)
      (by simp [Instr.readsFrom])
    have hn : n ≤ regBound p := writesTo_le_regBound p (List.mem_of_getElem? hi) rfl
    have hnot0 : ¬ ((p.map encodeInstr).getD s.pc 0).unpair.1 = 0 := by
      rw [getD_codes hi]; simp [encodeInstr]
    have hnot1 : ¬ ((p.map encodeInstr).getD s.pc 0).unpair.1 = 1 := by
      rw [getD_codes hi]; simp [encodeInstr]
    have htag : ((p.map encodeInstr).getD s.pc 0).unpair.1 = 2 := by
      rw [getD_codes hi]; simp [encodeInstr]
    have hm' : ((p.map encodeInstr).getD s.pc 0).unpair.2.unpair.1 = m := by
      rw [getD_codes hi]; simp [encodeInstr]
    have hn' : ((p.map encodeInstr).getD s.pc 0).unpair.2.unpair.2 = n := by
      rw [getD_codes hi]; simp [encodeInstr]
    have hget : (toRegs p s.regs).getD m 0 = s.regs m := by
      rw [getD_toRegs, ite_eq_left hm]
    rw [ite_eq_right hnot0, ite_eq_right hnot1, ite_eq_left htag, hn', hm', hget]
    simp only [toCoded, Regs.write, Regs.read]
    rw [toRegs_update p s.regs hn]
  | jump_eq hi heq =>
    rename_i m n q
    have hm : m ≤ regBound p := reads_le_regBound p (List.mem_of_getElem? hi)
      (by simp [Instr.readsFrom])
    have hn : n ≤ regBound p := reads_le_regBound p (List.mem_of_getElem? hi)
      (by simp [Instr.readsFrom])
    have hnot0 : ¬ ((p.map encodeInstr).getD s.pc 0).unpair.1 = 0 := by
      rw [getD_codes hi]; simp [encodeInstr]
    have hnot1 : ¬ ((p.map encodeInstr).getD s.pc 0).unpair.1 = 1 := by
      rw [getD_codes hi]; simp [encodeInstr]
    have hnot2 : ¬ ((p.map encodeInstr).getD s.pc 0).unpair.1 = 2 := by
      rw [getD_codes hi]; simp [encodeInstr]
    have htag : ((p.map encodeInstr).getD s.pc 0).unpair.1 = 3 := by
      rw [getD_codes hi]; simp [encodeInstr]
    have hm' : ((p.map encodeInstr).getD s.pc 0).unpair.2.unpair.1 = m := by
      rw [getD_codes hi]; simp [encodeInstr]
    have hn' : ((p.map encodeInstr).getD s.pc 0).unpair.2.unpair.2.unpair.1 = n := by
      rw [getD_codes hi]; simp [encodeInstr]
    have hq : ((p.map encodeInstr).getD s.pc 0).unpair.2.unpair.2.unpair.2 = q := by
      rw [getD_codes hi]; simp [encodeInstr]
    have hgetm : (toRegs p s.regs).getD m 0 = s.regs m := by
      rw [getD_toRegs, ite_eq_left hm]
    have hgetn : (toRegs p s.regs).getD n 0 = s.regs n := by
      rw [getD_toRegs, ite_eq_left hn]
    have heq' : s.regs m = s.regs n := heq
    rw [ite_eq_right hnot0, ite_eq_right hnot1, ite_eq_right hnot2, ite_eq_left htag,
      hm', hn', hq, hgetm, hgetn, ite_eq_left heq']
  | jump_ne hi hne =>
    rename_i m n q
    have hm : m ≤ regBound p := reads_le_regBound p (List.mem_of_getElem? hi)
      (by simp [Instr.readsFrom])
    have hn : n ≤ regBound p := reads_le_regBound p (List.mem_of_getElem? hi)
      (by simp [Instr.readsFrom])
    have hnot0 : ¬ ((p.map encodeInstr).getD s.pc 0).unpair.1 = 0 := by
      rw [getD_codes hi]; simp [encodeInstr]
    have hnot1 : ¬ ((p.map encodeInstr).getD s.pc 0).unpair.1 = 1 := by
      rw [getD_codes hi]; simp [encodeInstr]
    have hnot2 : ¬ ((p.map encodeInstr).getD s.pc 0).unpair.1 = 2 := by
      rw [getD_codes hi]; simp [encodeInstr]
    have htag : ((p.map encodeInstr).getD s.pc 0).unpair.1 = 3 := by
      rw [getD_codes hi]; simp [encodeInstr]
    have hm' : ((p.map encodeInstr).getD s.pc 0).unpair.2.unpair.1 = m := by
      rw [getD_codes hi]; simp [encodeInstr]
    have hn' : ((p.map encodeInstr).getD s.pc 0).unpair.2.unpair.2.unpair.1 = n := by
      rw [getD_codes hi]; simp [encodeInstr]
    have hgetm : (toRegs p s.regs).getD m 0 = s.regs m := by
      rw [getD_toRegs, ite_eq_left hm]
    have hgetn : (toRegs p s.regs).getD n 0 = s.regs n := by
      rw [getD_toRegs, ite_eq_left hn]
    have hne' : s.regs m ≠ s.regs n := hne
    rw [ite_eq_right hnot0, ite_eq_right hnot1, ite_eq_right hnot2, ite_eq_left htag,
      hm', hn', hgetm, hgetn, ite_eq_right hne']

/-- **A coded step is a machine step**: from a coded successor one reads off a machine
successor with the same coded state. -/
theorem step_of_codedStep {s : State} {c' : ℕ × List ℕ}
    (h : codedStep (p.map encodeInstr) (toCoded p s).1 (toCoded p s).2 = some c') :
    ∃ s' : State, Step p s s' ∧ toCoded p s' = c' := by
  obtain ⟨pc, σ⟩ := s
  change codedStep (p.map encodeInstr) pc (toRegs p σ) = some c' at h
  have hlen : (p.map encodeInstr).length = p.length := by simp
  have hlt : pc < p.length := by
    by_contra hc
    simp only [not_lt] at hc
    have hnp : ¬ pc < (p.map encodeInstr).length := by rw [hlen]; exact not_lt.2 hc
    have hnone : codedStep (p.map encodeInstr) pc (toRegs p σ) = Option.none := by
      unfold codedStep
      rw [ite_eq_right hnp]
    rw [hnone] at h
    simp at h
  have hlt' : pc < (p.map encodeInstr).length := by rw [hlen]; exact hlt
  unfold codedStep at h
  rw [ite_eq_left hlt'] at h
  cases hc : p[pc]? with
  | none =>
    exfalso
    exact absurd (List.getElem?_eq_none_iff.mp hc) (by omega)
  | some instr =>
    have hmem : instr ∈ p := List.mem_of_getElem? hc
    cases instr with
    | Z n =>
      have htag : ((p.map encodeInstr).getD pc 0).unpair.1 = 0 := by
        rw [getD_codes hc]; simp [encodeInstr]
      have hpay : ((p.map encodeInstr).getD pc 0).unpair.2 = n := by
        rw [getD_codes hc]; simp [encodeInstr]
      rw [ite_eq_left htag, hpay] at h
      refine ⟨⟨pc + 1, Regs.write σ n 0⟩, Step.zero hc, ?_⟩
      simp only [toCoded, Regs.write]
      rw [toRegs_update p σ (writesTo_le_regBound p hmem rfl)]
      exact Option.some.inj h
    | S n =>
      have hni : n ≤ regBound p := writesTo_le_regBound p hmem rfl
      have hnot0 : ¬ ((p.map encodeInstr).getD pc 0).unpair.1 = 0 := by
        rw [getD_codes hc]; simp [encodeInstr]
      have htag : ((p.map encodeInstr).getD pc 0).unpair.1 = 1 := by
        rw [getD_codes hc]; simp [encodeInstr]
      have hpay : ((p.map encodeInstr).getD pc 0).unpair.2 = n := by
        rw [getD_codes hc]; simp [encodeInstr]
      have hget : (toRegs p σ).getD n 0 = σ n := by
        rw [getD_toRegs, ite_eq_left hni]
      rw [ite_eq_right hnot0, ite_eq_left htag, hpay, hget] at h
      refine ⟨⟨pc + 1, Regs.write σ n (Regs.read σ n + 1)⟩, Step.succ hc, ?_⟩
      simp only [toCoded, Regs.write]
      rw [toRegs_update p σ hni]
      exact Option.some.inj h
    | T m n =>
      have hm : m ≤ regBound p := reads_le_regBound p hmem (by simp [Instr.readsFrom])
      have hn : n ≤ regBound p := writesTo_le_regBound p hmem rfl
      have hnot0 : ¬ ((p.map encodeInstr).getD pc 0).unpair.1 = 0 := by
        rw [getD_codes hc]; simp [encodeInstr]
      have hnot1 : ¬ ((p.map encodeInstr).getD pc 0).unpair.1 = 1 := by
        rw [getD_codes hc]; simp [encodeInstr]
      have htag : ((p.map encodeInstr).getD pc 0).unpair.1 = 2 := by
        rw [getD_codes hc]; simp [encodeInstr]
      have hm' : ((p.map encodeInstr).getD pc 0).unpair.2.unpair.1 = m := by
        rw [getD_codes hc]; simp [encodeInstr]
      have hn' : ((p.map encodeInstr).getD pc 0).unpair.2.unpair.2 = n := by
        rw [getD_codes hc]; simp [encodeInstr]
      have hget : (toRegs p σ).getD m 0 = σ m := by
        rw [getD_toRegs, ite_eq_left hm]
      rw [ite_eq_right hnot0, ite_eq_right hnot1, ite_eq_left htag, hn', hm', hget] at h
      refine ⟨⟨pc + 1, Regs.write σ n (Regs.read σ m)⟩, Step.transfer hc, ?_⟩
      simp only [toCoded, Regs.write]
      rw [toRegs_update p σ hn]
      exact Option.some.inj h
    | J m n q =>
      have hm : m ≤ regBound p := reads_le_regBound p hmem (by simp [Instr.readsFrom])
      have hn : n ≤ regBound p := reads_le_regBound p hmem (by simp [Instr.readsFrom])
      have hnot0 : ¬ ((p.map encodeInstr).getD pc 0).unpair.1 = 0 := by
        rw [getD_codes hc]; simp [encodeInstr]
      have hnot1 : ¬ ((p.map encodeInstr).getD pc 0).unpair.1 = 1 := by
        rw [getD_codes hc]; simp [encodeInstr]
      have hnot2 : ¬ ((p.map encodeInstr).getD pc 0).unpair.1 = 2 := by
        rw [getD_codes hc]; simp [encodeInstr]
      have htag : ((p.map encodeInstr).getD pc 0).unpair.1 = 3 := by
        rw [getD_codes hc]; simp [encodeInstr]
      have hm' : ((p.map encodeInstr).getD pc 0).unpair.2.unpair.1 = m := by
        rw [getD_codes hc]; simp [encodeInstr]
      have hn' : ((p.map encodeInstr).getD pc 0).unpair.2.unpair.2.unpair.1 = n := by
        rw [getD_codes hc]; simp [encodeInstr]
      have hq : ((p.map encodeInstr).getD pc 0).unpair.2.unpair.2.unpair.2 = q := by
        rw [getD_codes hc]; simp [encodeInstr]
      have hgetm : (toRegs p σ).getD m 0 = σ m := by
        rw [getD_toRegs, ite_eq_left hm]
      have hgetn : (toRegs p σ).getD n 0 = σ n := by
        rw [getD_toRegs, ite_eq_left hn]
      rw [ite_eq_right hnot0, ite_eq_right hnot1, ite_eq_right hnot2, ite_eq_left htag,
        hm', hn', hq, hgetm, hgetn] at h
      by_cases heq : σ m = σ n
      · refine ⟨⟨q, σ⟩, Step.jump_eq hc heq, ?_⟩
        simp only [toCoded]
        rw [ite_eq_left heq] at h
        exact Option.some.inj h
      · refine ⟨⟨pc + 1, σ⟩, Step.jump_ne hc heq, ?_⟩
        simp only [toCoded]
        rw [ite_eq_right heq] at h
        exact Option.some.inj h

end StepAgree


/-! ### Predicate classes -/

/-- A predicate is **URM-decidable** when a URM program computes its characteristic function
(`Cslib.Decidability.charFun`: `1` on members, `0` elsewhere). -/
def Decidable (P : ℕ → Prop) : Prop :=
  ∃ prog : Program, ∀ n, eval prog [n] = Cslib.Decidability.charFun P n

/-- A predicate is **URM-recognizable** when a URM program halts exactly on its members. -/
def Recognizable (P : ℕ → Prop) : Prop :=
  ∃ prog : Program, ∀ n, (eval prog [n]).Dom ↔ P n

/-! ### Bounded execution -/

section Exec

variable (p : Program)

/-- One coded step, staying put when halted. -/
def stepFn (codes : List ℕ) : ℕ × List ℕ → ℕ × List ℕ :=
  fun s ↦ (codedStep codes s.1 s.2).getD s

/-- **The one-step function is primitive recursive.** -/
theorem primrec_stepFn (codes : List ℕ) : Primrec (stepFn codes) := by
  change Primrec fun s : ℕ × List ℕ ↦ (codedStep codes s.1 s.2).getD s
  exact Primrec₂.comp Primrec.option_getD (primrec_codedStep codes) Primrec.id

/-- **Bounded execution**: `t` iterations of the one-step function. -/
def execN (codes : List ℕ) (t : ℕ) (s : ℕ × List ℕ) : ℕ × List ℕ :=
  (stepFn codes)^[t] s

/-- Bounded execution steps once per iteration. -/
theorem execN_succ (codes : List ℕ) (t : ℕ) (s : ℕ × List ℕ) :
    execN codes (t + 1) s = stepFn codes (execN codes t s) :=
  Function.iterate_succ_apply' _ _ _

/-- **Initial coded state** for input `x`: program counter `0`, register `0` holding `x`,
all other registers `0`. -/
def initCoded (x : ℕ) : ℕ × List ℕ :=
  (0, (List.range (regBound p + 1)).map fun n ↦ if n = 0 then x else 0)

/-- **The initial coded state is primitive recursive in the input.** -/
theorem primrec_initCoded : Primrec fun x ↦ initCoded p x := by
  refine (Primrec.pair (Primrec.const 0) ?_)
  refine (Primrec.list_map (Primrec.const (List.range (regBound p + 1))) ?_)
  exact Primrec.ite (Primrec.eq.comp Primrec.snd (Primrec.const 0)) Primrec.fst
    (Primrec.const 0)

/-- **Bounded execution is primitive recursive in the input and the step bound.** -/
theorem primrec_execN : Primrec fun a : ℕ × ℕ ↦
    execN (p.map encodeInstr) a.2 (initCoded p a.1) :=
  Primrec.nat_iterate Primrec.snd ((primrec_initCoded p).comp Primrec.fst)
    ((primrec_stepFn _).comp Primrec.snd)

/-- The initial coded state is the coded initial machine state. -/
theorem initCoded_eq_toCoded (x : ℕ) : initCoded p x = toCoded p (State.init [x]) := by
  simp only [initCoded, toCoded, State.init, Regs.ofInputs, toRegs]
  congr 1
  apply List.map_congr_left
  intro n _
  by_cases h : n = 0
  · subst h; rfl
  · obtain ⟨k, rfl⟩ : ∃ k, n = k + 1 := ⟨n - 1, by omega⟩
    change 0 = [x].getD (k + 1) 0
    rw [List.getD_eq_getElem?_getD,
      List.getElem?_eq_none_iff.2 (by rw [List.length_singleton]; omega)]
    rfl

/-- **Reached coded states are exactly the machine's reachable states.** -/
theorem execN_toCoded_steps (x : ℕ) (t : ℕ) :
    ∃ s' : State, Steps p (State.init [x]) s' ∧
      toCoded p s' = execN (p.map encodeInstr) t (initCoded p x) := by
  induction t with
  | zero => exact ⟨State.init [x], Relation.ReflTransGen.refl, (initCoded_eq_toCoded p x).symm⟩
  | succ t ih =>
    obtain ⟨s', hs', hcode⟩ := ih
    rw [execN_succ]
    by_cases hnone : codedStep (p.map encodeInstr) (toCoded p s').1 (toCoded p s').2 =
        Option.none
    · refine ⟨s', hs', ?_⟩
      rw [← hcode]
      simp [stepFn, hnone]
    · obtain ⟨c', hc'⟩ : ∃ c', codedStep (p.map encodeInstr) (toCoded p s').1
          (toCoded p s').2 = some c' := Option.ne_none_iff_exists'.mp hnone
      obtain ⟨s'', hstep, hcode''⟩ := step_of_codedStep hc'
      refine ⟨s'', hs'.tail hstep, ?_⟩
      rw [← hcode]
      change toCoded p s'' = (codedStep (p.map encodeInstr) (toCoded p s').1
        (toCoded p s').2).getD (toCoded p s')
      rw [hc', Option.getD_some, hcode'']

/-- **A halted coded state gives a halting machine run.** -/
theorem halts_of_execN_halted (x t : ℕ)
    (h : (execN (p.map encodeInstr) t (initCoded p x)).1 ≥ (p.map encodeInstr).length) :
    Halts p [x] := by
  obtain ⟨s', hs', hcode⟩ := execN_toCoded_steps p x t
  refine ⟨s', hs', ?_⟩
  have hpc : s'.pc = (execN (p.map encodeInstr) t (initCoded p x)).1 :=
    congrArg Prod.fst hcode
  change p.length ≤ s'.pc
  rw [hpc]
  have hlen : (p.map encodeInstr).length = p.length := by simp
  omega

/-- **Every reachable state is reached by bounded execution.** -/
theorem exists_execN_eq_of_steps (x : ℕ) {s : State}
    (hs : Steps p (State.init [x]) s) :
    ∃ t, execN (p.map encodeInstr) t (initCoded p x) = toCoded p s := by
  induction hs with
  | refl => exact ⟨0, initCoded_eq_toCoded p x⟩
  | tail hs' hstep ih =>
    obtain ⟨t, ht⟩ := ih
    refine ⟨t + 1, ?_⟩
    rw [execN_succ, ht]
    change (codedStep (p.map encodeInstr) (toCoded p _).1 (toCoded p _).2).getD _ =
      toCoded p _
    rw [codedStep_of_step hstep]
    rfl

/-- **Bounded execution is stable once halted.** -/
theorem execN_succ_of_halted (codes : List ℕ) {t : ℕ} {s : ℕ × List ℕ}
    (h : codes.length ≤ (execN codes t s).1) : execN codes (t + 1) s = execN codes t s := by
  rw [execN_succ]
  change (codedStep codes (execN codes t s).1 (execN codes t s).2).getD _ = execN codes t s
  have hnone : codedStep codes (execN codes t s).1 (execN codes t s).2 = Option.none := by
    unfold codedStep
    rw [ite_eq_right (by omega : ¬ (execN codes t s).1 < codes.length)]
  rw [hnone]
  rfl

/-- **Bounded execution stays at its halted value.** -/
theorem execN_eq_of_le (codes : List ℕ) {s : ℕ × List ℕ} {t₁ t₂ : ℕ} (hle : t₁ ≤ t₂)
    (h : codes.length ≤ (execN codes t₁ s).1) : execN codes t₂ s = execN codes t₁ s := by
  obtain ⟨k, rfl⟩ : ∃ k, t₂ = t₁ + k := ⟨t₂ - t₁, by omega⟩
  clear hle
  induction k with
  | zero => simp
  | succ k ih =>
    have hhalt : codes.length ≤ (execN codes (t₁ + k) s).1 := by rw [ih]; exact h
    rw [show t₁ + (k + 1) = (t₁ + k) + 1 from by omega, execN_succ_of_halted codes hhalt]
    exact ih

/-- **Output after `t` steps**: `none` while the program is still running, `some` of the
contents of register `0` once it has halted. -/
def haltedOutput (x t : ℕ) : Option ℕ :=
  if (execN (p.map encodeInstr) t (initCoded p x)).1 < (p.map encodeInstr).length then
    Option.none
  else some ((execN (p.map encodeInstr) t (initCoded p x)).2.getD 0 0)

/-- **The output function is computable**, hence the URM evaluation is partial recursive
by unbounded search below. -/
theorem computable₂_haltedOutput : Computable₂ (haltedOutput p) := by
  have hexec : Primrec fun a : ℕ × ℕ ↦ execN (p.map encodeInstr) a.2 (initCoded p a.1) :=
    primrec_execN p
  have hhalted : Primrec fun a : ℕ × ℕ ↦ haltedOutput p a.1 a.2 := by
    refine Primrec.ite ?_ (Primrec.const Option.none) ?_
    · exact Primrec.nat_lt.comp (Primrec.fst.comp hexec)
        (Primrec.const (p.map encodeInstr).length)
    · refine Primrec.option_some.comp ?_
      exact (Primrec.list_getD 0).comp (Primrec.snd.comp hexec) (Primrec.const 0)
  exact hhalted.to_comp

end Exec

/-! ### The main theorem -/

section Main

variable {f : ℕ →. ℕ}

/-- **A URM-computable partial function is partial recursive**: the URM evaluation is the
unbounded search for the first halting step of the coded execution. -/
theorem partrec_of_computable (hf : URM.Computable 1 (fun inputs ↦ f (inputs 0))) :
    Partrec f := by
  obtain ⟨prog, hprog⟩ := hf
  have heval : ∀ x, eval prog [x] = f x := by
    intro x
    have hof : List.ofFn (fun _ : Fin 1 ↦ x) = [x] := by rfl
    simpa [hof] using hprog (fun _ ↦ x)
  have hmain : ∀ x, Nat.rfindOpt (haltedOutput prog x) = f x := by
    intro x
    have hmono : ∀ {a m n}, m ≤ n → a ∈ haltedOutput prog x m → a ∈ haltedOutput prog x n := by
      intro a m n hmn ham
      have hsome : haltedOutput prog x m = some a := Option.mem_def.mp ham
      have hhalt : (prog.map encodeInstr).length ≤
          (execN (prog.map encodeInstr) m (initCoded prog x)).1 := by
        by_contra hc
        simp only [not_le] at hc
        rw [haltedOutput, ite_eq_left hc] at hsome
        simp at hsome
      have heq : execN (prog.map encodeInstr) n (initCoded prog x) =
          execN (prog.map encodeInstr) m (initCoded prog x) :=
        execN_eq_of_le _ hmn hhalt
      rw [Option.mem_def]
      have hcongr : haltedOutput prog x n = haltedOutput prog x m := by
        simp only [haltedOutput, heq]
      rw [hcongr, hsome]
    by_cases hdom : (eval prog [x]).Dom
    · obtain ⟨y, hy⟩ := Part.dom_iff_mem.mp hdom
      have hhw : HaltsWithResult prog [x] y :=
        (haltsWithResult_iff_eval prog).2 (Part.eq_some_iff.2 hy)
      obtain ⟨s, hs, hhalt, hout⟩ := hhw
      obtain ⟨t, ht⟩ := exists_execN_eq_of_steps prog x hs
      have hnot : ¬ (execN (prog.map encodeInstr) t (initCoded prog x)).1 <
          (prog.map encodeInstr).length := by
        rw [ht]
        have hlen : (prog.map encodeInstr).length = prog.length := by simp
        rw [hlen]
        change ¬ s.pc < prog.length
        exact not_lt.2 hhalt
      have hhalted : haltedOutput prog x t = some y := by
        rw [haltedOutput, ite_eq_right hnot]
        congr 1
        rw [ht]
        change (toRegs prog s.regs).getD 0 0 = y
        rw [getD_toRegs, ite_eq_left (Nat.zero_le _)]
        exact hout
      rw [← heval x, Part.eq_some_iff.2 hy]
      exact Part.eq_some_iff.2 ((Nat.rfindOpt_mono hmono).2
        ⟨t, Option.mem_def.2 hhalted⟩)
    · have hevnone : eval prog [x] = Part.none :=
        Part.eq_none_iff.2 fun _ hmem ↦ by
          obtain ⟨hDom, -⟩ := hmem
          exact hdom hDom
      have hnone : ∀ t, haltedOutput prog x t = Option.none := by
        intro t
        rw [haltedOutput]
        by_cases hc : (execN (prog.map encodeInstr) t (initCoded prog x)).1 <
            (prog.map encodeInstr).length
        · rw [ite_eq_left hc]
        · exfalso
          have hhalt : Halts prog [x] := halts_of_execN_halted prog x t (by omega)
          have hdom' : (eval prog [x]).Dom := by
            have h1 : (evalState prog [x]).Dom := hhalt
            change ((evalState prog [x]).map (·.regs.output)).Dom
            rw [Part.map_Dom]
            exact h1
          rw [hevnone] at hdom'
          exact hdom'
      rw [← heval x, hevnone]
      exact Part.eq_none_iff.2 fun hy hmem ↦ by
        obtain ⟨t, ht⟩ := Nat.rfindOpt_spec hmem
        rw [hnone t] at ht
        exact Option.not_mem_none hy ht
  exact (Partrec.rfindOpt (computable₂_haltedOutput prog)).of_eq hmain

/-- **A URM-decidable predicate is computable.** -/
theorem Decidable.computablePred {P : ℕ → Prop} (h : Decidable P) : ComputablePred P := by
  obtain ⟨prog, hprog⟩ := h
  refine Cslib.Decidability.computablePred_iff_partrec_charFun.mpr ?_
  apply partrec_of_computable (f := Cslib.Decidability.charFun P)
  refine ⟨prog, fun inputs ↦ ?_⟩
  have hof : List.ofFn inputs = [inputs 0] := by rfl
  rw [hof]
  exact hprog (inputs 0)

/-- **A URM-recognizable predicate is recursively enumerable.** -/
theorem Recognizable.rePred {P : ℕ → Prop} (h : Recognizable P) : REPred P := by
  obtain ⟨prog, hprog⟩ := h
  have hpart : Partrec fun n : ℕ ↦ eval prog [n] := by
    apply partrec_of_computable (f := fun n ↦ eval prog [n])
    refine ⟨prog, fun inputs ↦ ?_⟩
    have hof : List.ofFn inputs = [inputs 0] := by rfl
    rw [hof]
  refine hpart.dom_re.of_eq fun n ↦ hprog n

/-- **A URM-decidable predicate is decidable by a single-tape Turing machine.** -/
theorem Decidable.singleTapeDecidable {P : ℕ → Prop} (h : Decidable P) :
    Cslib.Decidability.SingleTapeDecidable P :=
  Cslib.Decidability.singleTapeDecidable_iff_computablePred.mpr h.computablePred

/-- **A URM-decidable predicate is decidable by a multi-stack Turing machine.** -/
theorem Decidable.tm2Decidable {P : ℕ → Prop} (h : Decidable P) :
    Cslib.Decidability.TM2Decidable P :=
  Cslib.Decidability.tm2Decidable_iff_computablePred.mpr h.computablePred

/-- **A URM-recognizable predicate is recognizable by a single-tape Turing machine.** -/
theorem Recognizable.singleTapeRecognizable {P : ℕ → Prop} (h : Recognizable P) :
    Cslib.Decidability.SingleTapeRecognizable P :=
  Cslib.Decidability.singleTapeRecognizable_iff_rePred.mpr h.rePred

/-- **A URM-recognizable predicate is recognizable by a multi-stack Turing machine.** -/
theorem Recognizable.tm2Recognizable {P : ℕ → Prop} (h : Recognizable P) :
    Cslib.Decidability.TM2Recognizable P :=
  Cslib.Decidability.tm2Recognizable_iff_rePred.mpr h.rePred

end Main

end Cslib.URM
