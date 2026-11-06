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

/-- **Tag of an instruction code.** For every URM instruction $I$, unpairing the code of $I$
gives first component $0$ if $I$ is a zero instruction $Z\,n$, $1$ if it is a successor
instruction $S\,n$, $2$ if it is a transfer $T\,m\,n$, and $3$ if it is a jump $J\,m\,n\,q$. -/
theorem encodeInstr_unpair_fst (instr : Instr) :
    (encodeInstr instr).unpair.1 = match instr with
      | .Z _ => 0 | .S _ => 1 | .T _ _ => 2 | .J _ _ _ => 3 := by
  cases instr <;> simp [encodeInstr, Nat.unpair_pair]

/-- **Payload of an instruction code.** Write $\langle a, b \rangle$ for the pairing of natural
numbers $a$ and $b$. For every URM instruction $I$, unpairing the code of $I$ gives second
component $n$ if $I$ is $Z\,n$ or $S\,n$, $\langle m, n \rangle$ if $I$ is $T\,m\,n$, and
$\langle m, \langle n, q \rangle \rangle$ if $I$ is $J\,m\,n\,q$. -/
theorem encodeInstr_unpair_snd (instr : Instr) :
    (encodeInstr instr).unpair.2 = match instr with
      | .Z n => n | .S n => n | .T m n => Nat.pair m n
      | .J m n q => Nat.pair m (Nat.pair n q) := by
  cases instr <;> simp [encodeInstr, Nat.unpair_pair]

/-- **One coded URM step.** A coded state is a program counter $k$ together with a list $r$ of
register contents (in use, the contents of registers $0, \dots, R$, where $R$ is the register bound
of the program), and a program is given by the list $c$ of its instruction codes. Write $c_k$ for
entry $k$ of $c$, and $r_j$ for entry $j$ of $r$, read as $0$ when $j$ is past the end of $r$;
setting an entry past the end of $r$ leaves $r$ unchanged. If $k$ is at least the length of $c$,
the state is halted and has no successor. Otherwise unpair the code $c_k$ as $(i, a)$. If
$i = 0$, the successor is $(k + 1, r')$ where $r'$ is $r$ with entry $a$ set to $0$. If $i = 1$,
it is $(k + 1, r')$ where $r'$ is $r$ with entry $a$ set to $r_a + 1$. If $i = 2$, unpair $a$ as
$(m, n)$; the successor is $(k + 1, r')$ where $r'$ is $r$ with entry $n$ set to $r_m$. If
$i = 3$, unpair $a$ as $(m, b)$ and $b$ as $(n, q)$; the successor is $(q, r)$ if $r_m = r_n$ and
$(k + 1, r)$ otherwise. Any other tag $i$ (which never occurs for a genuine instruction code)
gives no successor. -/
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

/-- **Register bound.** The register bound $R$ of a URM program $p$ is the sum, over the
instructions of $p$, of the largest register index each instruction refers to. Every register
that an instruction of $p$ can read or write is at most $R$. -/
def regBound : ℕ := (p.map Instr.maxRegister).sum

/-- **Register list.** For a URM program $p$ with register bound $R$, the register list of a
register state $\sigma$ is the list $(\sigma(0), \sigma(1), \dots, \sigma(R))$ of the contents of
registers $0, \dots, R$. -/
abbrev toRegs (σ : Regs) : List ℕ := (List.range (regBound p + 1)).map σ

/-- **Coded machine state.** For a URM program $p$ with register bound $R$, the coded state of a
machine state $s$ is the pair consisting of the program counter of $s$ and the register list
$(r_0, \dots, r_R)$ of the contents of registers $0, \dots, R$ of $s$. -/
abbrev toCoded (s : State) : ℕ × List ℕ := (s.pc, toRegs p s.regs)

/-- **Decoding a coded state.** A coded state is a pair $(c, \ell)$ of a natural number $c$ and a
list $\ell$ of natural numbers. Its machine state has program counter $c$, and register $n$
holds the $n$-th entry of $\ell$ (counting from $0$) when $n$ is less than the length of $\ell$,
and $0$ otherwise. -/
abbrev ofCoded (c : ℕ × List ℕ) : State := ⟨c.1, fun n ↦ c.2.getD n 0⟩

/-- **Length of the register list.** For a URM program $p$ with register bound $R$ and a register
state $\sigma$, the register list of $\sigma$ (the contents of registers $0, \dots, R$) has length
$R + 1$. -/
theorem length_toRegs (σ : Regs) : (toRegs p σ).length = regBound p + 1 := by
  simp [toRegs]

/-- **Reading the register list.** Let $p$ be a URM program with register bound $R$ and
$\sigma$ a register state. For every $n$, the entry at position $n$ of the register list of
$\sigma$, read with default $0$, is $\sigma(n)$ if $n \le R$ and $0$ otherwise. -/
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

/-- **Updating a register updates the register list.** Let $p$ be a URM program with register
bound $R$, let $\sigma$ be a register state, and let $n \le R$ and $v$ be natural numbers. The
register list of the state obtained from $\sigma$ by setting register $n$ to $v$ equals the
register list of $\sigma$ with its entry at position $n$ replaced by $v$. -/
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

/-- **Instructions stay within the register bound.** For a URM program $p$ with register bound
$R$ and every instruction $I$ of $p$, the largest register index referenced by $I$ is at most
$R$. -/
theorem maxRegister_le_regBound {instr : Instr} (h : instr ∈ p) :
    instr.maxRegister ≤ regBound p := by
  apply List.single_le_sum (fun _ _ ↦ Nat.zero_le _)
  exact List.mem_map_of_mem h

/-- **Written registers lie within the register bound.** Let $p$ be a URM program with register
bound $R$. If an instruction of $p$ writes to register $n$, then $n \le R$. -/
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

/-- **Registers read by a program lie within the register bound.** Let $p$ be a URM program. If
$n$ is a register read by some instruction of $p$, then $n$ is at most the register bound of
$p$. -/
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

/-- **Decoding and re-encoding a coded state gives it back.** Let $p$ be a URM program with
register bound $R$, and let $c$ be a coded state: a program counter together with a list of
register contents. If the list has length $R + 1$, then the coded state, with respect to $p$, of
the machine state decoded from $c$ is $c$. -/
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

/-- **A state that can step is running.** If a state $s$ of a URM program $p$ makes a step to some
state, then the program counter of $s$ is less than the number of instructions of $p$. -/
theorem pc_lt_of_step {s s' : State} (h : Step p s s') : s.pc < p.length := by
  cases h with
  | zero hi | succ hi | transfer hi | jump_eq hi _ | jump_ne hi _ =>
    by_contra hc
    simp only [not_lt] at hc
    rw [List.getElem?_eq_none_iff.2 hc] at hi
    simp at hi

/-- **Instruction codes by position.** If the URM program $p$ has instruction $I$ at position
$pc$, then the entry at position $pc$ of the list of instruction codes of $p$, read with
default $0$, is the code of $I$. -/
theorem getD_codes {pc : ℕ} {instr : Instr} (hi : p[pc]? = some instr) :
    (p.map encodeInstr).getD pc 0 = encodeInstr instr := by
  rw [List.getD_eq_getElem?_getD, List.getElem?_map, hi]
  rfl

/-- **A machine step is a coded step.** Let $p$ be a URM program, let $R$ be the sum over the
instructions of $p$ of the largest register index each one mentions, and let $s'$ be a state
that $p$ reaches from the state $s$ in one step. Then the coded step, run on the list of codes of
the instructions of $p$, sends the coded state of $s$ (its program counter together with the list
of the contents of its registers $0, \dots, R$) to the coded state of $s'$. -/
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

/-- **A coded step is a machine step.** Let $p$ be a URM program and $s$ a machine state. If one
coded URM step, run on the list of codes of the instructions of $p$ from the coded state of $s$,
yields $c'$, then there is a machine state $s'$ such that $p$ steps from $s$ to $s'$ in one step
and the coded state of $s'$ is $c'$. -/
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

/-- **URM-decidable predicate.** A predicate $P$ on the natural numbers is URM-decidable when
some URM program computes its characteristic function: started on any input $n$ (register $0$
holding $n$, all other registers $0$), the program halts, and register $0$ then holds $1$ if
$P(n)$ holds and $0$ otherwise. -/
def Decidable (P : ℕ → Prop) : Prop :=
  ∃ prog : Program, ∀ n, eval prog [n] = Cslib.Decidability.charFun P n

/-- **URM-recognizable predicates.** A predicate $P$ on the natural numbers is URM-recognizable
when there is a URM program that, started with input $n$ in register $0$ and every other register
$0$, halts if and only if $P(n)$ holds. -/
def Recognizable (P : ℕ → Prop) : Prop :=
  ∃ prog : Program, ∀ n, (eval prog [n]).Dom ↔ P n

/-! ### Bounded execution -/

section Exec

variable (p : Program)

/-- **One-step function on coded states.** Given a list of instruction codes, the one-step
function sends a coded state $s$ to the result of one coded URM step from $s$ when that step is
defined, and leaves $s$ unchanged when it is not (in particular when $s$ is halted). -/
def stepFn (codes : List ℕ) : ℕ × List ℕ → ℕ × List ℕ :=
  fun s ↦ (codedStep codes s.1 s.2).getD s

/-- **The one-step function is primitive recursive.** For every list of natural numbers, read as
instruction codes, the function on coded states (pairs of a program counter and a register list)
that sends a coded state to its successor under one coded step, and a coded state with no
successor to itself, is primitive recursive. -/
theorem primrec_stepFn (codes : List ℕ) : Primrec (stepFn codes) := by
  change Primrec fun s : ℕ × List ℕ ↦ (codedStep codes s.1 s.2).getD s
  exact Primrec₂.comp Primrec.option_getD (primrec_codedStep codes) Primrec.id

/-- **Bounded execution.** For a list of instruction codes, a number $t$ and a coded state $s$,
bounded execution applies the one-step function for these codes $t$ times, starting from
$s$. -/
def execN (codes : List ℕ) (t : ℕ) (s : ℕ × List ℕ) : ℕ × List ℕ :=
  (stepFn codes)^[t] s

/-- **Bounded execution unfolds by one step.** For a list of instruction codes, a number $t$
and a coded state $s$, bounded execution for $t + 1$ steps from $s$ is the one-step function
applied to the result of bounded execution for $t$ steps from $s$. -/
theorem execN_succ (codes : List ℕ) (t : ℕ) (s : ℕ × List ℕ) :
    execN codes (t + 1) s = stepFn codes (execN codes t s) :=
  Function.iterate_succ_apply' _ _ _

/-- **Initial coded state.** For a URM program $p$ with register bound $R$ and an input $x$,
the initial coded state has program counter $0$ and register list $(x, 0, \dots, 0)$ of
length $R + 1$: register $0$ holds $x$ and registers $1, \dots, R$ hold $0$. -/
def initCoded (x : ℕ) : ℕ × List ℕ :=
  (0, (List.range (regBound p + 1)).map fun n ↦ if n = 0 then x else 0)

/-- **The initial coded state is primitive recursive in the input.** -/
theorem primrec_initCoded : Primrec fun x ↦ initCoded p x := by
  refine (Primrec.pair (Primrec.const 0) ?_)
  refine (Primrec.list_map (Primrec.const (List.range (regBound p + 1))) ?_)
  exact Primrec.ite (Primrec.eq.comp Primrec.snd (Primrec.const 0)) Primrec.fst
    (Primrec.const 0)

/-- **Bounded execution is primitive recursive in the input and the step bound.** For a URM
program $p$, the bounded execution of $p$ for $t$ steps ($t$ iterations of the one-step
function on the list of instruction codes of $p$), started from the initial coded state for
input $x$, is a primitive recursive function of the pair $(x, t)$. -/
theorem primrec_execN : Primrec fun a : ℕ × ℕ ↦
    execN (p.map encodeInstr) a.2 (initCoded p a.1) :=
  Primrec.nat_iterate Primrec.snd ((primrec_initCoded p).comp Primrec.fst)
    ((primrec_stepFn _).comp Primrec.snd)

/-- **The initial coded state codes the initial machine state.** For a URM program $p$ and an
input $x$, the initial coded state for $x$ equals the coded state of the initial machine state
with input list $[x]$. -/
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

/-- **Bounded execution only reaches codes of reachable states.** Let $p$ be a URM program,
$x$ an input and $t$ a natural number. Then there is a machine state $s'$, reachable from the
initial state with input list $[x]$ by steps of $p$, whose coded state equals the result of
bounded execution for $t$ steps on the instruction codes of $p$ from the initial coded state
for $x$. -/
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

/-- **A halted coded state gives a halting machine run.** Let $p$ be a URM program, $x$ an input
and $t$ a number. If bounded execution for $t$ steps on the instruction codes of $p$ from the
initial coded state for $x$ reaches a program counter at least the length of the list of
instruction codes, then $p$ halts on the input list $[x]$. -/
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

/-- **Every reachable state is reached by bounded execution.** Let $p$ be a URM program and $x$
an input. If a machine state $s$ is reachable from the initial state with input list $[x]$ by
steps of $p$, then for some number $t$, bounded execution for $t$ steps on the instruction codes
of $p$ from the initial coded state for $x$ gives the coded state of $s$. -/
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

/-- **Bounded URM execution is stable once halted.** Let $c$ be a list of instruction codes, $s$
a coded state and $t$ a natural number. If after $t$ steps of bounded execution of $c$ from $s$
the program counter is at least the length of $c$, then $t + 1$ steps of bounded execution of $c$
from $s$ give the same coded state as $t$ steps. -/
theorem execN_succ_of_halted (codes : List ℕ) {t : ℕ} {s : ℕ × List ℕ}
    (h : codes.length ≤ (execN codes t s).1) : execN codes (t + 1) s = execN codes t s := by
  rw [execN_succ]
  change (codedStep codes (execN codes t s).1 (execN codes t s).2).getD _ = execN codes t s
  have hnone : codedStep codes (execN codes t s).1 (execN codes t s).2 = Option.none := by
    unfold codedStep
    rw [ite_eq_right (by omega : ¬ (execN codes t s).1 < codes.length)]
  rw [hnone]
  rfl

/-- **Bounded URM execution stays at its halted value.** Let $c$ be a list of instruction codes,
$s$ a coded state, and $t_1 \le t_2$ natural numbers. If after $t_1$ steps of bounded execution
of $c$ from $s$ the program counter is at least the length of $c$, then $t_2$ steps of bounded
execution of $c$ from $s$ give the same coded state as $t_1$ steps. -/
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

/-- **Output after a given number of steps.** For a URM program $p$, an input $x$ and a number
$t$, run bounded execution for $t$ steps on the instruction codes of $p$ from the initial coded
state for $x$. If the resulting program counter is less than the length of the list of
instruction codes, the program is still running and there is no output; otherwise the output
is the entry at position $0$ of the resulting register list, read with default $0$. -/
def haltedOutput (x t : ℕ) : Option ℕ :=
  if (execN (p.map encodeInstr) t (initCoded p x)).1 < (p.map encodeInstr).length then
    Option.none
  else some ((execN (p.map encodeInstr) t (initCoded p x)).2.getD 0 0)

/-- **The URM output after a given number of steps is computable.** For every URM program $p$,
the function sending an input $x$ and a step count $t$ to the output of $p$ on $x$ after $t$ steps
(nothing while $p$ is still running, the contents of register $0$ once it has halted) is a
computable function of the pair $(x, t)$.

Unbounded search over $t$ then shows that URM evaluation is partial recursive. -/
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

/-- **A URM-computable partial function is partial recursive.** Let $f$ be a partial function
from $\mathbb{N}$ to $\mathbb{N}$. Suppose some URM program has the following property for every
natural number $x$: started with $x$ in register $0$ and all other registers $0$, it halts
exactly when $f(x)$ is defined, and then it holds $f(x)$ in register $0$. Then $f$ is partial
recursive.

The URM evaluation is the unbounded search for the first halting step of the coded execution. -/
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

/-- **A URM-decidable predicate is computable.** If a predicate $P$ on the natural numbers is
URM-decidable, then it is a computable predicate: its Boolean decision function, sending $n$ to
whether $P(n)$ holds, is computable. -/
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
