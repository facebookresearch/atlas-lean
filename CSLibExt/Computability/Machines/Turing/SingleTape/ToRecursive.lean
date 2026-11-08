/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.Computability.Machines.Turing.SingleTape.Classes
public import MathlibExt.Computability.TuringMachine.Recursive.OfTM2
public import Mathlib.Computability.RE

/-!
# Single-tape Turing machines are recursive

Runs of CSLib's single-tape machines (`Cslib.Turing.SingleTapeTM`) are recursive: the halting
set of a machine is recursively enumerable, the final tape of a run is a partial recursive
function of the input word, and so every predicate that a single-tape machine recognizes
(decides) is `REPred` (`ComputablePred`). This is one direction of the correspondence
between the single-tape classes and Mathlib's; the converse, that recursive predicates have
single-tape recognizers and deciders, lives in `OfRecursive`, and `Bridge` combines the two.

A configuration is coded (`SingleTapeTM.CodedCfg`) as its state, the symbol under the head, and
the cell lists to the left and right of the head, the underlying lists of the two `StackTape`s.
The coded step (`SingleTapeTM.codedStep`) mirrors `SingleTapeTM.step` on these lists; it is
primitive recursive because states and symbols are finite. Mathlib's `StateTransition.eval` of a
computable step function is partial recursive (`Partrec.fix`), and the coding commutes with
`step`, so `StateTransition.tr_eval'` turns the evaluation of the coded step into that of the
machine (`SingleTapeTM.eval_codedStep`).

## Main definitions

- `Cslib.Turing.SingleTapeTM.CodedCfg`, `Cslib.Turing.SingleTapeTM.Cfg.toCodedCfg` : coded
  configurations.
- `Cslib.Turing.SingleTapeTM.codedCons`, `Cslib.Turing.SingleTapeTM.codedStep` : `StackTape.cons`
  and `SingleTapeTM.step` on codes.

## Main results

- `Cslib.Turing.StackTape.head_eq_headI`, `Cslib.Turing.StackTape.toList_tail`,
  `Cslib.Turing.StackTape.toList_cons` : `StackTape` operations on underlying lists.
- `Cslib.Turing.SingleTapeTM.haltsOn_iff_dom_eval`, `Cslib.Turing.SingleTapeTM.outputs_iff_mem_eval`
  : halting and outputs through `StateTransition.eval tm.step`.
- `Cslib.Turing.SingleTapeTM.primrec_codedCons` : `StackTape.cons` on codes is primitive recursive.
- `Cslib.Turing.SingleTapeTM.primrec_map_encodeNat` : binary codes written through `ι` are
  primitive recursive.
- `Cslib.Turing.SingleTapeTM.codedStep_toCodedCfg`, `Cslib.Turing.SingleTapeTM.primrec_codedStep`,
  `Cslib.Turing.SingleTapeTM.eval_codedStep` : the coded step agrees with `step`, is primitive
  recursive, and evaluates like the machine.
- `Cslib.Turing.SingleTapeTM.partrec_eval` : the final tape is partial recursive in the input word.
- `Cslib.Turing.SingleTapeTM.rePred_haltsOn`, `Cslib.Turing.SingleTapeTM.rePred_haltsOn_encodeNat`
  : halting sets are r.e., on input words and on binary codes of natural numbers.
- `Cslib.Decidability.SingleTapeRecognizable.rePred`,
  `Cslib.Decidability.SingleTapeDecidable.computablePred` : the single-tape classes lie inside
  Mathlib's `REPred` and `ComputablePred`.
-/

@[expose] public section

set_option autoImplicit false

open Relation Computability MetaMathlibExt.TM2Recursive

namespace Cslib.Turing

/-- `StackTape.cons` on underlying lists: a blank pushed onto the empty tape is dropped. -/
def SingleTapeTM.codedCons {Symbol : Type} :
    Option Symbol → List (Option Symbol) → List (Option Symbol)
  | none, [] => []
  | x, l => x :: l

namespace StackTape

variable {Symbol : Type}

/-- The head of a `StackTape` is the head of its underlying list, blank on the empty tape. -/
theorem head_eq_headI (s : StackTape Symbol) : s.head = s.toList.headI := by
  obtain ⟨_ | _, _⟩ := s <;> rfl

/-- The underlying list of the tail of a `StackTape` is the tail of its underlying list. -/
theorem toList_tail (s : StackTape Symbol) : s.tail.toList = s.toList.tail := by
  obtain ⟨_ | _, _⟩ := s <;> rfl

/-- `StackTape.cons` is `SingleTapeTM.codedCons` on underlying lists. -/
theorem toList_cons (x : Option Symbol) (s : StackTape Symbol) :
    (cons x s).toList = SingleTapeTM.codedCons x s.toList := by
  obtain ⟨_ | _, _⟩ := s <;> cases x <;> rfl

end StackTape

namespace SingleTapeTM

variable {Symbol : Type}

/-- `codedCons x` is primitive recursive. -/
theorem primrec_codedCons [Primcodable Symbol] (x : Option Symbol) :
    Primrec (codedCons x) := by
  cases x with
  | none =>
    refine (Primrec.list_casesOn Primrec.id (Primrec.const []) (Primrec.list_cons.comp
      (Primrec.const none) (Primrec.list_cons.comp (Primrec.fst.comp Primrec.snd)
        (Primrec.snd.comp Primrec.snd))).to₂).of_eq fun l ↦ ?_
    cases l <;> rfl
  | some a =>
    exact (Primrec.list_cons.comp (Primrec.const (some a)) Primrec.id).of_eq fun l ↦ by
      cases l <;> rfl

/-- Binary codes of natural numbers written through `ι : Bool → Symbol` are primitive
recursive. -/
theorem primrec_map_encodeNat [Primcodable Symbol] (ι : Bool → Symbol) :
    Primrec fun n ↦ (encodeNat n).map ι :=
  Primrec.list_map primrec_encodeNat ((Primrec.dom_finite ι).comp Primrec.snd).to₂

variable [Inhabited Symbol] [Fintype Symbol] (tm : SingleTapeTM Symbol)

/-! ### Runs through `StateTransition.eval` -/

/-- `tm` halts on `l` iff Mathlib's evaluation of the step function from `initCfg l` is
defined. -/
theorem haltsOn_iff_dom_eval {l : List Symbol} :
    tm.HaltsOn l ↔ (StateTransition.eval tm.step (tm.initCfg l)).Dom := by
  rw [Part.dom_iff_mem]
  refine exists_congr fun c ↦ ?_
  rw [StateTransition.mem_eval]
  refine and_congr Iff.rfl ?_
  obtain ⟨_ | q, t⟩ := c <;> simp

/-- `tm` outputs `l'` on `l` iff the evaluation of the step function from `initCfg l` ends at
`haltCfg l'`. -/
theorem outputs_iff_mem_eval {l l' : List Symbol} :
    tm.Outputs l l' ↔ tm.haltCfg l' ∈ StateTransition.eval tm.step (tm.initCfg l) := by
  rw [StateTransition.mem_eval]
  exact (and_iff_left rfl).symm

/-! ### Coded configurations -/

/-- A configuration coded as its state, the symbol under the head, and the underlying lists of
the tapes to the left and to the right of the head. -/
abbrev CodedCfg : Type :=
  Option tm.State × Option Symbol × List (Option Symbol) × List (Option Symbol)

/-- The code of a configuration. -/
def Cfg.toCodedCfg {tm : SingleTapeTM Symbol} (c : tm.Cfg) : tm.CodedCfg :=
  (c.state, c.BiTape.head, c.BiTape.left.toList, c.BiTape.right.toList)

/-- One step on codes, following `step`: in a running state, write, move and change state as
`tm.tr` says; a halted configuration has no successor. -/
def codedStep : tm.CodedCfg → Option tm.CodedCfg
  | (none, _) => none
  | (some q, h, L, R) =>
    some <| match tm.tr q h with
      | (⟨wr, none⟩, q') => (q', wr, L, R)
      | (⟨wr, some .left⟩, q') => (q', L.headI, L.tail, codedCons wr R)
      | (⟨wr, some .right⟩, q') => (q', R.headI, codedCons wr L, R.tail)

/-- The coded step agrees with `step` on codes. -/
theorem codedStep_toCodedCfg (c : tm.Cfg) :
    tm.codedStep c.toCodedCfg = (tm.step c).map Cfg.toCodedCfg := by
  obtain ⟨_ | q, t⟩ := c
  · rfl
  · rcases ht : tm.tr q t.head with ⟨⟨wr, _ | _ | _⟩, q'⟩ <;>
      simp only [step, ht, Option.map_some, Cfg.toCodedCfg, codedStep, BiTape.write,
        BiTape.optionMove, BiTape.move, BiTape.moveLeft, BiTape.moveRight,
        StackTape.head_eq_headI, StackTape.toList_tail, StackTape.toList_cons]

/-- The coded step is primitive recursive. -/
theorem primrec_codedStep [Primcodable Symbol] [Primcodable tm.State] :
    Primrec tm.codedStep := by
  have hLR : Primrec₂ fun (qh : Option tm.State × Option Symbol)
      (LR : List (Option Symbol) × List (Option Symbol)) ↦ tm.codedStep (qh.1, qh.2, LR) := by
    refine primrec₂_of_finite_left fun ⟨q, h⟩ ↦ ?_
    cases q with
    | none => exact Primrec.const none
    | some q =>
      refine Primrec.option_some.comp ?_
      obtain ⟨⟨wr, _ | _ | _⟩, q'⟩ := tm.tr q h
      · refine (Primrec.pair (Primrec.const q') (Primrec.pair (Primrec.const wr)
          (Primrec.pair Primrec.fst Primrec.snd))).of_eq fun _ ↦ rfl
      · refine (Primrec.pair (Primrec.const q') (Primrec.pair
          (Primrec.list_headI.comp Primrec.fst) (Primrec.pair (Primrec.list_tail.comp Primrec.fst)
            ((primrec_codedCons wr).comp Primrec.snd)))).of_eq fun _ ↦ rfl
      · refine (Primrec.pair (Primrec.const q') (Primrec.pair
          (Primrec.list_headI.comp Primrec.snd) (Primrec.pair
            ((primrec_codedCons wr).comp Primrec.fst) (Primrec.list_tail.comp Primrec.snd)))).of_eq
          fun _ ↦ rfl
  exact (hLR.comp (Primrec.pair Primrec.fst (Primrec.fst.comp Primrec.snd))
    (Primrec.snd.comp Primrec.snd)).of_eq fun _ ↦ rfl

/-- The coded step evaluates like the machine: its evaluation from the code of `c` is the code
of the evaluation of `step` from `c`. -/
theorem eval_codedStep (c : tm.Cfg) :
    StateTransition.eval tm.codedStep c.toCodedCfg =
      Cfg.toCodedCfg <$> StateTransition.eval tm.step c := by
  refine StateTransition.tr_eval' _ _ _ (StateTransition.fun_respects.mpr fun a ↦ ?_) c
  have e := tm.codedStep_toCodedCfg a
  cases h : tm.step a with
  | none => exact e.trans (congrArg _ h)
  | some b => exact TransGen.single (e.trans (congrArg _ h))

/-! ### Runs are partial recursive -/

/-- The code of the initial configuration is primitive recursive in the input word. -/
theorem primrec_toCodedCfg_initCfg [Primcodable Symbol] [Primcodable tm.State] :
    Primrec fun l : List Symbol ↦ (tm.initCfg l).toCodedCfg :=
  (Primrec.pair (Primrec.const (some tm.q₀)) (Primrec.pair Primrec.list_head? (Primrec.pair
    (Primrec.const []) (Primrec.list_map Primrec.list_tail
      (Primrec.option_some.comp Primrec.snd).to₂)))).of_eq fun l ↦ by cases l <;> rfl

/-- **The final tape of a run is partial recursive in the input word**: the head symbol and the
cell lists left and right of the head of the configuration where `tm` halts on `l`. -/
theorem partrec_eval [Primcodable Symbol] :
    Partrec fun l : List Symbol ↦ (StateTransition.eval tm.step (tm.initCfg l)).map
      fun c ↦ (c.BiTape.head, c.BiTape.left.toList, c.BiTape.right.toList) := by
  let _ : Primcodable tm.State := Primcodable.ofEquiv _ (Fintype.equivFin _)
  have hstep : Primrec fun c : tm.CodedCfg ↦ (tm.codedStep c).elim (Sum.inl c) Sum.inr :=
    (Primrec.option_casesOn (primrec_codedStep tm) Primrec.sumInl
      (Primrec.sumInr.comp Primrec.snd).to₂).of_eq fun c ↦ by cases tm.codedStep c <;> rfl
  have hfix : Partrec (StateTransition.eval tm.codedStep) := Partrec.fix hstep.to_comp.partrec
  refine ((hfix.comp (primrec_toCodedCfg_initCfg tm).to_comp).map
    (Computable.snd.comp Computable.snd).to₂).of_eq
    fun l ↦ ?_
  rw [eval_codedStep]
  exact Part.map_map _ _ _

/-- **The halting set of a single-tape machine is r.e.**, on input words. -/
theorem rePred_haltsOn [Primcodable Symbol] : REPred tm.HaltsOn :=
  (partrec_eval tm).dom_re.of_eq fun l ↦ by rw [Part.map_Dom, haltsOn_iff_dom_eval]

/-- **The halting set of a single-tape machine is r.e.**, on binary codes `encodeNat n` of natural
numbers written through any `ι : Bool → Symbol`. -/
theorem rePred_haltsOn_encodeNat (ι : Bool → Symbol) :
    REPred fun n : ℕ ↦ tm.HaltsOn ((encodeNat n).map ι) := by
  let _ : Primcodable Symbol := Primcodable.ofEquiv _ (Fintype.equivFin _)
  exact Partrec.comp (rePred_haltsOn tm) (primrec_map_encodeNat ι).to_comp

end SingleTapeTM

end Cslib.Turing

namespace Cslib.Decidability

open Encodable Cslib.Turing

variable {α : Type*} [Primcodable α] {p : α → Prop}

/-- **A predicate recognized by a single-tape machine is r.e.** -/
theorem SingleTapeRecognizable.rePred (h : SingleTapeRecognizable p) : REPred p := by
  obtain ⟨Symbol, _, _, ι, -, tm, hp⟩ := h
  have : REPred fun a : α ↦ tm.HaltsOn ((encodeNat (encode a)).map ι) :=
    Partrec.comp (tm.rePred_haltsOn_encodeNat ι) Computable.encode
  exact this.of_eq hp

/-- **A predicate decided by a single-tape machine is computable.** The decider's answer is the
symbol under the head of its final tape. -/
theorem SingleTapeDecidable.computablePred (h : SingleTapeDecidable p) : ComputablePred p := by
  classical
  obtain ⟨Symbol, _, _, ι, hι, tm, hp⟩ := h
  let _ : Primcodable Symbol := Primcodable.ofEquiv _ (Fintype.equivFin _)
  have hin : Computable fun a : α ↦ (encodeNat (encode a)).map ι :=
    ((SingleTapeTM.primrec_map_encodeNat ι).comp Primrec.encode).to_comp
  have hans : Primrec fun t : Option Symbol × List (Option Symbol) × List (Option Symbol) ↦
      decide (t.1 = some (ι true)) :=
    (Primrec.dom_finite fun o : Option Symbol ↦ decide (o = some (ι true))).comp Primrec.fst
  refine Computable.computablePred (((tm.partrec_eval.comp hin).map
    (hans.comp Primrec.snd).to_comp.to₂).of_eq_tot fun a ↦ ?_)
  obtain ⟨b, hb, hbp⟩ := hp a
  refine (Part.mem_map_iff _).mpr ⟨_, Part.mem_map _ ((tm.outputs_iff_mem_eval).mp hb), ?_⟩
  simp [SingleTapeTM.haltCfg, BiTape.mk₁, hι.eq_iff, ← hbp]

end Cslib.Decidability
