/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.Computability.Machines.Turing.SingleTape.Comp
public import CSLibExt.Computability.Machines.Turing.SingleTape.OfTM0
public import CSLibExt.Computability.Decidability.TM0Halting
public import MathlibExt.Computability.TuringMachine.Recursive.ToTM2
public import MathlibExt.Computability.RE

/-!
# Recursive predicates are decided and recognized by single-tape machines

The forward half of the bridge between CSLib's single-tape machines (`SingleTapeTM`) and
recursion theory: every `REPred` is `SingleTapeRecognizable` and every `ComputablePred` is
`SingleTapeDecidable`.

The machines come from the Turing–Kleene equivalence for Mathlib's multi-stack machines
(`FinTM2`), translated to single-tape machines by Mathlib's `TM2to1` and `TM1to0` (composed in
`MetaMathlibExt.TM2ToTM0.tr`) and run on a `SingleTapeTM` by `SingleTapeTM.ofTM0`. Two
adapters connect the conventions:

* **Input.** `TM2to1` lays the input stack out bottom first, so a stack holding the list `L` is
  the tape `L.reverse` (`TM2to1.trInit`), its leftmost cell flagged as the bottom. The emulation is
  therefore started on the stack `w.reverse ++ [true]` for the input word `w`: its tape is the
  flagged cell for the last `true` followed by `w` itself, so the single-tape machine only has to
  prepend one cell (`consComputer`) to its input. The tape alphabet is the non-blank cells of
  `TM2to1`, with the input bit `b` the cell holding `b` on the input stack (`inCell`). On the
  recursion side, `w.reverse ++ [true]` is the binary code of a number (`bitsVal`), from which `w`
  is computably recovered.
* **Output (deciders).** At the halt the multi-stack machine has emptied every stack except its
  output stack, which holds `encodeNat 1 = [true]` or `encodeNat 0 = []`; the emulation's tape is
  then the single bottom cell, and a one-step machine (`answerTM`) replaces it by the answer bit.

## Main results

- `SingleTapeTM.consComputer`, `SingleTapeTM.consComputer_outputsWithinTime`: prepend a symbol.
- `Cslib.Decidability.SingleTapeRecognizable.of_rePred`: r.e. predicates are recognizable.
- `Cslib.Decidability.SingleTapeDecidable.of_computablePred`: computable predicates are decidable.
-/

@[expose] public section

set_option autoImplicit false

open Relation Turing Computability Encodable

namespace Cslib.Turing.SingleTapeTM

variable {Symbol : Type} [Inhabited Symbol] [Fintype Symbol]

/-! ### Prepending a symbol -/

/-- The machine that prepends the symbol `c` to its input: it steps left and writes `c`. -/
def consComputer (c : Symbol) : SingleTapeTM Symbol where
  State := Bool
  q₀ := false
  tr q s := match q with
    | false => (⟨s, some .left⟩, some true)
    | true => (⟨some c, none⟩, none)

omit [Inhabited Symbol] [Fintype Symbol] in
/-- Stepping left from the start of a word and writing `c` gives the word with `c` prepended. -/
theorem write_moveLeft_mk₁ (c : Symbol) (l : List Symbol) :
    (((BiTape.mk₁ l).write (BiTape.mk₁ l).head).optionMove (some .left)).write (some c) =
      BiTape.mk₁ (c :: l) := by
  cases l <;> rfl

/-- `consComputer c` outputs `c :: l` on `l`, in two steps. -/
theorem consComputer_outputsWithinTime (c : Symbol) (l : List Symbol) :
    (consComputer c).OutputsWithinTime l (c :: l) 2 := by
  refine RelatesWithinSteps.of_relatesInSteps (RelatesInSteps.head _ _ _ _ rfl
    (RelatesInSteps.single ?_))
  simp only [TransitionRelation, step, consComputer, haltCfg, Option.some.injEq]
  congr 1
  exact write_moveLeft_mk₁ c l

/-- `consComputer c` outputs `c :: l` on `l`. -/
theorem consComputer_outputs (c : Symbol) (l : List Symbol) :
    (consComputer c).Outputs l (c :: l) :=
  let ⟨_, _, h⟩ := consComputer_outputsWithinTime c l
  h.reflTransGen

end Cslib.Turing.SingleTapeTM

namespace Cslib.Turing.SingleTapeTM.OfTM2

open MetaMathlibExt.TM2Recursive

/-! ### The input stack of the emulation as a number -/

/-- The number whose binary code is the bit list `w.reverse ++ [true]`: the input stack the
single-tape emulation starts on for the input word `w`. -/
def inputCode (w : List Bool) : ℕ := bitsVal (w.reverse ++ [true])

/-- A bit list ending in `true` is the binary code of its value. (Private: the general fact for
lists not ending in `false` is `Cslib.Complexity.Karp.EmitSS.encodeNat_bitsVal`, which lives in a
Karp module; both could move next to `bitsVal` in MathlibExt.) -/
private theorem encodeNat_bitsVal_append_true (l : List Bool) :
    encodeNat (bitsVal (l ++ [true])) = l ++ [true] := by
  induction l with
  | nil => rfl
  | cons b l ih =>
    have hpos : bitsVal (l ++ [true]) ≠ 0 := fun h ↦ by
      rw [h, encodeNat_zero] at ih
      simp at ih
    have hval : bitsVal (b :: l ++ [true]) = 2 * bitsVal (l ++ [true]) + cond b 1 0 := rfl
    rw [hval, encodeNat_eq_cons (by cases b <;> simp [hpos])]
    cases b <;> simp [Nat.mul_add_div, ih]

theorem encodeNat_inputCode (w : List Bool) : encodeNat (inputCode w) = w.reverse ++ [true] :=
  encodeNat_bitsVal_append_true _

/-- `inputCode` is undone by reversing the binary code and dropping its first bit. -/
theorem reverse_tail_encodeNat_inputCode (w : List Bool) :
    (encodeNat (inputCode w)).reverse.tail = w := by
  rw [encodeNat_inputCode]
  simp

/-- Reading back the input word's value from the multi-stack machine's input number: reverse the
binary code and drop its first bit (`inputCode` in the other direction). -/
def inputDecode (m : ℕ) : ℕ := bitsVal (encodeNat m).reverse.tail

theorem computable_inputDecode : Computable inputDecode :=
  (primrec_bitsVal.comp (Primrec.list_tail.comp
    (Primrec.list_reverse.comp primrec_encodeNat))).to_comp

theorem inputDecode_inputCode (n : ℕ) : inputDecode (inputCode (encodeNat n)) = n := by
  rw [inputDecode, reverse_tail_encodeNat_inputCode, bitsVal_encodeNat]

end Cslib.Turing.SingleTapeTM.OfTM2

namespace Cslib.Turing.SingleTapeTM.OfTM2

open MetaMathlibExt MetaMathlibExt.TM2Recursive
open scoped MetaMathlibExt.TM2ToTM0

/-! ### The single-tape emulation of a multi-stack machine -/

section Emulation

variable (tm : FinTM2) [∀ k, Fintype (tm.Γ k)]

attribute [local instance] FinTM2.kFin FinTM2.ΛFin FinTM2.σFin

/-- Equality of `TM2to1` cells, decided classically (scoped). -/
noncomputable scoped instance instDecidableEqΓ' : DecidableEq (TM2to1.Γ' tm.K tm.Γ) :=
  Classical.decEq _

/-- The bottom-flag cell with all stacks empty is not blank (scoped). -/
scoped instance instInhabitedNonBlankΓ' : Inhabited (NonBlank (TM2to1.Γ' tm.K tm.Γ)) :=
  ⟨⟨(true, fun _ ↦ none), fun h ↦ Bool.noConfusion (congrArg Prod.fst h)⟩⟩

variable (e : tm.Γ tm.k₀ ≃ Bool)

/-- The tape symbol of the input bit `b`: the cell holding `b` on the input stack. -/
def inCell (b : Bool) : NonBlank (TM2to1.Γ' tm.K tm.Γ) :=
  ⟨(false, Function.update (fun _ ↦ none) tm.k₀ (some (e.symm b))), fun h ↦ by
    have := congrFun (congrArg Prod.snd h) tm.k₀
    simp only [Function.update_self] at this
    cases this⟩

/-- The bottom cell of the emulation's start tape: the flagged cell holding `true` on the input
stack. -/
def botCell : NonBlank (TM2to1.Γ' tm.K tm.Γ) :=
  ⟨(true, Function.update (fun _ ↦ none) tm.k₀ (some (e.symm true))),
    fun h ↦ Bool.noConfusion (congrArg Prod.fst h)⟩

omit [∀ k, Fintype (tm.Γ k)] in
theorem inCell_injective : Function.Injective (inCell tm e) := fun b b' h ↦ by
  have := congrFun (congrArg Prod.snd (congrArg Subtype.val h)) tm.k₀
  simpa [inCell] using this

/-- The finite set of `TM0` states the emulation visits. -/
noncomputable abbrev emuSupport : Finset (TM1to0.Λ' (TM2to1.tr tm.m)) :=
  TM1to0.trStmts (TM2to1.tr tm.m) (TM2to1.trSupp tm.m Finset.univ)

/-- The single-tape emulation of `tm` as a CSLib single-tape machine. -/
noncomputable def emuTM : SingleTapeTM (NonBlank (TM2to1.Γ' tm.K tm.Γ)) :=
  ofTM0 (TM2ToTM0.tr tm.m) (emuSupport tm)
    (TM2ToTM0.tr_supports tm.m (TM2ToTM0.supports_univ tm.m))

/-- The recognizer built from `tm`: prepend the bottom cell, then run the emulation. -/
noncomputable def recognizerTM : SingleTapeTM (NonBlank (TM2to1.Γ' tm.K tm.Γ)) :=
  compComputer (consComputer (botCell tm e)) (emuTM tm)

omit [∀ k, Fintype (tm.Γ k)] in
/-- The input word with the bottom cell prepended is the emulation's start tape for the input
stack `w.reverse ++ [true]`. -/
theorem map_val_botCell_cons (w : List Bool) :
    (botCell tm e :: w.map (inCell tm e)).map Subtype.val =
      TM2to1.trInit tm.k₀ ((w.reverse ++ [true]).map e.symm) := by
  simp only [TM2to1.trInit, List.map_append, List.map_reverse, List.reverse_append,
    List.reverse_reverse, List.map_cons, List.map_nil, List.reverse_singleton,
    List.singleton_append]
  refine congrArg₂ List.cons rfl ?_
  change List.map _ (List.map _ w) = List.map _ (List.map _ w)
  induction w with
  | nil => rfl
  | cons b w ih => exact congrArg₂ List.cons rfl ih

/-- **The recognizer halts iff the multi-stack machine does**, on the input stack
`w.reverse ++ [true]`. -/
theorem haltsOn_recognizerTM_iff (w : List Bool) :
    (recognizerTM tm e).HaltsOn (w.map (inCell tm e)) ↔
      TM2HaltsOn tm ((w.reverse ++ [true]).map e.symm) := by
  rw [recognizerTM, haltsOn_compComputer_iff (consComputer_outputs _ _), emuTM,
    haltsOn_ofTM0_iff, map_val_botCell_cons, TM2ToTM0.tr_eval_dom,
    Cslib.Decidability.tm2HaltsOn_iff_eval_dom]

/-! ### The emulation's final tape, and deciders -/

omit [∀ k, Fintype (tm.Γ k)] in
/-- **The emulation's final tape.** If `tm` halts at `c` on the input stack `L`, the `TM0`
emulation halts at a configuration whose tape is `Tape.mk' ∅ (addBottom L')`, where `L'` lays out
the stacks of `c`, each bottom first. -/
theorem exists_mem_eval_tr (L : List (tm.Γ tm.k₀)) {c : tm.Cfg}
    (hc : c ∈ StateTransition.eval tm.step (initList tm L)) :
    ∃ c₀ ∈ StateTransition.eval (TM0.step (TM2ToTM0.tr tm.m))
        (TM0.init (TM2to1.trInit tm.k₀ L)),
      ∃ L' : ListBlank (∀ k, Option (tm.Γ k)),
        (∀ k, L'.map (proj k) = ListBlank.mk ((c.stk k).map some).reverse) ∧
          c₀.Tape = Tape.mk' ∅ (TM2to1.addBottom L') := by
  rw [TM2ToTM0.initList_eq_init] at hc
  obtain ⟨b₂, hb, hb₂⟩ :=
    StateTransition.tr_eval (TM2to1.tr_respects tm.m) (TM2to1.trCfg_init tm.k₀ L) hc
  have h0 := StateTransition.tr_eval' _ _ _ (TM1to0.tr_respects (TM2to1.tr tm.m))
    (TM1.init (TM2to1.trInit tm.k₀ L))
  refine ⟨TM1to0.trCfg (TM2to1.tr tm.m) b₂, ?_, ?_⟩
  · have hinit : TM0.init (TM2to1.trInit tm.k₀ L) =
        TM1to0.trCfg (TM2to1.tr tm.m) (TM1.init (TM2to1.trInit tm.k₀ L)) := rfl
    rw [hinit, h0]
    exact Part.mem_map _ hb₂
  · obtain ⟨q, v, S⟩ := c
    cases hb with
    | mk L' hL' => exact ⟨L', hL', rfl⟩

omit [∀ k, Fintype (tm.Γ k)] in
/-- Stacks holding at most one symbol each make a one-cell tape: the bottom cell with the top of
every stack. -/
theorem addBottom_eq_of_length_le_one {S : ∀ k, List (tm.Γ k)} (hS : ∀ k, (S k).length ≤ 1)
    {L' : ListBlank (∀ k, Option (tm.Γ k))}
    (hL' : ∀ k, L'.map (proj k) = ListBlank.mk ((S k).map some).reverse) :
    TM2to1.addBottom L' = ListBlank.mk [((true, fun k ↦ (S k).head?) : TM2to1.Γ' tm.K tm.Γ)] := by
  have hrev : ∀ k, (S k).reverse = S k := fun k ↦ by
    have := hS k
    rcases h : S k with _ | ⟨x, _ | ⟨y, t⟩⟩ <;> simp_all
  refine ListBlank.ext fun i ↦ Prod.ext ?_ ?_
  · rcases i with _ | i
    · rw [ListBlank.nth_zero, TM2to1.addBottom_head_fst]
      rfl
    · rw [TM2to1.addBottom_nth_succ_fst]
      rfl
  · rw [TM2to1.addBottom_nth_snd]
    funext k
    rw [TM2to1.stk_nth_val i (hL' k), hrev]
    have := hS k
    rcases i with _ | i
    · change (S k)[0]? = (S k).head?
      rcases S k with _ | ⟨x, _⟩ <;> rfl
    · change (S k)[i + 1]? = none
      rcases h : S k with _ | ⟨x, _ | ⟨y, t⟩⟩
      · rfl
      · rfl
      · rw [h] at this
        simp at this

variable (e₁ : tm.Γ tm.k₁ ≃ Bool)

open scoped Classical in
/-- The answer read from a cell: whether it holds `true` on the output stack. -/
noncomputable def cellAnswer (x : NonBlank (TM2to1.Γ' tm.K tm.Γ)) : Bool :=
  decide (x.1.2 tm.k₁ = some (e₁.symm true))

/-- The answer machine: read the answer of the cell under the head, write the input-bit cell for
it, and halt (one step). -/
noncomputable def answerTM : SingleTapeTM (NonBlank (TM2to1.Γ' tm.K tm.Γ)) where
  State := Unit
  q₀ := ()
  tr _ s := (⟨some (inCell tm e (s.elim false (cellAnswer tm e₁))), none⟩, none)

/-- `answerTM` turns a one-cell tape into the answer bit of that cell. -/
theorem answerTM_outputs (x : NonBlank (TM2to1.Γ' tm.K tm.Γ)) :
    (answerTM tm e e₁).Outputs [x] [inCell tm e (cellAnswer tm e₁ x)] :=
  ReflTransGen.single rfl

/-- The decider built from `tm`: the recognizer, then the answer machine. -/
noncomputable def deciderTM : SingleTapeTM (NonBlank (TM2to1.Γ' tm.K tm.Γ)) :=
  compComputer (recognizerTM tm e) (answerTM tm e e₁)

/-- **The decider outputs the answer bit.** If `tm` halts on the input stack `w.reverse ++ [true]`
with output `out` of length at most one (and every other stack empty), the decider outputs, on the
input word `w`, the input-bit cell for an answer that is `true` exactly when `out` is `[true]`. -/
theorem deciderTM_outputs {w : List Bool} {out : List (tm.Γ tm.k₁)} (hout : out.length ≤ 1)
    (h : haltList tm out ∈
      StateTransition.eval tm.step (initList tm ((w.reverse ++ [true]).map e.symm))) :
    ∃ b : Bool, (deciderTM tm e e₁).Outputs (w.map (inCell tm e)) [inCell tm e b] ∧
      (b = true ↔ out.head? = some (e₁.symm true)) := by
  obtain ⟨c₀, hc₀, L', hL', ht⟩ := exists_mem_eval_tr tm _ h
  have hS : ∀ k, ((haltList tm out).stk k).length ≤ 1 := fun k ↦ by
    by_cases hk : k = tm.k₁
    · subst hk
      simpa [haltList] using hout
    · simp [haltList, hk]
  rw [addBottom_eq_of_length_le_one tm hS hL'] at ht
  let col : ∀ k, Option (tm.Γ k) := fun k ↦ ((haltList tm out).stk k).head?
  let cell : NonBlank (TM2to1.Γ' tm.K tm.Γ) :=
    ⟨(true, col), fun h ↦ Bool.noConfusion (congrArg Prod.fst h)⟩
  have hsim : (emuTM tm).Outputs (botCell tm e :: w.map (inCell tm e)) [cell] := by
    refine outputs_ofTM0 _ _ _ ?_ ?_ (c := c₀)
    · rw [map_val_botCell_cons]
      exact hc₀
    · rw [ht]
      rfl
  have hcol : col tm.k₁ = out.head? := by simp [col, haltList]
  refine ⟨cellAnswer tm e₁ cell, ((consComputer_outputs _ _).compComputer hsim).compComputer
    (answerTM_outputs tm e e₁ cell), ?_⟩
  simp only [cellAnswer, decide_eq_true_eq, ← hcol]
  rfl

end Emulation

end Cslib.Turing.SingleTapeTM.OfTM2

namespace Cslib.Decidability

open Cslib.Turing Cslib.Turing.SingleTapeTM Cslib.Turing.SingleTapeTM.OfTM2 MetaMathlibExt
  MetaMathlibExt.TM2Recursive
open scoped MetaMathlibExt.TM2ToTM0 Cslib.Turing.SingleTapeTM.OfTM2

attribute [local instance] FinTM2.kFin

variable {α : Type*} [Primcodable α]

/-- **R.e. predicates are recognizable by single-tape machines.** -/
theorem SingleTapeRecognizable.of_rePred {p : α → Prop} (hp : REPred p) :
    SingleTapeRecognizable p := by
  have hq : REPred fun m : ℕ ↦ ∃ a : α, encode a = inputDecode m ∧ p a :=
    MetaMathlibExt.REPred.exists (R := fun m a ↦ encode a = inputDecode m ∧ p a)
      (REPred.and (ComputablePred.to_re (ComputablePred.computable_iff.mpr
        ⟨fun x : ℕ × α ↦ encode x.2 == inputDecode x.1,
          Primrec.beq.to_comp.comp (Computable.encode.comp Computable.snd)
            (computable_inputDecode.comp Computable.fst), by funext x; simp⟩))
        (hp.comp Computable.snd))
  obtain ⟨tm, hfin, e, h⟩ := exists_finite_tm2HaltsOn_iff_of_rePred hq
  have : ∀ k, Fintype (tm.Γ k) := fun k ↦ Fintype.ofFinite _
  refine ⟨_, inferInstance, inferInstance, inCell tm e, inCell_injective tm e, recognizerTM tm e,
    fun a ↦ ?_⟩
  rw [haltsOn_recognizerTM_iff, ← encodeNat_inputCode, ← h, inputDecode_inputCode]
  simp

/-- **Computable predicates are decidable by single-tape machines.** -/
theorem SingleTapeDecidable.of_computablePred {p : α → Prop} (hp : ComputablePred p) :
    SingleTapeDecidable p := by
  classical
  obtain ⟨f, hf, rfl⟩ := ComputablePred.computable_iff.mp hp
  let F : ℕ → ℕ := fun m ↦ ((decode (α := α) (inputDecode m)).map fun a ↦ cond (f a) 1 0).getD 0
  have hF : Computable F :=
    Computable.option_getD (Computable.option_map (Computable.decode.comp computable_inputDecode)
      ((Computable.cond (hf.comp Computable.snd) (Computable.const 1)
        (Computable.const 0)).to₂)) (Computable.const 0)
  obtain ⟨c, hc⟩ := ToPartrec.Code.exists_code (Nat.Partrec'.part_iff₁.mpr hF.partrec)
  have hc' : ∀ n, c.eval [n] = pure [F n] := fun n ↦ by
    have := hc ⟨[n], rfl⟩
    simp only [Part.map_eq_map] at this
    exact this
  let T := tm2ComputableOfCode c hc'
  have hfin : ∀ k, Fintype ((fwdTM c).Γ k) := fun k ↦ by
    rcases k with k | k
    · exact inferInstanceAs (Fintype Turing.PartrecToTM2.Γ')
    · exact inferInstanceAs (Fintype Bool)
  refine ⟨_, inferInstance, inferInstance, inCell (fwdTM c) T.inputAlphabet,
    inCell_injective _ _, deciderTM (fwdTM c) T.inputAlphabet T.outputAlphabet, fun a ↦ ?_⟩
  let w := encodeNat (encode a)
  have hFa : F (inputCode w) = cond (f a) 1 0 := by simp [F, w, inputDecode_inputCode, encodek]
  obtain ⟨steps, hsteps⟩ := T.outputsFun (inputCode w)
  have hmem : haltList (fwdTM c) ((encodeNat (F (inputCode w))).map T.outputAlphabet.invFun) ∈
      StateTransition.eval (fwdTM c).step
        (initList (fwdTM c) ((w.reverse ++ [true]).map T.inputAlphabet.symm)) := by
    refine StateTransition.mem_eval.mpr ⟨?_, rfl⟩
    rw [← encodeNat_inputCode]
    exact reaches_of_iterate_eq_some hsteps
  have e0 : encodeNat 0 = [] := rfl
  have e1 : encodeNat 1 = [true] := rfl
  have hout : ((encodeNat (F (inputCode w))).map T.outputAlphabet.invFun).length ≤ 1 := by
    rw [hFa]
    cases f a <;> simp [e0, e1]
  obtain ⟨b, hb, hbiff⟩ := deciderTM_outputs (fwdTM c) T.inputAlphabet T.outputAlphabet hout hmem
  refine ⟨b, hb, hbiff.trans ?_⟩
  rw [hFa]
  cases h : f a
  · simp only [Bool.cond_false, e0, h, Bool.false_eq_true, iff_false]
    exact fun h ↦ nomatch h
  · simp only [Bool.cond_true, e1, h, iff_true]
    rfl

end Cslib.Decidability
