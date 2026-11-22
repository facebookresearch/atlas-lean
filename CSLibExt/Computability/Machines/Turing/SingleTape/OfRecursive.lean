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

/-- **The machine that prepends a symbol.** For a symbol $c$, this is the single-tape machine
with two states that, from its start state, writes back the symbol under the head, moves left and
enters its second state, and from its second state writes $c$ and halts without moving.

On an input word $l$ it outputs $c$ followed by $l$. -/
def consComputer (c : Symbol) : SingleTapeTM Symbol where
  State := Bool
  q₀ := false
  tr q s := match q with
    | false => (⟨s, some .left⟩, some true)
    | true => (⟨some c, none⟩, none)

omit [Inhabited Symbol] [Fintype Symbol] in
/-- **Prepending a symbol by stepping left.** Let $c$ be a symbol and $l$ a list of symbols, and
consider the tape holding $l$ from the head rightwards, all other cells blank. Writing back the
symbol under the head, moving the head one cell left, and then writing $c$ gives the tape holding
the list $c$ followed by $l$ from the head rightwards, all other cells blank. -/
theorem write_moveLeft_mk₁ (c : Symbol) (l : List Symbol) :
    (((BiTape.mk₁ l).write (BiTape.mk₁ l).head).optionMove (some .left)).write (some c) =
      BiTape.mk₁ (c :: l) := by
  cases l <;> rfl

/-- **Prepending a symbol takes at most two steps.** For every symbol $c$ and every word $l$, the
machine that prepends $c$, started on $l$, halts with output the word $c$ followed by $l$ within
at most two steps. -/
theorem consComputer_outputsWithinTime (c : Symbol) (l : List Symbol) :
    (consComputer c).OutputsWithinTime l (c :: l) 2 := by
  refine RelatesWithinSteps.of_relatesInSteps (RelatesInSteps.head _ _ _ _ rfl
    (RelatesInSteps.single ?_))
  simp only [TransitionRelation, step, consComputer, haltCfg, Option.some.injEq]
  congr 1
  exact write_moveLeft_mk₁ c l

/-- **Correctness of the prepending machine.** For every symbol $c$ and every word $l$, the
machine that prepends $c$, started on $l$, halts with output the word $c$ followed by $l$. -/
theorem consComputer_outputs (c : Symbol) (l : List Symbol) :
    (consComputer c).Outputs l (c :: l) :=
  let ⟨_, _, h⟩ := consComputer_outputsWithinTime c l
  h.reflTransGen

end Cslib.Turing.SingleTapeTM

namespace Cslib.Turing.SingleTapeTM.OfTM2

open MetaMathlibExt.TM2Recursive

/-! ### The input stack of the emulation as a number -/

/-- **Input code of a bit word.** For a list of bits $w$, let $b_0, \dots, b_n$ be the reversal of
$w$ followed by $\mathsf{true}$, reading $\mathsf{true}$ as $1$ and $\mathsf{false}$ as $0$. The
input code of $w$ is the natural number $\sum_{i=0}^{n} b_i 2^i$. Its binary expansion, least
significant bit first, is $b_0, \dots, b_n$: the input stack on which the single-tape emulation
starts for the input word $w$. -/
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

/-- **Recovering a word from its input code.** For every list of bits $w$, reversing the binary
encoding (least significant bit first) of the input code of $w$ and then dropping the first bit of
the result gives back $w$. -/
theorem reverse_tail_encodeNat_inputCode (w : List Bool) :
    (encodeNat (inputCode w)).reverse.tail = w := by
  rw [encodeNat_inputCode]
  simp

/-- **Input decoding.** For a natural number $m > 0$, let $b_0, \dots, b_n$ be its binary
expansion, least significant bit first, without trailing zeros. The input decoding of $m$ is
$\sum_{i=0}^{n-1} b_{n-1-i} 2^i$, the value, least significant bit first, of the reversed
expansion with its first bit dropped. The input decoding of $0$, whose expansion is empty, is $0$.

It undoes the encoding of input words: for every natural number $k$ with binary expansion $w$,
least significant bit first, the input decoding of the number whose binary expansion, least
significant bit first, is the reversal of $w$ followed by $1$ is $k$. -/
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

/-- **Input cell of a bit.** Let $M$ be a multi-stack machine with finitely many stacks, labels
and internal states, and let $e$ be a bijection from the alphabet of its input stack to the bits.
The input cell of a bit $b$ is the non-blank cell of the single-tape emulation of $M$ whose
bottom-of-stack flag is off, whose entry for the input stack is $e^{-1}(b)$, and whose entries for
all other stacks are empty. -/
def inCell (b : Bool) : NonBlank (TM2to1.Γ' tm.K tm.Γ) :=
  ⟨(false, Function.update (fun _ ↦ none) tm.k₀ (some (e.symm b))), fun h ↦ by
    have := congrFun (congrArg Prod.snd h) tm.k₀
    simp only [Function.update_self] at this
    cases this⟩

/-- **The bottom cell of the start tape.** Let $M$ be a finite multi-stack machine whose input
stack alphabet is identified with the bits. The bottom cell of the emulation's start tape is the
cell flagged as the stack bottom that holds the symbol for $\mathrm{true}$ on the input stack and
nothing on every other stack. -/
def botCell : NonBlank (TM2to1.Γ' tm.K tm.Γ) :=
  ⟨(true, Function.update (fun _ ↦ none) tm.k₀ (some (e.symm true))),
    fun h ↦ Bool.noConfusion (congrArg Prod.fst h)⟩

omit [∀ k, Fintype (tm.Γ k)] in
theorem inCell_injective : Function.Injective (inCell tm e) := fun b b' h ↦ by
  have := congrFun (congrArg Prod.snd (congrArg Subtype.val h)) tm.k₀
  simpa [inCell] using this

/-- **States of the single-tape emulation.** Let $M$ be a multi-stack machine with finitely many
stacks, labels and internal states and a finite input alphabet. Its plain single-tape emulation
is the translation of $M$ to a single-tape machine with a finite store, followed by the
translation of that machine to a plain single-tape machine, whose states are pairs of a
statement of the intermediate machine, or the halting state, and an internal state. This is the
finite set of those pairs whose first entry is the halting state or a statement occurring in the
program of one of the labels that the first translation produces from the labels of $M$.

The emulation only visits states in this set. -/
noncomputable abbrev emuSupport : Finset (TM1to0.Λ' (TM2to1.tr tm.m)) :=
  TM1to0.trStmts (TM2to1.tr tm.m) (TM2to1.trSupp tm.m Finset.univ)

/-- **Finite single-tape emulation of a multi-stack machine.** Let $M$ be a multi-stack machine
with finitely many stacks, labels and internal states, and with finite stack alphabets. Its
finite single-tape emulation is the single-tape machine that runs the plain single-tape emulation
of $M$ (through a single-tape machine with a finite store) step for step: its states are those in
the finite set of states the emulation visits, and its tape alphabet is the set of non-blank cells
of the emulation, where a cell is a bottom-of-stack flag together with an optional symbol for each
stack. -/
noncomputable def emuTM : SingleTapeTM (NonBlank (TM2to1.Γ' tm.K tm.Γ)) :=
  ofTM0 (TM2ToTM0.tr tm.m) (emuSupport tm)
    (TM2ToTM0.tr_supports tm.m (TM2ToTM0.supports_univ tm.m))

/-- **The recognizer of a multi-stack machine.** Let $M$ be a finite multi-stack machine all of
whose stack alphabets are finite, and let $e$ be an identification of the alphabet of its input
stack with the booleans. The recognizer of $M$ is the single-tape machine, over the non-blank
cells of the multi-stack-to-single-tape translation of $M$, that first runs the machine
prepending the bottom cell determined by $M$ and $e$ (the bottom-flagged cell holding
$e^{-1}(\mathrm{true})$ on the input stack and nothing on the other stacks) to its input and, when
that machine halts, runs the single-tape emulation of $M$. -/
noncomputable def recognizerTM : SingleTapeTM (NonBlank (TM2to1.Γ' tm.K tm.Γ)) :=
  compComputer (consComputer (botCell tm e)) (emuTM tm)

omit [∀ k, Fintype (tm.Γ k)] in
/-- **The bottom cell followed by the input word is the emulation's start tape.** Let $M$ be a
multi-stack machine with finitely many stacks, labels and internal states, and let $e$ be a
bijection from the alphabet of its input stack to the bits. For every list of bits $w$, the bottom
cell followed by the input cells of the bits of $w$, read as cells of the emulation, is the start
tape that the single-tape emulation assigns to the input stack obtained by applying $e^{-1}$ to
each entry of the reversal of $w$ followed by $\mathsf{true}$. -/
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

/-- **The recognizer halts iff the multi-stack machine does.** Let $M$ be a multi-stack machine
with finitely many stacks, labels and internal states and with finite stack alphabets, and let
$e$ be a bijection from the alphabet of its input stack to the bits. For every list of bits $w$,
the recognizer built from $M$ and $e$ halts on the word of input cells of the bits of $w$ if and
only if $M$ halts when started on the input stack obtained by applying $e^{-1}$ to each entry of
the reversal of $w$ followed by $\mathsf{true}$. -/
theorem haltsOn_recognizerTM_iff (w : List Bool) :
    (recognizerTM tm e).HaltsOn (w.map (inCell tm e)) ↔
      TM2HaltsOn tm ((w.reverse ++ [true]).map e.symm) := by
  rw [recognizerTM, haltsOn_compComputer_iff (consComputer_outputs _ _), emuTM,
    haltsOn_ofTM0_iff, map_val_botCell_cons, TM2ToTM0.tr_eval_dom,
    Cslib.Decidability.tm2HaltsOn_iff_eval_dom]

/-! ### The emulation's final tape, and deciders -/

omit [∀ k, Fintype (tm.Γ k)] in
/-- **The emulation's final tape.** Let $M$ be a multi-stack machine with finitely many stacks,
labels and internal states and a finite input alphabet, let $L$ be a list of symbols of its input
stack, and suppose that $M$, started with $L$ on its input stack and every other stack empty,
halts at the configuration $c$. Then its plain single-tape emulation, started on the tape that
holds the symbols of $L$ bottom first on the input stack with the first cell flagged as the
bottom, halts at a configuration $c_0$ for which there is a list $L'$ of columns, each holding an
optional symbol for every stack and padded with blank columns, such that for every stack $k$ the
entries of $L'$ for $k$ are the symbols of stack $k$ of $c$ listed bottom first, followed by
blanks, and the tape of $c_0$ is blank to the left of the head and holds $L'$ from the head
rightwards, with the bottom-of-stack flag set on its first cell and cleared on all others. -/
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
/-- **Stacks of height at most one give a one-cell tape.** Let $M$ be a finite multi-stack
machine, and let $S$ assign to every stack $k$ of $M$ a list $S_k$ of length at most $1$. Let $L'$
be a tape of stack columns whose $k$-th track, for every $k$, is $S_k$ laid out bottom first and
followed by blanks. Then adding the bottom marker to $L'$, as in the translation of $M$ to a
single-tape machine, gives the tape whose first cell is flagged as the bottom and holds the top of
$S_k$ on every stack $k$ (nothing if $S_k$ is empty), followed by blank cells. -/
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
/-- **The answer bit of a cell.** Let $M$ be a finite multi-stack machine whose output stack
alphabet is identified with the bits. The answer read from a non-blank cell of the single-tape
emulation of $M$ is $\mathrm{true}$ exactly when the cell holds the symbol for $\mathrm{true}$ on
the output stack. -/
noncomputable def cellAnswer (x : NonBlank (TM2to1.Γ' tm.K tm.Γ)) : Bool :=
  decide (x.1.2 tm.k₁ = some (e₁.symm true))

/-- **The answer machine.** Let $M$ be a finite multi-stack machine whose stack alphabets are all
finite, with its input and output stack alphabets identified with the bits. The answer machine of
$M$ is the single-tape machine over the non-blank cells of the single-tape emulation of $M$ with a
single state that, in one step, replaces the symbol under the head by the input-bit cell for the
answer read from that cell (the answer $\mathrm{false}$ if the cell is blank), does not move, and
halts. -/
noncomputable def answerTM : SingleTapeTM (NonBlank (TM2to1.Γ' tm.K tm.Γ)) where
  State := Unit
  q₀ := ()
  tr _ s := (⟨some (inCell tm e (s.elim false (cellAnswer tm e₁))), none⟩, none)

/-- **The answer machine outputs the answer of a one-cell input.** Let $M$ be a finite multi-stack
machine whose stack alphabets are all finite, with its input and output stack alphabets
identified with the bits. For every non-blank cell $x$ of the single-tape emulation of $M$, the
answer machine of $M$, started on the one-cell input $x$, halts with the one-cell output holding
the input-bit cell for the answer read from $x$. -/
theorem answerTM_outputs (x : NonBlank (TM2to1.Γ' tm.K tm.Γ)) :
    (answerTM tm e e₁).Outputs [x] [inCell tm e (cellAnswer tm e₁ x)] :=
  ReflTransGen.single rfl

/-- **The decider of a multi-stack machine.** Let $M$ be a finite multi-stack machine whose stack
alphabets are all finite, with its input and output stack alphabets identified with the bits. The
decider of $M$ is the single-tape machine over the non-blank cells of the single-tape emulation of
$M$ that runs the recognizer of $M$ and, once the recognizer halts, runs the answer machine of $M$
on the resulting tape. -/
noncomputable def deciderTM : SingleTapeTM (NonBlank (TM2to1.Γ' tm.K tm.Γ)) :=
  compComputer (recognizerTM tm e) (answerTM tm e e₁)

/-- **The decider outputs the answer bit.** Let $M$ be a finite multi-stack machine whose stack
alphabets are all finite, with its input and output stack alphabets identified with the bits, and
let $w$ be a word of bits. Suppose that $M$, started with the input stack holding the reverse of
$w$ followed by $\mathrm{true}$, halts with the output stack holding a list $u$ of length at most
$1$, every other stack empty and its variable back at its initial value. Then there is a bit $b$
such that the decider of $M$, started on the input-bit cells of $w$, halts with the one-cell
output holding the input-bit cell for $b$, and $b = \mathrm{true}$ exactly when $u$ is nonempty
and its first symbol is the symbol for $\mathrm{true}$. -/
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

/-- **Computable predicates are decidable by single-tape machines.** Let $\alpha$ be a type with a
primitive recursive encoding into $\mathbb{N}$, and let $p$ be a computable predicate on $\alpha$,
that is, one whose indicator function $\alpha \to \{0, 1\}$ is computable. Then $p$ is decidable
by a single-tape Turing machine. -/
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
