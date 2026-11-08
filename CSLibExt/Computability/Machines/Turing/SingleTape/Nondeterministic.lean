/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Cslib.Computability.Machines.Turing.SingleTape.NonDeterministic
public import CSLibExt.Computability.Machines.Turing.SingleTape.Bridge
public import MathlibExt.Computability.RE
public import Mathlib.Basic.Finite.Sum

/-!
# Nondeterministic single-tape machines recognize only r.e. predicates

CSLib's nondeterministic single-tape machine (`SingleTapeNTM State Symbol`) is a
nondeterministic automaton over the transition labels `TrLabel Symbol` (read a symbol, write a
symbol, move, skip), and accepts `xs` when a run from a start state on the tape `BiTape.mk₁ xs`
reaches an accepting state. By `SingleTapeNTM.mYields_mTr`, a run is a label list `μs` along
which the automaton reaches an accepting state and which applies to the tape without a failed
read. For finite state and tape alphabets both conditions are computable in `(xs, μs)`: the
tape by coding it as lists (as in `ToRecursive`), the states by iterating the image of the set
of start states. Searching over `μs` shows that acceptance is r.e. (Sipser, Theorem 3.16,
through recursion theory rather than a breadth-first simulation), and the bridge
`singleTapeRecognizable_iff_rePred` gives a deterministic single-tape recognizer.

**A defect of the pinned definition.** `TrLabel.read` takes a `Symbol`, never the blank, so a
machine cannot test whether a cell is blank. A run on `xs` therefore never reads a blank cell,
and every cell it reads holds the same symbol on the input `xs ++ ys`: the same run accepts
`xs ++ ys` (`SingleTapeNTM.accepts_append`). In particular a machine that accepts the empty
word accepts every word, so no such machine accepts exactly the binary code `encodeNat 0 = []`
of `0`. The predicate `n = 0` is decidable by a deterministic machine, so pinned NTMs cannot
simulate deterministic machines, and the NTM half of Sipser's Corollary 3.18 (a language is
Turing-recognizable iff some NTM recognizes it) fails on this definition
(`exists_singleTapeDecidable_not_singleTapeNTMRecognizable`). The upstream PR
leanprover/cslib#1039 changes `TrLabel.read` and `TrLabel.write` to take an `Option Symbol`, so
that machines can read and write blank cells.

## Main definitions

- `Cslib.Decidability.SingleTapeNTMRecognizable`: recognizability by a single-tape NTM, with the
  input convention of `SingleTapeRecognizable`.

## Main results

- `SingleTapeNTM.accepts_iff_exists_labels`: acceptance as a label list that applies to the input
  tape and leads from a start state to an accepting state.
- `SingleTapeNTM.rePred_accepts`: for finite state and tape alphabets, acceptance is r.e.
- `Cslib.Decidability.singleTapeRecognizable_accepts`,
  `Cslib.Decidability.singleTapeRecognizable_accepts_comp`,
  `Cslib.Decidability.SingleTapeNTMRecognizable.singleTapeRecognizable`: deterministic
  single-tape machines recognize what NTMs accept (Sipser, Theorem 3.16).
- `SingleTapeNTM.accepts_append`, `SingleTapeNTM.accepts_of_accepts_nil`: acceptance is closed
  under extension on the right.
- `SingleTapeNTM.not_forall_accepts_encodeNat_iff_eq_zero`,
  `Cslib.Decidability.not_singleTapeNTMRecognizable_eq_zero`,
  `Cslib.Decidability.exists_singleTapeDecidable_not_singleTapeNTMRecognizable`: pinned NTMs
  cannot simulate deterministic machines (the NTM half of Sipser's Corollary 3.18 fails).

## References

* M. Sipser, *Introduction to the Theory of Computation*, 3rd ed., Cengage, 2013, Theorem 3.16
  and Corollary 3.18.
* leanprover/cslib#1039, "fix(SingleTapeTM): allow reading and writing blank cells" (changes
  `TrLabel.read` and `TrLabel.write` to take an `Option Symbol`).
-/

@[expose] public section

set_option autoImplicit false

open Computability Cslib.Turing Cslib.Automata

namespace Cslib.Computability.Turing.SingleTape

namespace TrLabel

/-! ### Labels on coded tapes -/

section Coded

variable {Symbol : Type}

/-- A tape coded as the symbol under the head and the underlying lists of the tapes to the left
and to the right of the head. -/
private abbrev CodedTape (Symbol : Type) : Type :=
  Option Symbol × List (Option Symbol) × List (Option Symbol)

/-- The code of a tape. -/
private def codeTape (t : BiTape Symbol) : CodedTape Symbol :=
  (t.head, t.left.toList, t.right.toList)

/-- `TrLabel.applyToTape` on coded tapes. -/
private def codedApply [DecidableEq Symbol] :
    Option (CodedTape Symbol) → TrLabel Symbol → Option (CodedTape Symbol)
  | some (h, L, R), read x => if some x = h then some (h, L, R) else none
  | some (_, L, R), write x => some (some x, L, R)
  | some (h, L, R), move .left => some (L.headI, L.tail, SingleTapeTM.codedCons h R)
  | some (h, L, R), move .right => some (R.headI, SingleTapeTM.codedCons h L, R.tail)
  | some c, skip => some c
  | none, _ => none

/-- Applying a label commutes with coding. -/
private theorem codedApply_map [DecidableEq Symbol] (o : Option (BiTape Symbol))
    (μ : TrLabel Symbol) : codedApply (o.map codeTape) μ = (applyToTape o μ).map codeTape := by
  rcases o with _ | t
  · cases μ <;> rfl
  · rcases μ with x | x | (_ | _) | _
    · by_cases hx : some x = t.head <;>
        simp [codedApply, applyToTape, codeTape, hx]
    all_goals simp [codedApply, applyToTape, codeTape, BiTape.write, BiTape.move,
      BiTape.moveLeft, BiTape.moveRight, StackTape.head_eq_headI, StackTape.toList_tail,
      StackTape.toList_cons]

/-- Applying a list of labels commutes with coding. -/
private theorem foldl_codedApply [DecidableEq Symbol] (μs : List (TrLabel Symbol))
    (o : Option (BiTape Symbol)) :
    μs.foldl codedApply (o.map codeTape) = (μs.foldl applyToTape o).map codeTape := by
  induction μs generalizing o with
  | nil => rfl
  | cons μ μs ih => simp only [List.foldl_cons, codedApply_map, ih]

/-- `codedApply` is primitive recursive. -/
private theorem primrec_codedApply [DecidableEq Symbol] [Primcodable Symbol] [Finite Symbol]
    [Primcodable (TrLabel Symbol)] [Finite (TrLabel Symbol)] :
    Primrec₂ (codedApply (Symbol := Symbol)) := by
  have hg : Primrec₂ fun (hμ : Option Symbol × TrLabel Symbol)
      (LR : List (Option Symbol) × List (Option Symbol)) ↦ codedApply (some (hμ.1, LR)) hμ.2 := by
    refine MetaMathlibExt.TM2Recursive.primrec₂_of_finite_left fun ⟨h, μ⟩ ↦ ?_
    rcases μ with x | x | (_ | _) | _
    · by_cases hx : some x = h
      · exact (Primrec.option_some.comp (Primrec.pair (Primrec.const h) Primrec.id)).of_eq
          fun _ ↦ by simp [codedApply, hx]
      · exact (Primrec.const none).of_eq fun _ ↦ by simp [codedApply, hx]
    · exact (Primrec.option_some.comp (Primrec.pair (Primrec.const (some x))
        Primrec.id)).of_eq fun _ ↦ rfl
    · exact (Primrec.option_some.comp (Primrec.pair (Primrec.list_headI.comp Primrec.fst)
        (Primrec.pair (Primrec.list_tail.comp Primrec.fst)
          ((SingleTapeTM.primrec_codedCons h).comp Primrec.snd)))).of_eq fun _ ↦ rfl
    · exact (Primrec.option_some.comp (Primrec.pair (Primrec.list_headI.comp Primrec.snd)
        (Primrec.pair ((SingleTapeTM.primrec_codedCons h).comp Primrec.fst)
          (Primrec.list_tail.comp Primrec.snd)))).of_eq fun _ ↦ rfl
    · exact (Primrec.option_some.comp (Primrec.pair (Primrec.const h) Primrec.id)).of_eq
        fun _ ↦ rfl
  refine (Primrec.option_bind Primrec.fst (hg.comp (Primrec.pair
    (Primrec.fst.comp Primrec.snd) (Primrec.snd.comp Primrec.fst))
      (Primrec.snd.comp Primrec.snd)).to₂).of_eq fun ⟨o, μ⟩ ↦ ?_
  rcases o with _ | ⟨h, L, R⟩
  · cases μ <;> rfl
  · rfl

/-- The labels as a sum: read, write, a direction to move in, skip. -/
private def ofSum : Symbol ⊕ Symbol ⊕ Bool ⊕ Unit → TrLabel Symbol
  | .inl x => read x
  | .inr (.inl x) => write x
  | .inr (.inr (.inl false)) => move .left
  | .inr (.inr (.inl true)) => move .right
  | .inr (.inr (.inr ())) => skip

/-- Every label is a value of `ofSum`. -/
private theorem ofSum_surjective : Function.Surjective (ofSum (Symbol := Symbol)) := by
  rintro (x | x | (_ | _) | _)
  exacts [⟨.inl x, rfl⟩, ⟨.inr (.inl x), rfl⟩, ⟨.inr (.inr (.inl false)), rfl⟩,
    ⟨.inr (.inr (.inl true)), rfl⟩, ⟨.inr (.inr (.inr ())), rfl⟩]

end Coded

/-! ### Labels on extended tapes -/

section Extends

variable {Symbol : Type*}

/-- `s'` extends `s`: every non-blank cell of `s` holds the same symbol in `s'`. -/
private def StackExtends (s s' : StackTape Symbol) : Prop :=
  ∀ n a, (StackTape.tail^[n] s).head = some a → (StackTape.tail^[n] s').head = some a

/-- The heads of extending stacks. -/
private theorem StackExtends.head {s s' : StackTape Symbol} (h : StackExtends s s') {a : Symbol}
    (ha : s.head = some a) : s'.head = some a :=
  h 0 a ha

/-- The tails of extending stacks extend each other. -/
private theorem StackExtends.tail {s s' : StackTape Symbol} (h : StackExtends s s') :
    StackExtends s.tail s'.tail := fun n a ha ↦ by
  simpa only [Function.iterate_succ_apply] using h (n + 1) a (by
    simpa only [Function.iterate_succ_apply] using ha)

/-- Pushing cells onto extending stacks. -/
private theorem StackExtends.cons {x x' : Option Symbol} (hx : ∀ a, x = some a → x' = some a)
    {s s' : StackTape Symbol} (h : StackExtends s s') :
    StackExtends (StackTape.cons x s) (StackTape.cons x' s') := by
  rintro (_ | n) a ha
  · simpa using hx a (by simpa using ha)
  · simpa only [Function.iterate_succ_apply, StackTape.tail_cons] using h n a (by
      simpa only [Function.iterate_succ_apply, StackTape.tail_cons] using ha)

/-- Every stack extends the blank stack. -/
private theorem stackExtends_nil (s : StackTape Symbol) : StackExtends StackTape.nil s := by
  intro n a ha
  rw [Function.iterate_fixed (rfl : StackTape.tail (StackTape.nil : StackTape Symbol) = _)]
    at ha
  exact absurd ha (by simp [StackTape.head, StackTape.nil])

/-- A word laid out on a stack is extended by its extensions on the right. -/
private theorem stackExtends_mapSome_append (l l' : List Symbol) :
    StackExtends (StackTape.mapSome l) (StackTape.mapSome (l ++ l')) := by
  induction l with
  | nil => exact stackExtends_nil _
  | cons b l ih =>
    rintro (_ | n) a ha
    · exact ha
    · exact ih n a ha

/-- `t'` extends `t`: every non-blank cell of `t` holds the same symbol in `t'`. -/
private def TapeExtends (t t' : BiTape Symbol) : Prop :=
  (∀ a, t.head = some a → t'.head = some a) ∧ StackExtends t.left t'.left ∧
    StackExtends t.right t'.right

/-- A label that applies to a tape applies to every extension, and the results extend each
other: `read` never succeeds on a blank cell. -/
private theorem applyToTape_extends [DecidableEq Symbol] {t t' u : BiTape Symbol}
    (h : TapeExtends t t') {μ : TrLabel Symbol} (hu : applyToTape (some t) μ = some u) :
    ∃ u', applyToTape (some t') μ = some u' ∧ TapeExtends u u' := by
  obtain ⟨hh, hl, hr⟩ := h
  rcases μ with x | x | (_ | _) | _
  · by_cases hx : some x = t.head
    · simp only [applyToTape, hx, ↓reduceIte, Option.some.injEq] at hu
      subst hu
      exact ⟨t', by simp [applyToTape, hh x hx.symm], hh, hl, hr⟩
    · simp [applyToTape, hx] at hu
  · simp only [applyToTape, Option.some.injEq] at hu
    subst hu
    exact ⟨_, rfl, fun _ ↦ id, hl, hr⟩
  · simp only [applyToTape, Option.some.injEq] at hu
    subst hu
    exact ⟨_, rfl, fun _ ↦ hl.head, hl.tail, hr.cons hh⟩
  · simp only [applyToTape, Option.some.injEq] at hu
    subst hu
    exact ⟨_, rfl, fun _ ↦ hr.head, hl.cons hh, hr.tail⟩
  · simp only [applyToTape, Option.some.injEq] at hu
    subst hu
    exact ⟨t', rfl, hh, hl, hr⟩

/-- A label list that applies to a tape applies to every extension. -/
private theorem foldl_applyToTape_extends [DecidableEq Symbol] (μs : List (TrLabel Symbol))
    {t t' u : BiTape Symbol} (h : TapeExtends t t') (hu : μs.foldl applyToTape (some t) = some u) :
    ∃ u', μs.foldl applyToTape (some t') = some u' ∧ TapeExtends u u' := by
  induction μs generalizing t t' with
  | nil => exact ⟨t', rfl, Option.some.inj hu ▸ h⟩
  | cons μ μs ih =>
    rw [List.foldl_cons] at hu ⊢
    have hs : (applyToTape (some t) μ).isSome :=
      applyToTape_foldl_isSome (μs := μs) (by rw [hu]; rfl)
    obtain ⟨v, hv⟩ := Option.isSome_iff_exists.mp hs
    obtain ⟨v', hv', hvv⟩ := applyToTape_extends h hv
    rw [hv] at hu
    rw [hv']
    exact ih hvv hu

/-- The input tape of a word is extended by the input tape of its extensions on the right. -/
private theorem tapeExtends_mk₁_append (xs ys : List Symbol) :
    TapeExtends (BiTape.mk₁ xs) (BiTape.mk₁ (xs ++ ys)) := by
  cases xs with
  | nil => exact ⟨by simp [BiTape.mk₁, BiTape.nil], stackExtends_nil _, stackExtends_nil _⟩
  | cons x xs =>
    exact ⟨fun _ ↦ id, stackExtends_nil _, stackExtends_mapSome_append xs ys⟩

end Extends

end TrLabel

namespace SingleTapeNTM

open TrLabel

section Accepts

variable {State Symbol : Type*} [DecidableEq Symbol] (m : SingleTapeNTM State Symbol)

/-- **Acceptance as a label list**: `m` accepts `xs` iff some list of labels applies to the
input tape `BiTape.mk₁ xs` (no read fails) and leads the automaton from a start state to an
accepting state. -/
theorem accepts_iff_exists_labels {xs : List Symbol} :
    Acceptor.Accepts m xs ↔ ∃ μs : List (TrLabel Symbol),
      (μs.foldl applyToTape (some (BiTape.mk₁ xs))).isSome ∧
        ∃ s ∈ m.start, ∃ s' ∈ m.accept, m.MTr s μs s' := by
  constructor
  · rintro ⟨s, hs, c', hc', hy⟩
    obtain ⟨μs, hmtr, htape⟩ := mYields_mTr.mp hy
    exact ⟨μs, by rw [show BiTape.mk₁ xs = (Cfg.mk₁ s xs).tape from rfl, htape]; rfl,
      s, hs, c'.state, hc', hmtr⟩
  · rintro ⟨μs, hsome, s, hs, s', hs', hmtr⟩
    obtain ⟨t, ht⟩ := Option.isSome_iff_exists.mp hsome
    exact ⟨s, hs, ⟨s', t⟩, hs', mYields_mTr.mpr ⟨μs, hmtr, ht⟩⟩

/-- **Acceptance is closed under extension on the right** (a defect of the pinned definition):
`TrLabel.read` cannot read a blank cell, so every cell that an accepting run on `xs` reads holds a
symbol of `xs` or one the run wrote, and the same run accepts `xs ++ ys`. Fixed upstream by
leanprover/cslib#1039. -/
theorem accepts_append {xs : List Symbol} (ys : List Symbol) (h : Acceptor.Accepts m xs) :
    Acceptor.Accepts m (xs ++ ys) := by
  obtain ⟨μs, hsome, hst⟩ := (accepts_iff_exists_labels m).mp h
  obtain ⟨u, hu⟩ := Option.isSome_iff_exists.mp hsome
  obtain ⟨u', hu', -⟩ := foldl_applyToTape_extends μs (tapeExtends_mk₁_append xs ys) hu
  exact (accepts_iff_exists_labels m).mpr ⟨μs, by rw [hu']; rfl, hst⟩

/-- A machine that accepts the empty word accepts every word (a defect of the pinned definition,
see `accepts_append`). -/
theorem accepts_of_accepts_nil (xs : List Symbol) (h : Acceptor.Accepts m []) :
    Acceptor.Accepts m xs :=
  m.accepts_append xs h

/-- **No NTM accepts exactly the binary code of `0`**, on any copy `ι` of the input bits: the
code `encodeNat 0` is the empty word, and a machine that accepts it accepts the code of `1`
(`accepts_of_accepts_nil`). -/
theorem not_forall_accepts_encodeNat_iff_eq_zero (ι : Bool → Symbol) :
    ¬∀ n : ℕ, Acceptor.Accepts m ((encodeNat n).map ι) ↔ n = 0 := fun h ↦
  one_ne_zero ((h 1).mp (m.accepts_of_accepts_nil _ ((h 0).mpr rfl)))

end Accepts

section Recursive

variable {State : Type*} {Symbol : Type} [DecidableEq Symbol] (m : SingleTapeNTM State Symbol)

/-- **Acceptance by an NTM with finite state and tape alphabets is r.e.** in the input word
(Sipser, Theorem 3.16, through recursion theory): search for a label list that applies to the
input tape, checked on coded tapes, and along which the image of the start states, a finite set,
meets the accepting states. -/
theorem rePred_accepts [Finite State] [Finite Symbol] [Primcodable Symbol] :
    REPred fun xs : List Symbol ↦ Acceptor.Accepts m xs := by
  classical
  have : Finite (TrLabel Symbol) := Finite.of_surjective _ ofSum_surjective
  let _ := Fintype.ofFinite (TrLabel Symbol)
  let _ := Fintype.ofFinite (Set State)
  let _ : Primcodable (TrLabel Symbol) := Primcodable.ofEquiv _ (Fintype.equivFin _)
  let _ : Primcodable (Set State) := Primcodable.ofEquiv _ (Fintype.equivFin _)
  have hinit : Primrec fun xs : List Symbol ↦ some (codeTape (BiTape.mk₁ xs)) :=
    Primrec.option_some.comp ((Primrec.pair Primrec.list_head? (Primrec.pair (Primrec.const [])
      (Primrec.list_map Primrec.list_tail (Primrec.option_some.comp Primrec.snd).to₂))).of_eq
        fun xs ↦ by cases xs <;> rfl)
  have htape : Primrec fun p : List Symbol × List (TrLabel Symbol) ↦
      (p.2.foldl codedApply (some (codeTape (BiTape.mk₁ p.1)))).isSome :=
    Primrec.option_isSome.comp (Primrec.list_foldl Primrec.snd (hinit.comp Primrec.fst)
      (primrec_codedApply.comp (Primrec.fst.comp Primrec.snd)
        (Primrec.snd.comp Primrec.snd)).to₂)
  have hstate : Primrec fun p : List Symbol × List (TrLabel Symbol) ↦
      decide (∃ s' ∈ m.accept, s' ∈ p.2.foldl m.setImage m.start) :=
    (Primrec.dom_finite fun S : Set State ↦ decide (∃ s' ∈ m.accept, s' ∈ S)).comp
      (Primrec.list_foldl Primrec.snd (Primrec.const m.start)
        ((Primrec.dom_finite fun q : Set State × TrLabel Symbol ↦ m.setImage q.1 q.2).comp
          Primrec.snd).to₂)
  have hR : ComputablePred fun p : List Symbol × List (TrLabel Symbol) ↦
      (p.2.foldl applyToTape (some (BiTape.mk₁ p.1))).isSome ∧
        ∃ s ∈ m.start, ∃ s' ∈ m.accept, m.MTr s p.2 s' := by
    refine ComputablePred.computable_iff.mpr ⟨_, (Primrec.and.comp htape hstate).to_comp, ?_⟩
    funext p
    rw [show some (codeTape (BiTape.mk₁ p.1)) = (some (BiTape.mk₁ p.1)).map codeTape from rfl,
      foldl_codedApply, Option.isSome_map]
    simp only [Bool.and_eq_true, decide_eq_true_eq, LTS.mem_foldl_setImage]
    exact propext ⟨fun ⟨h₁, s, hs, s', hs', h⟩ ↦ ⟨h₁, s', hs', s, hs, h⟩,
      fun ⟨h₁, s', hs', s, hs, h⟩ ↦ ⟨h₁, s, hs, s', hs', h⟩⟩
  exact (MetaMathlibExt.REPred.exists hR.to_re).of_eq fun xs ↦
    (accepts_iff_exists_labels m).symm

end Recursive

end SingleTapeNTM

end Cslib.Computability.Turing.SingleTape

namespace Cslib.Decidability

open Encodable Cslib.Computability.Turing.SingleTape

section Recognizable

variable {State : Type*} {Symbol : Type} [DecidableEq Symbol] [Finite State] [Finite Symbol]
  [Primcodable Symbol] (m : SingleTapeNTM State Symbol)

/-- **A deterministic single-tape machine recognizes what an NTM accepts** (Sipser,
Theorem 3.16), for finite state and tape alphabets, on input words. -/
theorem singleTapeRecognizable_accepts :
    SingleTapeRecognizable fun xs : List Symbol ↦ Acceptor.Accepts m xs :=
  singleTapeRecognizable_iff_rePred.mpr m.rePred_accepts

/-- **A deterministic single-tape machine recognizes what an NTM accepts** (Sipser,
Theorem 3.16), on the image of any computable input map. -/
theorem singleTapeRecognizable_accepts_comp {α : Type*} [Primcodable α] {f : α → List Symbol}
    (hf : Computable f) : SingleTapeRecognizable fun a ↦ Acceptor.Accepts m (f a) :=
  singleTapeRecognizable_iff_rePred.mpr (Partrec.comp m.rePred_accepts hf)

end Recognizable

variable {α : Type*} [Primcodable α] {p : α → Prop}

/-- `p` is **recognizable by a single-tape nondeterministic machine** (CSLib's `SingleTapeNTM`),
with the input convention of `SingleTapeRecognizable`: for finite state and tape alphabets and an
injective copy `ι` of the input bits, some NTM accepts the input word
`(encodeNat (encode a)).map ι` exactly when `p a`.

On the pinned CSLib definition a machine cannot read a blank cell, so acceptance is closed under
extension on the right (`SingleTapeNTM.accepts_append`) and this class is strictly smaller than
`SingleTapeRecognizable` (`exists_singleTapeDecidable_not_singleTapeNTMRecognizable`); the
upstream PR leanprover/cslib#1039 lets machines read and write blank cells. -/
def SingleTapeNTMRecognizable (p : α → Prop) : Prop :=
  ∃ (State Symbol : Type) (_ : Fintype State) (_ : Fintype Symbol) (_ : DecidableEq Symbol)
    (ι : Bool → Symbol), Function.Injective ι ∧ ∃ m : SingleTapeNTM State Symbol,
      ∀ a, Acceptor.Accepts m ((encodeNat (encode a)).map ι) ↔ p a

/-- **A predicate recognized by a single-tape NTM is recognized by a deterministic single-tape
machine** (Sipser, Theorem 3.16, through recursion theory). -/
theorem SingleTapeNTMRecognizable.singleTapeRecognizable (h : SingleTapeNTMRecognizable p) :
    SingleTapeRecognizable p := by
  obtain ⟨State, Symbol, _, _, _, ι, -, m, hm⟩ := h
  let _ : Primcodable Symbol := Primcodable.ofEquiv _ (Fintype.equivFin _)
  have hin : Computable fun a : α ↦ (encodeNat (encode a)).map ι :=
    ((SingleTapeTM.primrec_map_encodeNat ι).comp Primrec.encode).to_comp
  have : REPred fun a : α ↦ Acceptor.Accepts m ((encodeNat (encode a)).map ι) :=
    Partrec.comp m.rePred_accepts hin
  exact singleTapeRecognizable_iff_rePred.mpr (this.of_eq hm)

/-- **No single-tape NTM recognizes `n = 0`** on the pinned definition: the code of `0` is the
empty word, and an NTM that accepts the empty word accepts every word
(`SingleTapeNTM.not_forall_accepts_encodeNat_iff_eq_zero`). -/
theorem not_singleTapeNTMRecognizable_eq_zero :
    ¬SingleTapeNTMRecognizable fun n : ℕ ↦ n = 0 := by
  rintro ⟨State, Symbol, _, _, _, ι, -, m, hm⟩
  exact m.not_forall_accepts_encodeNat_iff_eq_zero ι hm

/-- **Pinned NTMs cannot simulate deterministic machines**: `n = 0` is decidable by a
deterministic single-tape machine but recognized by no single-tape NTM, so the NTM half of
Sipser's Corollary 3.18 fails on the pinned definition. Fixed upstream by
leanprover/cslib#1039. -/
theorem exists_singleTapeDecidable_not_singleTapeNTMRecognizable :
    ∃ p : ℕ → Prop, SingleTapeDecidable p ∧ ¬SingleTapeNTMRecognizable p := by
  refine ⟨fun n ↦ n = 0, singleTapeDecidable_iff_computablePred.mpr
    (ComputablePred.computable_iff.mpr ⟨fun n ↦ n == 0, ?_, ?_⟩),
      not_singleTapeNTMRecognizable_eq_zero⟩
  · exact (Primrec.beq.comp Primrec.id (Primrec.const 0)).to_comp
  · funext n
    simp

end Cslib.Decidability
