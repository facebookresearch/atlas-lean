/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.Computability.Languages.Congruences.NerodeUpstream

/-!
# Tests for upstream Myhill-Nerode bridges

The two-state empty-word recognizer exercises the minimality and uniqueness bridges with
distinct Nerode classes. A one-state recognizer exercises the empty-alphabet boundary; an
unreachable duplicate state fails minimality. The existing local quotient and automaton
conversions still support arbitrary alphabet universes.
-/

@[expose] public section

open scoped Computability

namespace Cslib.Language.NerodeUpstreamTests

open Cslib.Automata.DA.FinAcc

/-- The language containing only the empty Boolean word. -/
def emptyOnly : Language Bool := {[]}

/-- A two-state recognizer for `emptyOnly`: it stays in `true` until it reads a letter. -/
def emptyOnlyDFA : DFA Bool Bool where
  step _ _ := false
  start := true
  accept := {true}

@[simp]
theorem emptyOnlyDFA_eval_nil : emptyOnlyDFA.eval [] = true :=
  rfl

@[simp]
theorem emptyOnlyDFA_eval_cons (a : Bool) (w : List Bool) :
    emptyOnlyDFA.eval (a :: w) = false := by
  obtain ⟨v, b, hv⟩ := (List.eq_nil_or_concat (a :: w)).resolve_left (List.cons_ne_nil a w)
  rw [hv, List.concat_eq_append, DFA.eval_append_singleton]
  rfl

@[simp]
theorem emptyOnlyDFA_accepts : emptyOnlyDFA.accepts = emptyOnly := by
  ext w
  cases w with
  | nil => simp [DFA.mem_accepts, emptyOnly, emptyOnlyDFA]
  | cons a w =>
    rw [DFA.mem_accepts, emptyOnlyDFA_eval_cons]
    simp [emptyOnly, emptyOnlyDFA]

/-- A recognizer of every word whose two states behave identically. -/
def redundantUniversalDFA : DFA Bool Bool where
  step q _ := q
  start := false
  accept := Set.univ

example (L : Language Bool) (x : List Bool) :
    nerodeClassEquivNerodeQuotient L (nerodeClass L x) = Quotient.mk _ x :=
  nerodeClassEquivNerodeQuotient_mk L x

example (L : Language Bool) (x : List Bool) :
    (nerodeClassEquivNerodeQuotient L).symm (Quotient.mk _ x) = nerodeClass L x := by
  simp

example (L : Language Bool) : L.IsRegular ↔ Finite (NerodeClass L) := by
  rw [_root_.Language.IsRegular.iff_finite_nerodeQuotient]
  constructor
  · intro h
    let := h
    exact Finite.of_equiv L.NerodeQuotient (nerodeClassEquivNerodeQuotient L).symm
  · intro h
    let := h
    exact Finite.of_equiv (NerodeClass L) (nerodeClassEquivNerodeQuotient L)

example : Nat.card (NerodeClass emptyOnly) ≤ Nat.card Bool := by
  have h := _root_.Language.dfa_num_state_min (M := ofDFA emptyOnlyDFA)
  rw [accepts_ofDFA, emptyOnlyDFA_accepts] at h
  rw [Nat.card_congr (nerodeClassEquivNerodeQuotient emptyOnly)]
  exact h

example : Nat.card (Set.range emptyOnly.leftQuotient) ≤ Nat.card Bool := by
  have h := _root_.Language.dfa_num_state_min (M := ofDFA emptyOnlyDFA)
  rw [accepts_ofDFA, emptyOnlyDFA_accepts] at h
  rw [← Nat.card_congr (nerodeQuotientEquivResidual emptyOnly)]
  exact h

/-- Both states of the empty-word recognizer are reached, by an empty or a one-letter word. -/
theorem emptyOnly_accessible : Accessible emptyOnlyDFA := by
  intro q
  cases q with
  | false => exact ⟨[true], emptyOnlyDFA_eval_cons true []⟩
  | true => exact ⟨[], emptyOnlyDFA_eval_nil⟩

/-- The empty continuation distinguishes the two states of the empty-word recognizer. -/
theorem emptyOnly_separated : StateSeparated emptyOnlyDFA := by
  intro p q h
  have hnil := (stateEquivalent_iff.mp h) []
  change (p = true ↔ q = true) at hnil
  cases p <;> cases q <;> simp_all

example : (ofDFA emptyOnlyDFA).IsMinimalAutomaton emptyOnly := by
  have h := isMinimalAutomaton_ofDFA_of_accessible_separated emptyOnlyDFA
    emptyOnly_accessible emptyOnly_separated
  simpa only [emptyOnlyDFA_accepts] using h

example : Function.Surjective (NerodeClass.toDFAState (L := emptyOnly) emptyOnlyDFA) := by
  apply (isMinimalAutomaton_ofDFA_iff emptyOnlyDFA emptyOnlyDFA_accepts).mp
  have h := isMinimalAutomaton_ofDFA_of_accessible_separated emptyOnlyDFA
    emptyOnly_accessible emptyOnly_separated
  simpa only [emptyOnlyDFA_accepts] using h

example : ∃! e : Bool ≃ NerodeClass emptyOnlyDFA.accepts,
    ∀ w, e (emptyOnlyDFA.eval w) = nerodeClass emptyOnlyDFA.accepts w :=
  unique_minimal_ofDFA emptyOnlyDFA
    (isMinimalAutomaton_ofDFA_of_accessible_separated emptyOnlyDFA
      emptyOnly_accessible emptyOnly_separated)

example (e : Bool ≃ emptyOnlyDFA.accepts.NerodeQuotient)
    (he : ∀ w, e (emptyOnlyDFA.eval w) = Quotient.mk _ w) :
    (stateEquivResidualsOfSeparated emptyOnlyDFA emptyOnly_accessible emptyOnly_separated).trans
      (nerodeQuotientEquivResidual emptyOnlyDFA.accepts).symm = e :=
  stateEquivResidualsOfSeparated_eq_minimal_equiv emptyOnlyDFA
    emptyOnly_accessible emptyOnly_separated e he

example : ∃ e : Bool ≃ emptyOnlyDFA.accepts.NerodeQuotient,
    (stateEquivResidualsOfSeparated emptyOnlyDFA emptyOnly_accessible emptyOnly_separated).trans
      (nerodeQuotientEquivResidual emptyOnlyDFA.accepts).symm = e ∧
    e true = Quotient.mk _ ([] : List Bool) ∧ e false = Quotient.mk _ [true] := by
  have hr : emptyOnlyDFA.accepts.IsRegular := by
    apply isRegular_iff_finite_nerodeClass.mpr
    exact Finite.of_injective _ (NerodeClass.toDFAState_injective emptyOnlyDFA rfl)
  obtain ⟨e, he, _⟩ := (ofDFA emptyOnlyDFA).unique_minimal emptyOnlyDFA.accepts hr
    (isMinimalAutomaton_ofDFA_of_accessible_separated emptyOnlyDFA
      emptyOnly_accessible emptyOnly_separated)
  have heDFA (w : List Bool) : e (emptyOnlyDFA.eval w) = Quotient.mk _ w := he w
  refine ⟨e, stateEquivResidualsOfSeparated_eq_minimal_equiv emptyOnlyDFA
    emptyOnly_accessible emptyOnly_separated e heDFA, ?_, ?_⟩
  · simpa only [emptyOnlyDFA_eval_nil] using heDFA []
  · simpa only [emptyOnlyDFA_eval_cons] using heDFA [true]

/-- A single accepting state recognizes every word over any alphabet. -/
def universal (Symbol : Type*) : DFA Symbol Unit where
  step _ _ := ()
  start := ()
  accept := Set.univ

/-- The single state is reached by the empty word even when the alphabet is empty. -/
theorem universal_accessible (Symbol : Type*) : Accessible (universal Symbol) := by
  intro q
  cases q
  exact ⟨[], rfl⟩

/-- A singleton state type has no observationally equivalent distinct states. -/
theorem universal_separated (Symbol : Type*) : StateSeparated (universal Symbol) := by
  intro p q _
  exact Subsingleton.elim p q

example : (ofDFA (universal Empty)).IsMinimalAutomaton (universal Empty).accepts :=
  isMinimalAutomaton_ofDFA_of_accessible_separated (universal Empty)
    (universal_accessible Empty) (universal_separated Empty)

example : Nat.card (NerodeClass (universal Empty).accepts) = 1 := by
  have h := isMinimalAutomaton_ofDFA_of_accessible_separated (universal Empty)
    (universal_accessible Empty) (universal_separated Empty)
  rw [Nat.card_congr (nerodeClassEquivNerodeQuotient (universal Empty).accepts)]
  simpa only [Nat.card_eq_fintype_card, Fintype.card_unit] using h.2.symm

example : ∃! e : Unit ≃ NerodeClass (universal Empty).accepts,
    ∀ w, e ((universal Empty).eval w) = nerodeClass (universal Empty).accepts w :=
  unique_minimal_ofDFA (universal Empty)
    (isMinimalAutomaton_ofDFA_of_accessible_separated (universal Empty)
      (universal_accessible Empty) (universal_separated Empty))

example : ¬(ofDFA redundantUniversalDFA).IsMinimalAutomaton redundantUniversalDFA.accepts := by
  intro h
  have hsurj := (isMinimalAutomaton_ofDFA_iff redundantUniversalDFA rfl).mp h
  obtain ⟨q, hq⟩ := hsurj true
  have heval (w : List Bool) : redundantUniversalDFA.eval w = false := by
    change List.foldl (fun s (_ : Bool) ↦ s) false w = false
    induction w with
    | nil => rfl
    | cons a w ih => exact ih
  have hf : NerodeClass.toDFAState (L := redundantUniversalDFA.accepts)
      redundantUniversalDFA q = false := heval _
  have hfalse : false = true := hf.symm.trans hq
  cases hfalse

universe u v

example (Symbol : Type u) : toDFA (ofDFA (universal Symbol)) = universal Symbol :=
  toDFA_ofDFA _

example {State : Type v} (M : DFA Bool State) (hacc : Accessible M) (hsep : StateSeparated M) :
    (ofDFA M).IsMinimalAutomaton M.accepts :=
  isMinimalAutomaton_ofDFA_of_accessible_separated M hacc hsep

example {State : Type v} [Finite State] (M : DFA Bool State)
    (hmin : (ofDFA M).IsMinimalAutomaton M.accepts) :
    ∃! e : State ≃ NerodeClass M.accepts,
      ∀ w, e (M.eval w) = nerodeClass M.accepts w :=
  unique_minimal_ofDFA M hmin

example {State : Type v} (M : DFA Bool State) (hacc : Accessible M) (hsep : StateSeparated M)
    (e : State ≃ M.accepts.NerodeQuotient)
    (he : ∀ w, e (M.eval w) = Quotient.mk _ w) :
    (stateEquivResidualsOfSeparated M hacc hsep).trans
      (nerodeQuotientEquivResidual M.accepts).symm = e :=
  stateEquivResidualsOfSeparated_eq_minimal_equiv M hacc hsep e he

noncomputable section

example {Symbol : Type u} (L : Language Symbol) :
    NerodeClass L ≃ Set.range L.leftQuotient :=
  nerodeClassEquivResidual L

end

end Cslib.Language.NerodeUpstreamTests
