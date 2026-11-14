/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.Computability.Languages.KleeneConverse
public import Mathlib.Computability.Language

@[expose] public section

/-!
# Client tests for Kleene's theorem, converse direction

The existing Mathlib-DFA clients retain their API. Canonical CSLib deterministic and
nondeterministic clients obtain a regex with the same accepted language, match a one-letter
word and reject empty and two-letter words. The NFA has two successors from its initial state.
A one-state deterministic automaton over an empty alphabet covers the smallest alphabet case.
-/

set_option autoImplicit false

open Cslib.Language
open scoped Computability

/-- The one-letter-word language over `Bool` is denoted by a regular expression. -/
example : ∃ r : RegularExpression Bool, r.matches' = ({w : List Bool | w.length = 1} : Language Bool) :=
  IsRegular.exists_regex
    ⟨Fin 3, inferInstance, (KleeneConverse.singletonDFA : DFA Bool (Fin 3)),
      KleeneConverse.singletonDFA_accepts⟩

/-- The Kleene iff, applied to the one-letter-word language. -/
example : (KleeneConverse.singletonDFA : DFA Bool (Fin 3)).accepts.IsRegular ↔
    ∃ r : RegularExpression Bool,
      r.matches' = (KleeneConverse.singletonDFA : DFA Bool (Fin 3)).accepts :=
  isRegular_iff_exists_regex

/-- The regular expression for the one-letter-word language matches `[true]` but not
`[]` or `[true, true]`. -/
example : ∃ r : RegularExpression Bool, r.matches' = ({w : List Bool | w.length = 1} : Language Bool) ∧
    [true] ∈ r.matches' ∧ [] ∉ r.matches' ∧ [true, true] ∉ r.matches' := by
  obtain ⟨r, hr⟩ := IsRegular.exists_regex
    ⟨Fin 3, inferInstance, (KleeneConverse.singletonDFA : DFA Bool (Fin 3)),
      KleeneConverse.singletonDFA_accepts⟩
  refine ⟨r, hr, ?_, ?_, ?_⟩
  · rw [hr]
    change (1 : ℕ) = 1
    rfl
  · rw [hr]
    intro h
    change (0 : ℕ) = 1 at h
    exact absurd h (by decide)
  · rw [hr]
    intro h
    change (2 : ℕ) = 1 at h
    exact absurd h (by decide)

namespace CslibTest.Computability.Languages.KleeneConverse

open Cslib.Automata Acceptor

private def oneLetterDA : DA.FinAcc (Fin 3) Bool where
  tr q _ := if q = 0 then 1 else 2
  start := 0
  accept := {1}

private theorem oneLetterDA_language :
    language oneLetterDA = {w : List Bool | w.length = 1} :=
  Cslib.Language.KleeneConverse.singletonDFA_accepts

example : ∃ r : RegularExpression Bool, r.matches' = language oneLetterDA ∧
    [true] ∈ r.matches' ∧ [] ∉ r.matches' ∧ [false, true] ∉ r.matches' := by
  obtain ⟨r, hr⟩ := Cslib.Language.KleeneConverse.exists_regex_of_da oneLetterDA
  refine ⟨r, hr, ?_, ?_, ?_⟩
  · rw [hr, oneLetterDA_language]
    change (1 : ℕ) = 1
    rfl
  · rw [hr, oneLetterDA_language]
    change ¬ (0 : ℕ) = 1
    decide
  · rw [hr, oneLetterDA_language]
    change ¬ (2 : ℕ) = 1
    decide

private def branchingOneLetter : NA.FinAcc (Fin 3) Bool where
  Tr s _ t := s = 0 ∧ (t = 1 ∨ t = 2)
  start := {0}
  accept := {1}

/-- One input can reach both the accepting state and a nonaccepting state. -/
example : branchingOneLetter.Tr 0 false 1 ∧ branchingOneLetter.Tr 0 false 2 :=
  ⟨⟨rfl, Or.inl rfl⟩, ⟨rfl, Or.inr rfl⟩⟩

private theorem branching_accepts (a : Bool) : [a] ∈ language branchingOneLetter := by
  exact ⟨0, rfl, 1, rfl, .stepL ⟨rfl, Or.inl rfl⟩ .refl⟩

private theorem branching_no_nil : [] ∉ language branchingOneLetter := by
  rintro ⟨s, hs, t, ht, h⟩
  change s = 0 at hs
  change t = 1 at ht
  subst s
  subst t
  have heq : (0 : Fin 3) = 1 := Cslib.LTS.MTr.nil_eq _ h
  exact (by decide : ¬ (0 : Fin 3) = 1) heq

private theorem branching_no_two (a b : Bool) : [a, b] ∉ language branchingOneLetter := by
  rintro ⟨s, hs, t, ht, h⟩
  change s = 0 at hs
  subst s
  obtain ⟨u, hfirst, htail⟩ := Cslib.LTS.MTr.cons_iff.mp h
  obtain ⟨v, hsecond, _⟩ := Cslib.LTS.MTr.cons_iff.mp htail
  change 0 = 0 ∧ (u = 1 ∨ u = 2) at hfirst
  change u = 0 ∧ (v = 1 ∨ v = 2) at hsecond
  rcases hfirst.2 with h1 | h2 <;> omega

example : ∃ r : RegularExpression Bool, r.matches' = language branchingOneLetter ∧
    [true] ∈ r.matches' ∧ [] ∉ r.matches' ∧ [false, true] ∉ r.matches' := by
  obtain ⟨r, hr⟩ := Cslib.Language.KleeneConverse.exists_regex_of_na branchingOneLetter
  exact ⟨r, hr, hr.symm ▸ branching_accepts true, hr.symm ▸ branching_no_nil,
    hr.symm ▸ branching_no_two false true⟩

private def emptyAlphabet : DA.FinAcc Unit Empty where
  tr _ symbol := nomatch symbol
  start := ()
  accept := Set.univ

example : ∃ r : RegularExpression Empty, r.matches' = language emptyAlphabet ∧ [] ∈ r.matches' := by
  obtain ⟨r, hr⟩ := Cslib.Language.KleeneConverse.exists_regex_of_da emptyAlphabet
  refine ⟨r, hr, ?_⟩
  rw [hr]
  trivial

end CslibTest.Computability.Languages.KleeneConverse

#print axioms Cslib.Language.KleeneConverse.exists_regex_of_da
#print axioms Cslib.Language.KleeneConverse.exists_regex_of_na
#print axioms Cslib.Language.IsRegular.exists_regex
#print axioms Cslib.Language.isRegular_iff_exists_regex
#print axioms Cslib.Language.exists_regular_not_regex
