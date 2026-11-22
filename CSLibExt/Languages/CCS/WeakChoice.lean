/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Ported from fairinternal/formal-math at `9db2af32bec4c1fe1731f17c030e9410961257ed`.
Original formalization by Zeina Migeed (@migeed-z); ported with permission.
-/

/-
# Weak equivalence for finite CCS choice processes
-/
module

public import CSLibExt.Foundations.Semantics.LTS.ObservationCongruence
public import CSLibExt.Languages.CCS.Choice

/-!
# Weak equivalence and observation congruence for finite CCS

This file instantiates weak-transition theory for the finite CCS fragment with
a distinguished silent action.  Ordinary weak bisimilarity validates the
silent-prefix law, but is not preserved by nondeterministic choice.  We
therefore define the standard rooted variant, here called observational
congruence, and prove that prefix and binary choice preserve it.

The definitions and laws follow Robin Milner, *Communication and Concurrency*,
Prentice Hall, 1989, Chapter 5 (ISBN 978-0-13-115007-2), especially the
distinction between observational equivalence and observational congruence.
-/

@[expose] public section

namespace Cslib.CCS

namespace Process

open Cslib Cslib.LTS

variable {Action : Type*} [HasTau Action]

private theorem silentClosure_choice_left_to_rooted
    {left right before after target : Process Action} {label : Action}
    (hprefix : (lts (Action := Action)).τSTr left before)
    (hmiddle : Step before label after)
    (hsuffix : (lts (Action := Action)).τSTr after target) :
    RootedWeakStep (lts := lts (Action := Action))
      (.choice left right) label target := by
  rcases Relation.ReflTransGen.cases_head hprefix with hEq | ⟨middle, head, tail⟩
  · subst before
    exact ⟨.choice left right, after, Relation.ReflTransGen.refl, .choiceLeft hmiddle,
      hsuffix⟩
  · exact ⟨before, after, τSTr.cons (.choiceLeft head) tail, hmiddle, hsuffix⟩

private theorem silentClosure_choice_right_to_rooted
    {left right before after target : Process Action} {label : Action}
    (hprefix : (lts (Action := Action)).τSTr right before)
    (hmiddle : Step before label after)
    (hsuffix : (lts (Action := Action)).τSTr after target) :
    RootedWeakStep (lts := lts (Action := Action))
      (.choice left right) label target := by
  rcases Relation.ReflTransGen.cases_head hprefix with hEq | ⟨middle, head, tail⟩
  · subst before
    exact ⟨.choice left right, after, Relation.ReflTransGen.refl, .choiceRight hmiddle,
      hsuffix⟩
  · exact ⟨before, after, τSTr.cons (.choiceRight head) tail, hmiddle, hsuffix⟩

/-- A rooted weak transition of the left summand lifts through choice. -/
theorem rootedWeakStep_choiceLeft {left target right : Process Action}
    {label : Action}
    (hstep : RootedWeakStep (lts := (lts (Action := Action))) left label target) :
    RootedWeakStep (lts := lts (Action := Action))
      (.choice left right) label target := by
  obtain ⟨before, after, hprefix, hmiddle, hsuffix⟩ := hstep
  exact silentClosure_choice_left_to_rooted hprefix hmiddle hsuffix

/-- A rooted weak transition of the right summand lifts through choice. -/
theorem rootedWeakStep_choiceRight {right target left : Process Action}
    {label : Action}
    (hstep : RootedWeakStep (lts := (lts (Action := Action))) right label target) :
    RootedWeakStep (lts := lts (Action := Action))
      (.choice left right) label target := by
  obtain ⟨before, after, hprefix, hmiddle, hsuffix⟩ := hstep
  exact silentClosure_choice_right_to_rooted hprefix hmiddle hsuffix

/-- Compatibility specialization of generic observational congruence to the
finite CCS transition system. -/
abbrev ObservationCongruent (left right : Process Action) : Prop :=
  RootedWeaklyBisimilar (lts := (lts (Action := Action))) left right

/-- Prefix preserves weak bisimilarity as observational congruence. -/
theorem prefix_observationCongruent (action : Action) {left right : Process Action}
    (hcontinuation :
      HomWeakBisimilarity (lts (Action := Action)) left right) :
    ObservationCongruent (.prefix action left) (.prefix action right) := by
  constructor
  · intro label next hstep
    change Step (.prefix action left) label next at hstep
    rw [prefix_step_iff] at hstep
    obtain ⟨rfl, rfl⟩ := hstep
    exact ⟨right, rootedWeakStep_of_tr (.prefix _ _), hcontinuation⟩
  · intro label next hstep
    change Step (.prefix action right) label next at hstep
    rw [prefix_step_iff] at hstep
    obtain ⟨rfl, rfl⟩ := hstep
    exact ⟨left, rootedWeakStep_of_tr (.prefix _ _), hcontinuation⟩

/-- Binary choice preserves observational congruence. -/
theorem choice_observationCongruent {left₁ left₂ right₁ right₂ : Process Action}
    (hleft : ObservationCongruent left₁ left₂)
    (hright : ObservationCongruent right₁ right₂) :
    ObservationCongruent (.choice left₁ right₁) (.choice left₂ right₂) := by
  constructor
  · intro label next hstep
    change Step (.choice left₁ right₁) label next at hstep
    rw [choice_step_iff] at hstep
    rcases hstep with hstep | hstep
    · obtain ⟨next', hnext', hrel⟩ := hleft.1 hstep
      exact ⟨next', rootedWeakStep_choiceLeft hnext', hrel⟩
    · obtain ⟨next', hnext', hrel⟩ := hright.1 hstep
      exact ⟨next', rootedWeakStep_choiceRight hnext', hrel⟩
  · intro label next hstep
    change Step (.choice left₂ right₂) label next at hstep
    rw [choice_step_iff] at hstep
    rcases hstep with hstep | hstep
    · obtain ⟨next', hnext', hrel⟩ := hleft.2 hstep
      exact ⟨next', rootedWeakStep_choiceLeft hnext', hrel⟩
    · obtain ⟨next', hnext', hrel⟩ := hright.2 hstep
      exact ⟨next', rootedWeakStep_choiceRight hnext', hrel⟩

/-- Prefix preserves observational congruence componentwise. -/
theorem prefix_observationCongruent_congr (action : Action) {left right : Process Action}
    (hcontinuation : ObservationCongruent left right) :
    ObservationCongruent (.prefix action left) (.prefix action right) :=
  prefix_observationCongruent action hcontinuation.to_homWeakBisimilarity

/-- Ordinary weak bisimilarity validates elimination of one silent prefix. -/
theorem tau_prefix_weaklyBisimilar (process : Process Action) :
    HomWeakBisimilarity (lts (Action := Action))
      (.prefix HasTau.τ process) process := by
  let relation : Process Action → Process Action → Prop := fun left right =>
    left = .prefix HasTau.τ process ∧ right = process ∨ left = right
  have hbisim : IsWeakBisimulation
      (lts (Action := Action)) (lts (Action := Action)) relation := by
    apply _root_.Cslib.LTS.IsSWBisimulation.isWeakBisimulation
    intro left right hrel label
    constructor
    · intro next hstep
      rcases hrel with hpair | heq
      · rcases hpair with ⟨hleft, hright⟩
        rw [hleft] at hstep
        change Step (.prefix HasTau.τ process) label next at hstep
        rw [prefix_step_iff] at hstep
        obtain ⟨hlabel, hnext⟩ := hstep
        rw [hright]
        subst label
        rw [← hnext]
        exact ⟨next, STr.refl, Or.inr rfl⟩
      · exact ⟨next, STr.single (heq ▸ hstep), Or.inr rfl⟩
    · intro next hstep
      rcases hrel with hpair | heq
      · rcases hpair with ⟨hleft, hright⟩
        rw [hright] at hstep
        change Step process label next at hstep
        rw [hleft]
        exact ⟨next,
          _root_.Cslib.LTS.STr.tr (τSTr.of_tr (.prefix HasTau.τ process)) hstep
            τSTr.refl,
          Or.inr rfl⟩
      · exact ⟨next, STr.single (heq.symm ▸ hstep), Or.inr rfl⟩
  exact ⟨relation, Or.inl ⟨rfl, rfl⟩, hbisim⟩

/-- Commutativity of choice, restated at the observational-congruence level. -/
theorem choice_comm_observationCongruent (left right : Process Action) :
    ObservationCongruent (.choice left right) (.choice right left) :=
  observationCongruent_of_bisimilar (choice_comm left right)

/-- Associativity of choice, restated at the observational-congruence level. -/
theorem choice_assoc_observationCongruent (first second third : Process Action) :
    ObservationCongruent
      (.choice (.choice first second) third)
      (.choice first (.choice second third)) :=
  observationCongruent_of_bisimilar (choice_assoc first second third)

/-- Idempotence of choice, restated at the observational-congruence level. -/
theorem choice_idem_observationCongruent (process : Process Action) :
    ObservationCongruent (.choice process process) process :=
  observationCongruent_of_bisimilar (choice_idem process)

/-- Nil is a left identity for choice under observational congruence. -/
theorem choice_nil_left_observationCongruent (process : Process Action) :
    ObservationCongruent (.choice .nil process) process :=
  observationCongruent_of_bisimilar (choice_nil_left process)

/-- Nil is a right identity for choice under observational congruence. -/
theorem choice_nil_right_observationCongruent (process : Process Action) :
    ObservationCongruent (.choice process .nil) process :=
  observationCongruent_of_bisimilar (choice_nil_right process)

end Process

end Cslib.CCS
