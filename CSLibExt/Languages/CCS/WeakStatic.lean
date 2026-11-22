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
# Weak equivalence for extended finite CCS
-/
module

public import CSLibExt.Foundations.Semantics.LTS.ObservationCongruence
public import CSLibExt.Languages.CCS.StrongCongruence

/-!
# Weak equivalence for extended finite CCS

This module develops weak bisimilarity and rooted observational congruence for
the finite CCS language with restriction and relabelling. Silent closures,
weak transitions, and rooted weak transitions are lifted through both static
operators. These constructions establish weak and rooted congruence for
restriction and relabelling, as well as rooted congruence for prefix and
choice in the extended syntax.

The development follows Robin Milner, *Communication and Concurrency*,
Prentice Hall, 1989, Chapter 5 (ISBN 978-0-13-115007-2).
-/

@[expose] public section

namespace Cslib.CCS.StaticProcess

open Cslib.LTS

variable {Name : Type*} [DecidableEq Name]

/-- Specialization of ordinary weak bisimilarity to extended finite CCS. -/
abbrev WeaklyBisimilar (left right : StaticProcess Name) : Prop :=
  lts.HomWeakBisimilarity left right

/-- Specialization of rooted weak bisimilarity to extended finite CCS. -/
abbrev ObservationCongruent (left right : StaticProcess Name) : Prop :=
  Cslib.LTS.RootedWeaklyBisimilar (lts := lts) left right

/-- Silent reductions lift through a fixed restriction context. -/
theorem τSTr.restriction {blocked : List Name}
    {process process' : StaticProcess Name}
    (hclosure : lts.τSTr process process') :
    lts.τSTr (.restriction blocked process) (.restriction blocked process') := by
  induction hclosure using Relation.ReflTransGen.head_induction_on with
  | refl => exact .refl
  | head step _ ih => exact τSTr.cons (.restrict step (allowed_tau _)) ih

/-- Silent reductions lift through a fixed relabelling context. -/
theorem τSTr.relabelling {rename : Relabelling Name}
    {process process' : StaticProcess Name}
    (hclosure : lts.τSTr process process') :
    lts.τSTr (.relabelling rename process) (.relabelling rename process') := by
  induction hclosure using Relation.ReflTransGen.head_induction_on with
  | refl => exact .refl
  | head step _ ih => exact τSTr.cons (.relabel step) ih

/-- A weak transition whose label is allowed by a restriction lifts through
that restriction. -/
theorem STr.restriction {blocked : List Name} {process process' : StaticProcess Name}
    {action : Label Name} (hstep : lts.STr process action process')
    (allowed : Allowed blocked action) :
    lts.STr (.restriction blocked process) action
      (.restriction blocked process') := by
  cases hstep with
  | refl => exact _root_.Cslib.LTS.STr.refl
  | tr hprefix hvis hsuffix =>
      exact _root_.Cslib.LTS.STr.tr (τSTr.restriction hprefix)
        (.restrict hvis allowed) (τSTr.restriction hsuffix)

private theorem relabelAction_ne_tau {rename : Relabelling Name} {action : Label Name}
    (hne : action ≠ .tau) : relabelAction rename action ≠ .tau := by
  cases action with
  | tau => exact False.elim (hne rfl)
  | input name =>
      cases hrename : rename.apply name <;>
        simp [relabelAction, hrename, VisibleLabel.toLabel]
  | output name =>
      cases hrename : rename.apply name <;>
        simp [relabelAction, hrename, VisibleLabel.complement, VisibleLabel.toLabel]

/-- Relabelling maps weak transitions, including all silent preparation and
cleanup steps. -/
theorem STr.relabelling {rename : Relabelling Name}
    {process process' : StaticProcess Name} {action : Label Name}
    (hstep : lts.STr process action process') :
    lts.STr (.relabelling rename process)
      (relabelAction rename action) (.relabelling rename process') := by
  cases hstep with
  | refl => exact _root_.Cslib.LTS.STr.refl
  | tr hprefix hvis hsuffix =>
      exact _root_.Cslib.LTS.STr.tr (τSTr.relabelling hprefix)
        (.relabel hvis) (τSTr.relabelling hsuffix)

/-- An allowed rooted weak transition lifts through restriction. -/
theorem RootedWeakStep.restriction {blocked : List Name}
    {process process' : StaticProcess Name} {action : Label Name}
    (hstep : Cslib.LTS.RootedWeakStep (lts := lts) process action process')
    (allowed : Allowed blocked action) :
    Cslib.LTS.RootedWeakStep (lts := lts) (.restriction blocked process) action
      (.restriction blocked process') := by
  obtain ⟨before, after, hprefix, hmiddle, hsuffix⟩ := hstep
  exact ⟨.restriction blocked before, .restriction blocked after,
    τSTr.restriction hprefix, .restrict hmiddle allowed,
    τSTr.restriction hsuffix⟩

/-- A rooted weak transition lifts through relabelling. -/
theorem RootedWeakStep.relabelling {rename : Relabelling Name}
    {process process' : StaticProcess Name} {action : Label Name}
    (hstep : Cslib.LTS.RootedWeakStep (lts := lts) process action process') :
    Cslib.LTS.RootedWeakStep (lts := lts) (.relabelling rename process)
      (relabelAction rename action) (.relabelling rename process') := by
  obtain ⟨before, after, hprefix, hmiddle, hsuffix⟩ := hstep
  exact ⟨.relabelling rename before, .relabelling rename after,
    τSTr.relabelling hprefix, .relabel hmiddle,
    τSTr.relabelling hsuffix⟩

/-- Weak simulation is preserved by a fixed restriction context. -/
theorem restrictionLift_isWeakSimulation {blocked : List Name}
    {relation : StaticProcess Name → StaticProcess Name → Prop}
    (hsim : lts.saturate.IsHomSimulation relation) :
    lts.saturate.IsHomSimulation (RestrictionLift blocked relation) := by
  apply _root_.Cslib.LTS.IsSimulation.isSimulation_saturate_left
  intro source target hrel action next hstep
  cases hrel with
  | base hrel =>
      obtain ⟨next', hnext', hrel'⟩ := hsim hrel action next (STr.single hstep)
      exact ⟨next', hnext', .base hrel'⟩
  | restriction hrel =>
      change Step (.restriction blocked _) action next at hstep
      rw [restriction_step_iff] at hstep
      obtain ⟨source', hsource', allowed, rfl⟩ := hstep
      obtain ⟨target', htarget', hrel'⟩ :=
        hsim hrel action source' (STr.single hsource')
      exact ⟨.restriction blocked target', STr.restriction htarget' allowed,
        .restriction hrel'⟩

/-- Weak bisimulation is preserved by a fixed restriction context. -/
theorem restrictionLift_isWeakBisimulation {blocked : List Name}
    {relation : StaticProcess Name → StaticProcess Name → Prop}
    (hbisim : lts.IsHomWeakBisimulation relation) :
    lts.IsHomWeakBisimulation
      (RestrictionLift blocked relation) := by
  apply _root_.Cslib.LTS.IsSWBisimulation.isWeakBisimulation
  intro source target hrel action
  constructor
  · intro next hstep
    cases hrel with
    | base hrel =>
        obtain ⟨next', hnext', hrel'⟩ :=
          hbisim.isSimulation hrel action next (STr.single hstep)
        exact ⟨next', hnext', .base hrel'⟩
    | restriction hrel =>
        change Step (.restriction blocked _) action next at hstep
        rw [restriction_step_iff] at hstep
        obtain ⟨source', hsource', allowed, rfl⟩ := hstep
        obtain ⟨target', htarget', hrel'⟩ :=
          hbisim.isSimulation hrel action source' (STr.single hsource')
        exact ⟨.restriction blocked target', STr.restriction htarget' allowed,
          .restriction hrel'⟩
  · intro next hstep
    cases hrel with
    | base hrel =>
        obtain ⟨next', hnext', hrel'⟩ :=
          hbisim.flip_isSimulation hrel action next (STr.single hstep)
        exact ⟨next', hnext', .base hrel'⟩
    | restriction hrel =>
        change Step (.restriction blocked _) action next at hstep
        rw [restriction_step_iff] at hstep
        obtain ⟨target', htarget', allowed, rfl⟩ := hstep
        obtain ⟨source', hsource', hrel'⟩ :=
          hbisim.flip_isSimulation hrel action target' (STr.single htarget')
        exact ⟨.restriction blocked source', STr.restriction hsource' allowed,
          .restriction hrel'⟩

/-- Restriction preserves ordinary weak bisimilarity. -/
theorem restriction_weaklyBisimilar_congr (blocked : List Name)
    {left right : StaticProcess Name} (h : WeaklyBisimilar left right) :
    WeaklyBisimilar (.restriction blocked left) (.restriction blocked right) := by
  obtain ⟨relation, hrel, hbisim⟩ := h
  exact ⟨RestrictionLift blocked relation, .restriction hrel,
    restrictionLift_isWeakBisimulation hbisim⟩

/-- Weak simulation is preserved by a fixed relabelling context. -/
theorem relabellingLift_isWeakSimulation {rename : Relabelling Name}
    {relation : StaticProcess Name → StaticProcess Name → Prop}
    (hsim : lts.saturate.IsHomSimulation relation) :
    lts.saturate.IsHomSimulation (RelabellingLift rename relation) := by
  apply _root_.Cslib.LTS.IsSimulation.isSimulation_saturate_left
  intro source target hrel action next hstep
  cases hrel with
  | base hrel =>
      obtain ⟨next', hnext', hrel'⟩ := hsim hrel action next (STr.single hstep)
      exact ⟨next', hnext', .base hrel'⟩
  | relabelling hrel =>
      change Step (.relabelling rename _) action next at hstep
      rw [relabelling_step_iff] at hstep
      obtain ⟨sourceAction, source', hsource', rfl, rfl⟩ := hstep
      obtain ⟨target', htarget', hrel'⟩ :=
        hsim hrel sourceAction source' (STr.single hsource')
      exact ⟨.relabelling rename target', STr.relabelling htarget',
        .relabelling hrel'⟩

/-- Weak bisimulation is preserved by a fixed relabelling context. -/
theorem relabellingLift_isWeakBisimulation {rename : Relabelling Name}
    {relation : StaticProcess Name → StaticProcess Name → Prop}
    (hbisim : lts.IsHomWeakBisimulation relation) :
    lts.IsHomWeakBisimulation
      (RelabellingLift rename relation) := by
  apply _root_.Cslib.LTS.IsSWBisimulation.isWeakBisimulation
  intro source target hrel action
  constructor
  · intro next hstep
    cases hrel with
    | base hrel =>
        obtain ⟨next', hnext', hrel'⟩ :=
          hbisim.isSimulation hrel action next (STr.single hstep)
        exact ⟨next', hnext', .base hrel'⟩
    | relabelling hrel =>
        change Step (.relabelling rename _) action next at hstep
        rw [relabelling_step_iff] at hstep
        obtain ⟨sourceAction, source', hsource', rfl, rfl⟩ := hstep
        obtain ⟨target', htarget', hrel'⟩ :=
          hbisim.isSimulation hrel sourceAction source' (STr.single hsource')
        exact ⟨.relabelling rename target', STr.relabelling htarget',
          .relabelling hrel'⟩
  · intro next hstep
    cases hrel with
    | base hrel =>
        obtain ⟨next', hnext', hrel'⟩ :=
          hbisim.flip_isSimulation hrel action next (STr.single hstep)
        exact ⟨next', hnext', .base hrel'⟩
    | relabelling hrel =>
        change Step (.relabelling rename _) action next at hstep
        rw [relabelling_step_iff] at hstep
        obtain ⟨sourceAction, target', htarget', rfl, rfl⟩ := hstep
        obtain ⟨source', hsource', hrel'⟩ :=
          hbisim.flip_isSimulation hrel sourceAction target' (STr.single htarget')
        exact ⟨.relabelling rename source', STr.relabelling hsource',
          .relabelling hrel'⟩

/-- Relabelling preserves ordinary weak bisimilarity. -/
theorem relabelling_weaklyBisimilar_congr (rename : Relabelling Name)
    {left right : StaticProcess Name} (h : WeaklyBisimilar left right) :
    WeaklyBisimilar (.relabelling rename left) (.relabelling rename right) := by
  obtain ⟨relation, hrel, hbisim⟩ := h
  exact ⟨RelabellingLift rename relation, .relabelling hrel,
    relabellingLift_isWeakBisimulation hbisim⟩

/-- Restriction preserves rooted observational congruence. -/
theorem restriction_observationCongruent_congr (blocked : List Name)
    {left right : StaticProcess Name} (h : ObservationCongruent left right) :
    ObservationCongruent (.restriction blocked left) (.restriction blocked right) := by
  constructor
  · intro action next hstep
    change Step (.restriction blocked left) action next at hstep
    rw [restriction_step_iff] at hstep
    obtain ⟨left', hleft', allowed, rfl⟩ := hstep
    obtain ⟨right', hright', hnext⟩ := h.1 hleft'
    exact ⟨.restriction blocked right', RootedWeakStep.restriction hright' allowed,
      restriction_weaklyBisimilar_congr blocked hnext⟩
  · intro action next hstep
    change Step (.restriction blocked right) action next at hstep
    rw [restriction_step_iff] at hstep
    obtain ⟨right', hright', allowed, rfl⟩ := hstep
    obtain ⟨left', hleft', hnext⟩ := h.2 hright'
    exact ⟨.restriction blocked left', RootedWeakStep.restriction hleft' allowed,
      restriction_weaklyBisimilar_congr blocked hnext⟩

/-- Relabelling preserves rooted observational congruence. -/
theorem relabelling_observationCongruent_congr (rename : Relabelling Name)
    {left right : StaticProcess Name} (h : ObservationCongruent left right) :
    ObservationCongruent (.relabelling rename left) (.relabelling rename right) := by
  constructor
  · intro action next hstep
    change Step (.relabelling rename left) action next at hstep
    rw [relabelling_step_iff] at hstep
    obtain ⟨sourceAction, left', hleft', rfl, rfl⟩ := hstep
    obtain ⟨right', hright', hnext⟩ := h.1 hleft'
    exact ⟨.relabelling rename right', RootedWeakStep.relabelling hright',
      relabelling_weaklyBisimilar_congr rename hnext⟩
  · intro action next hstep
    change Step (.relabelling rename right) action next at hstep
    rw [relabelling_step_iff] at hstep
    obtain ⟨sourceAction, right', hright', rfl, rfl⟩ := hstep
    obtain ⟨left', hleft', hnext⟩ := h.2 hright'
    exact ⟨.relabelling rename left', RootedWeakStep.relabelling hleft',
      relabelling_weaklyBisimilar_congr rename hnext⟩

/-- Prefix converts weak equivalence of continuations into observational
congruence. -/
theorem prefix_observationCongruent (action : Label Name)
    {left right : StaticProcess Name} (h : WeaklyBisimilar left right) :
    ObservationCongruent (.prefix action left) (.prefix action right) := by
  constructor
  · intro label next hstep
    change Step (.prefix action left) label next at hstep
    rw [prefix_step_iff] at hstep
    obtain ⟨rfl, rfl⟩ := hstep
    exact ⟨right, rootedWeakStep_of_tr (.prefix _ _), h⟩
  · intro label next hstep
    change Step (.prefix action right) label next at hstep
    rw [prefix_step_iff] at hstep
    obtain ⟨rfl, rfl⟩ := hstep
    exact ⟨left, rootedWeakStep_of_tr (.prefix _ _), h⟩

private theorem silentClosure_choice_left_to_rooted
    {left right before after target : StaticProcess Name} {action : Label Name}
    (hprefix : lts.τSTr left before) (hmiddle : Step before action after)
    (hsuffix : lts.τSTr after target) :
    Cslib.LTS.RootedWeakStep (lts := lts) (.choice left right) action target := by
  rcases Relation.ReflTransGen.cases_head hprefix with hEq | ⟨middle, head, tail⟩
  · subst before
    exact ⟨.choice left right, after, .refl, .choiceLeft hmiddle, hsuffix⟩
  · exact ⟨before, after, τSTr.cons (.choiceLeft head) tail, hmiddle, hsuffix⟩

private theorem silentClosure_choice_right_to_rooted
    {left right before after target : StaticProcess Name} {action : Label Name}
    (hprefix : lts.τSTr right before) (hmiddle : Step before action after)
    (hsuffix : lts.τSTr after target) :
    Cslib.LTS.RootedWeakStep (lts := lts) (.choice left right) action target := by
  rcases Relation.ReflTransGen.cases_head hprefix with hEq | ⟨middle, head, tail⟩
  · subst before
    exact ⟨.choice left right, after, .refl, .choiceRight hmiddle, hsuffix⟩
  · exact ⟨before, after, τSTr.cons (.choiceRight head) tail, hmiddle, hsuffix⟩

theorem RootedWeakStep.choiceLeft {left target right : StaticProcess Name}
    {action : Label Name} (hstep : Cslib.LTS.RootedWeakStep (lts := lts) left action target) :
    Cslib.LTS.RootedWeakStep (lts := lts) (.choice left right) action target := by
  obtain ⟨before, after, hprefix, hmiddle, hsuffix⟩ := hstep
  exact silentClosure_choice_left_to_rooted hprefix hmiddle hsuffix

theorem RootedWeakStep.choiceRight {right target left : StaticProcess Name}
    {action : Label Name} (hstep : Cslib.LTS.RootedWeakStep (lts := lts) right action target) :
    Cslib.LTS.RootedWeakStep (lts := lts) (.choice left right) action target := by
  obtain ⟨before, after, hprefix, hmiddle, hsuffix⟩ := hstep
  exact silentClosure_choice_right_to_rooted hprefix hmiddle hsuffix

/-- Choice preserves observational congruence componentwise. -/
theorem choice_observationCongruent_congr
    {left₁ left₂ right₁ right₂ : StaticProcess Name}
    (hleft : ObservationCongruent left₁ left₂)
    (hright : ObservationCongruent right₁ right₂) :
    ObservationCongruent (.choice left₁ right₁) (.choice left₂ right₂) := by
  constructor
  · intro action next hstep
    change Step (.choice left₁ right₁) action next at hstep
    rw [choice_step_iff] at hstep
    rcases hstep with hstep | hstep
    · obtain ⟨next', hnext', hrel⟩ := hleft.1 hstep
      exact ⟨next', RootedWeakStep.choiceLeft hnext', hrel⟩
    · obtain ⟨next', hnext', hrel⟩ := hright.1 hstep
      exact ⟨next', RootedWeakStep.choiceRight hnext', hrel⟩
  · intro action next hstep
    change Step (.choice left₂ right₂) action next at hstep
    rw [choice_step_iff] at hstep
    rcases hstep with hstep | hstep
    · obtain ⟨next', hnext', hrel⟩ := hleft.2 hstep
      exact ⟨next', RootedWeakStep.choiceLeft hnext', hrel⟩
    · obtain ⟨next', hnext', hrel⟩ := hright.2 hstep
      exact ⟨next', RootedWeakStep.choiceRight hnext', hrel⟩

/-- A silent prefix is eliminated by ordinary weak bisimilarity. -/
theorem tau_prefix_weaklyBisimilar (process : StaticProcess Name) :
    WeaklyBisimilar (.prefix .tau process) process := by
  let relation : StaticProcess Name → StaticProcess Name → Prop := fun left right =>
    (left = .prefix .tau process ∧ right = process) ∨ left = right
  have hbisim : lts.IsHomWeakBisimulation relation := by
    apply _root_.Cslib.LTS.IsSWBisimulation.isWeakBisimulation
    intro left right hrel action
    constructor
    · intro next hstep
      rcases hrel with ⟨rfl, rfl⟩ | rfl
      · change Step (.prefix .tau right) action next at hstep
        rw [prefix_step_iff] at hstep
        obtain ⟨rfl, rfl⟩ := hstep
        exact ⟨next, STr.refl, Or.inr rfl⟩
      · exact ⟨next, STr.single hstep, Or.inr rfl⟩
    · intro next hstep
      rcases hrel with ⟨rfl, rfl⟩ | rfl
      · exact ⟨next,
          _root_.Cslib.LTS.STr.tr (τSTr.of_tr (.prefix .tau right)) hstep
            Relation.ReflTransGen.refl,
          Or.inr rfl⟩
      · exact ⟨next, STr.single hstep, Or.inr rfl⟩
  exact ⟨relation, Or.inl ⟨rfl, rfl⟩, hbisim⟩

end Cslib.CCS.StaticProcess
