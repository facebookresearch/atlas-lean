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
# Strong laws for CCS static operators
-/
module

public import CSLibExt.Languages.CCS.StaticOperators

/-!
# Strong laws for CCS static operators

This file develops the standard strong-equivalence equations for finite CCS
restriction and relabelling.  Both operators preserve termination and
nondeterministic choice.  Restriction either preserves or suppresses a
prefixed transition according to its channel set, while relabelling transforms
the prefix label.  Empty restriction and empty relabelling are identities, and
restrictions with extensionally equal blocked-name sets are equivalent.

The equations follow Robin Milner, *Communication and Concurrency*, Prentice
Hall, 1989, Chapters 2--3 (ISBN 978-0-13-115007-2).
-/

@[expose] public section

namespace Cslib.CCS.StaticProcess

open Cslib.LTS

variable {Name : Type*} [DecidableEq Name]

/-- Close an explicitly supplied family of equations under equality. -/
def EquationClosure (equation : StaticProcess Name → StaticProcess Name → Prop) :
    StaticProcess Name → StaticProcess Name → Prop :=
  fun left right => left = right ∨ equation left right

/-- Prove a family of equations by matching one transition in either
direction and returning another equation instance for the derivatives. -/
theorem equationClosure_isBisimulation
    {equation : StaticProcess Name → StaticProcess Name → Prop}
    (hforward : ∀ ⦃left right action next⦄, equation left right →
      Step left action next →
      ∃ next', Step right action next' ∧ EquationClosure equation next next')
    (hbackward : ∀ ⦃left right action next⦄, equation left right →
      Step right action next →
      ∃ next', Step left action next' ∧ EquationClosure equation next' next) :
    lts.IsHomBisimulation (EquationClosure equation) := by
  intro left right hrel action
  constructor
  · intro next hstep
    rcases hrel with rfl | hrel
    · exact ⟨next, hstep, Or.inl rfl⟩
    · exact hforward hrel hstep
  · intro next hstep
    rcases hrel with rfl | hrel
    · exact ⟨next, hstep, Or.inl rfl⟩
    · exact hbackward hrel hstep

/-- Restriction preserves terminated processes. -/
theorem restriction_nil (blocked : List Name) :
    lts.HomBisimilarity (.restriction blocked .nil) .nil := by
  let equation : StaticProcess Name → StaticProcess Name → Prop := fun left right =>
    left = .restriction blocked .nil ∧ right = .nil
  refine ⟨EquationClosure equation, Or.inr ⟨rfl, rfl⟩,
    equationClosure_isBisimulation ?_ ?_⟩
  · rintro left right action next ⟨rfl, rfl⟩ hstep
    rw [restriction_step_iff] at hstep
    obtain ⟨_, hnil, _, _⟩ := hstep
    exact False.elim (nil_no_step hnil)
  · rintro left right action next ⟨rfl, rfl⟩ hstep
    exact False.elim (nil_no_step hstep)

/-- An allowed prefix passes through restriction. -/
theorem restriction_prefix_of_allowed (blocked : List Name) (action : Label Name)
    (continuation : StaticProcess Name) (allowed : Allowed blocked action) :
    lts.HomBisimilarity (.restriction blocked (.prefix action continuation))
      (.prefix action (.restriction blocked continuation)) := by
  let equation : StaticProcess Name → StaticProcess Name → Prop := fun left right =>
    left = .restriction blocked (.prefix action continuation) ∧
      right = .prefix action (.restriction blocked continuation)
  refine ⟨EquationClosure equation, Or.inr ⟨rfl, rfl⟩,
    equationClosure_isBisimulation ?_ ?_⟩
  · rintro left right label next ⟨rfl, rfl⟩ hstep
    rw [restriction_step_iff] at hstep
    obtain ⟨next', hprefix, _, rfl⟩ := hstep
    rw [prefix_step_iff] at hprefix
    obtain ⟨rfl, rfl⟩ := hprefix
    exact ⟨_, .prefix _ _, Or.inl rfl⟩
  · rintro left right label next ⟨rfl, rfl⟩ hstep
    rw [prefix_step_iff] at hstep
    obtain ⟨rfl, rfl⟩ := hstep
    exact ⟨_, .restrict (.prefix _ _) allowed, Or.inl rfl⟩

/-- A blocked prefix has no transition and is strongly equivalent to
termination. -/
theorem restriction_prefix_of_blocked (blocked : List Name) (action : Label Name)
    (continuation : StaticProcess Name) (blockedAction : ¬Allowed blocked action) :
    lts.HomBisimilarity (.restriction blocked (.prefix action continuation)) .nil := by
  let equation : StaticProcess Name → StaticProcess Name → Prop := fun left right =>
    left = .restriction blocked (.prefix action continuation) ∧ right = .nil
  refine ⟨EquationClosure equation, Or.inr ⟨rfl, rfl⟩,
    equationClosure_isBisimulation ?_ ?_⟩
  · rintro left right label next ⟨rfl, rfl⟩ hstep
    rw [restriction_step_iff] at hstep
    obtain ⟨next', hprefix, allowed, rfl⟩ := hstep
    rw [prefix_step_iff] at hprefix
    exact False.elim (blockedAction (hprefix.1 ▸ allowed))
  · rintro left right label next ⟨rfl, rfl⟩ hstep
    exact False.elim (nil_no_step hstep)

/-- Restriction distributes over finite nondeterministic choice. -/
theorem restriction_choice (blocked : List Name) (left right : StaticProcess Name) :
    lts.HomBisimilarity (.restriction blocked (.choice left right))
      (.choice (.restriction blocked left) (.restriction blocked right)) := by
  let equation : StaticProcess Name → StaticProcess Name → Prop := fun source target =>
    source = .restriction blocked (.choice left right) ∧
      target = .choice (.restriction blocked left) (.restriction blocked right)
  refine ⟨EquationClosure equation, Or.inr ⟨rfl, rfl⟩,
    equationClosure_isBisimulation ?_ ?_⟩
  · rintro source target action next ⟨rfl, rfl⟩ hstep
    rw [restriction_step_iff] at hstep
    obtain ⟨next', hchoice, allowed, rfl⟩ := hstep
    rw [choice_step_iff] at hchoice
    rcases hchoice with hleft | hright
    · exact ⟨_, .choiceLeft (.restrict hleft allowed), Or.inl rfl⟩
    · exact ⟨_, .choiceRight (.restrict hright allowed), Or.inl rfl⟩
  · rintro source target action next ⟨rfl, rfl⟩ hstep
    rw [choice_step_iff] at hstep
    rcases hstep with hleft | hright
    · rw [restriction_step_iff] at hleft
      obtain ⟨next', hnext, allowed, rfl⟩ := hleft
      exact ⟨_, .restrict (.choiceLeft hnext) allowed, Or.inl rfl⟩
    · rw [restriction_step_iff] at hright
      obtain ⟨next', hnext, allowed, rfl⟩ := hright
      exact ⟨_, .restrict (.choiceRight hnext) allowed, Or.inl rfl⟩

/-- Empty restriction is a strong identity on every process. -/
theorem restriction_empty (process : StaticProcess Name) :
    lts.HomBisimilarity (.restriction [] process) process := by
  let equation : StaticProcess Name → StaticProcess Name → Prop := fun left right =>
    ∃ current, left = .restriction [] current ∧ right = current
  refine ⟨EquationClosure equation, Or.inr ⟨process, rfl, rfl⟩,
    equationClosure_isBisimulation ?_ ?_⟩
  · rintro left right action next ⟨current, rfl, rfl⟩ hstep
    rw [restriction_step_iff] at hstep
    obtain ⟨next', hnext, _, rfl⟩ := hstep
    exact ⟨next', hnext, Or.inr ⟨next', rfl, rfl⟩⟩
  · rintro left right action next ⟨current, rfl, rfl⟩ hstep
    exact ⟨.restriction [] next, .restrict hstep (by cases action <;> simp [Allowed]),
      Or.inr ⟨next, rfl, rfl⟩⟩

/-- Restrictions with the same blocked-name membership are strongly
equivalent. -/
theorem restriction_congr_list {first second : List Name}
    (same : ∀ name, name ∈ first ↔ name ∈ second) (process : StaticProcess Name) :
    lts.HomBisimilarity (.restriction first process) (.restriction second process) := by
  let equation : StaticProcess Name → StaticProcess Name → Prop := fun left right =>
    ∃ current, left = .restriction first current ∧ right = .restriction second current
  have allowed_iff (action : Label Name) : Allowed first action ↔ Allowed second action := by
    cases action with
    | tau => simp
    | input name => simpa using not_congr (same name)
    | output name => simpa using not_congr (same name)
  refine ⟨EquationClosure equation, Or.inr ⟨process, rfl, rfl⟩,
    equationClosure_isBisimulation ?_ ?_⟩
  · rintro left right action next ⟨current, rfl, rfl⟩ hstep
    rw [restriction_step_iff] at hstep
    obtain ⟨next', hnext, allowed, rfl⟩ := hstep
    exact ⟨.restriction second next', .restrict hnext ((allowed_iff action).mp allowed),
      Or.inr ⟨next', rfl, rfl⟩⟩
  · rintro left right action next ⟨current, rfl, rfl⟩ hstep
    rw [restriction_step_iff] at hstep
    obtain ⟨next', hnext, allowed, rfl⟩ := hstep
    exact ⟨.restriction first next', .restrict hnext ((allowed_iff action).mpr allowed),
      Or.inr ⟨next', rfl, rfl⟩⟩

/-- Relabelling preserves terminated processes. -/
theorem relabelling_nil (rename : Relabelling Name) :
    lts.HomBisimilarity (.relabelling rename .nil) .nil := by
  let equation : StaticProcess Name → StaticProcess Name → Prop := fun left right =>
    left = .relabelling rename .nil ∧ right = .nil
  refine ⟨EquationClosure equation, Or.inr ⟨rfl, rfl⟩,
    equationClosure_isBisimulation ?_ ?_⟩
  · rintro left right action next ⟨rfl, rfl⟩ hstep
    rw [relabelling_step_iff] at hstep
    obtain ⟨_, _, hnil, _, _⟩ := hstep
    exact False.elim (nil_no_step hnil)
  · rintro left right action next ⟨rfl, rfl⟩ hstep
    exact False.elim (nil_no_step hstep)

/-- Relabelling transforms a prefix label. -/
theorem relabelling_prefix (rename : Relabelling Name) (action : Label Name)
    (continuation : StaticProcess Name) :
    lts.HomBisimilarity (.relabelling rename (.prefix action continuation))
      (.prefix (relabelAction rename action) (.relabelling rename continuation)) := by
  let equation : StaticProcess Name → StaticProcess Name → Prop := fun left right =>
    left = .relabelling rename (.prefix action continuation) ∧
      right = .prefix (relabelAction rename action) (.relabelling rename continuation)
  refine ⟨EquationClosure equation, Or.inr ⟨rfl, rfl⟩,
    equationClosure_isBisimulation ?_ ?_⟩
  · rintro left right label next ⟨rfl, rfl⟩ hstep
    rw [relabelling_step_iff] at hstep
    obtain ⟨sourceAction, next', hprefix, rfl, rfl⟩ := hstep
    rw [prefix_step_iff] at hprefix
    obtain ⟨rfl, rfl⟩ := hprefix
    exact ⟨_, .prefix _ _, Or.inl rfl⟩
  · rintro left right label next ⟨rfl, rfl⟩ hstep
    rw [prefix_step_iff] at hstep
    obtain ⟨rfl, rfl⟩ := hstep
    exact ⟨_, .relabel (.prefix _ _), Or.inl rfl⟩

/-- Relabelling distributes over finite nondeterministic choice. -/
theorem relabelling_choice (rename : Relabelling Name) (left right : StaticProcess Name) :
    lts.HomBisimilarity (.relabelling rename (.choice left right))
      (.choice (.relabelling rename left) (.relabelling rename right)) := by
  let equation : StaticProcess Name → StaticProcess Name → Prop := fun source target =>
    source = .relabelling rename (.choice left right) ∧
      target = .choice (.relabelling rename left) (.relabelling rename right)
  refine ⟨EquationClosure equation, Or.inr ⟨rfl, rfl⟩,
    equationClosure_isBisimulation ?_ ?_⟩
  · rintro source target action next ⟨rfl, rfl⟩ hstep
    rw [relabelling_step_iff] at hstep
    obtain ⟨sourceAction, next', hchoice, rfl, rfl⟩ := hstep
    rw [choice_step_iff] at hchoice
    rcases hchoice with hleft | hright
    · exact ⟨_, .choiceLeft (.relabel hleft), Or.inl rfl⟩
    · exact ⟨_, .choiceRight (.relabel hright), Or.inl rfl⟩
  · rintro source target action next ⟨rfl, rfl⟩ hstep
    rw [choice_step_iff] at hstep
    rcases hstep with hleft | hright
    · rw [relabelling_step_iff] at hleft
      obtain ⟨sourceAction, next', hnext, rfl, rfl⟩ := hleft
      exact ⟨_, .relabel (.choiceLeft hnext), Or.inl rfl⟩
    · rw [relabelling_step_iff] at hright
      obtain ⟨sourceAction, next', hnext, rfl, rfl⟩ := hright
      exact ⟨_, .relabel (.choiceRight hnext), Or.inl rfl⟩

/-- Empty relabelling is a strong identity on every process. -/
theorem relabelling_empty (process : StaticProcess Name) :
    lts.HomBisimilarity (.relabelling ⟨[]⟩ process) process := by
  let equation : StaticProcess Name → StaticProcess Name → Prop := fun left right =>
    ∃ current, left = .relabelling ⟨[]⟩ current ∧ right = current
  have unchanged (action : Label Name) : relabelAction (Relabelling.mk []) action = action := by
    cases action <;> simp [relabelAction, Relabelling.apply, Relabelling.applyEntries,
      VisibleLabel.toLabel, VisibleLabel.complement]
  refine ⟨EquationClosure equation, Or.inr ⟨process, rfl, rfl⟩,
    equationClosure_isBisimulation ?_ ?_⟩
  · rintro left right action next ⟨current, rfl, rfl⟩ hstep
    rw [relabelling_step_iff] at hstep
    obtain ⟨sourceAction, next', hnext, actionEq, rfl⟩ := hstep
    rw [unchanged] at actionEq
    subst sourceAction
    exact ⟨next', hnext, Or.inr ⟨next', rfl, rfl⟩⟩
  · rintro left right action next ⟨current, rfl, rfl⟩ hstep
    exact ⟨.relabelling ⟨[]⟩ next,
      unchanged action ▸ Step.relabel (rename := Relabelling.mk []) hstep,
      Or.inr ⟨next, rfl, rfl⟩⟩

end Cslib.CCS.StaticProcess
