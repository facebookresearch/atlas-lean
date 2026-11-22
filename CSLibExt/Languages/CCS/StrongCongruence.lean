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
# Strong congruence for extended finite CCS
-/
module

public import CSLibExt.Languages.CCS.StaticLaws

/-!
# Strong congruence for extended finite CCS

Strong bisimilarity is a congruence for action prefix, nondeterministic choice,
and parallel composition in the finite CCS language with static operators.
It also establishes commutativity, a left unit, and idempotence for
nondeterministic choice, all up to strong bisimilarity.

The results follow Robin Milner, *Communication and Concurrency*, Prentice
Hall, 1989, Chapters 2--3 (ISBN 978-0-13-115007-2).
-/

@[expose] public section

namespace Cslib.CCS.StaticProcess

open Cslib.LTS

variable {Name : Type*} [DecidableEq Name]

/-- Action prefix preserves strong bisimilarity. -/
theorem prefix_congr (action : Label Name) {left right : StaticProcess Name}
    (h : lts.HomBisimilarity left right) :
    lts.HomBisimilarity (.prefix action left) (.prefix action right) := by
  obtain ⟨relation, hrel, hbisim⟩ := h
  let lifted : StaticProcess Name → StaticProcess Name → Prop := fun source target =>
    (source = .prefix action left ∧ target = .prefix action right) ∨ relation source target
  refine ⟨lifted, Or.inl ⟨rfl, rfl⟩, ?_⟩
  apply _root_.Cslib.LTS.IsBisimulation.isSimulation_iff.mpr
  constructor
  · intro source target hrel' label next hstep
    rcases hrel' with ⟨rfl, rfl⟩ | hrel'
    · cases hstep
      exact ⟨right, .prefix _ _, Or.inr hrel⟩
    · obtain ⟨next', hnext', hrel''⟩ := hbisim.isSimulation hrel' label next hstep
      exact ⟨next', hnext', Or.inr hrel''⟩
  · intro target source hrel' label next hstep
    rcases hrel' with ⟨rfl, rfl⟩ | hrel'
    · cases hstep
      exact ⟨left, .prefix _ _, Or.inr hrel⟩
    · obtain ⟨next', hnext', hrel''⟩ := hbisim.flip_isSimulation hrel' label next hstep
      exact ⟨next', hnext', Or.inr hrel''⟩

/-- Lift two relations through nondeterministic choice. -/
inductive ChoiceLift
    (leftRel rightRel : StaticProcess Name → StaticProcess Name → Prop) :
    StaticProcess Name → StaticProcess Name → Prop
  | left {left₁ left₂} (related : leftRel left₁ left₂) :
      ChoiceLift leftRel rightRel left₁ left₂
  | right {right₁ right₂} (related : rightRel right₁ right₂) :
      ChoiceLift leftRel rightRel right₁ right₂
  | choice {left₁ left₂ right₁ right₂}
      (left : leftRel left₁ left₂) (right : rightRel right₁ right₂) :
      ChoiceLift leftRel rightRel (.choice left₁ right₁) (.choice left₂ right₂)

theorem choiceLift_isSimulation
    {leftRel rightRel : StaticProcess Name → StaticProcess Name → Prop}
    (hleft : lts.IsHomSimulation leftRel) (hright : lts.IsHomSimulation rightRel) :
    lts.IsHomSimulation (ChoiceLift leftRel rightRel) := by
  intro source target hrel action next hstep
  cases hrel with
  | left hrel =>
      obtain ⟨next', hnext', hrel'⟩ := hleft hrel action next hstep
      exact ⟨next', hnext', .left hrel'⟩
  | right hrel =>
      obtain ⟨next', hnext', hrel'⟩ := hright hrel action next hstep
      exact ⟨next', hnext', .right hrel'⟩
  | choice hleftRel hrightRel =>
      change Step (.choice _ _) action next at hstep
      rw [choice_step_iff] at hstep
      rcases hstep with hstep | hstep
      · obtain ⟨next', hnext', hrel'⟩ := hleft hleftRel action _ hstep
        exact ⟨next', .choiceLeft hnext', .left hrel'⟩
      · obtain ⟨next', hnext', hrel'⟩ := hright hrightRel action _ hstep
        exact ⟨next', .choiceRight hnext', .right hrel'⟩

theorem choiceLift_isBisimulation
    {leftRel rightRel : StaticProcess Name → StaticProcess Name → Prop}
    (hleft : lts.IsHomBisimulation leftRel) (hright : lts.IsHomBisimulation rightRel) :
    lts.IsHomBisimulation (ChoiceLift leftRel rightRel) := by
  apply _root_.Cslib.LTS.IsBisimulation.isSimulation_iff.mpr
  constructor
  · exact choiceLift_isSimulation hleft.isSimulation hright.isSimulation
  · intro target source hrel action next hstep
    cases hrel with
    | left hrel =>
        obtain ⟨next', hnext', hrel'⟩ :=
          hleft.flip_isSimulation hrel action next hstep
        exact ⟨next', hnext', .left hrel'⟩
    | right hrel =>
        obtain ⟨next', hnext', hrel'⟩ :=
          hright.flip_isSimulation hrel action next hstep
        exact ⟨next', hnext', .right hrel'⟩
    | choice hleftRel hrightRel =>
        change Step (.choice _ _) action next at hstep
        rw [choice_step_iff] at hstep
        rcases hstep with hstep | hstep
        · obtain ⟨next', hnext', hrel'⟩ :=
            hleft.flip_isSimulation hleftRel action _ hstep
          exact ⟨next', .choiceLeft hnext', .left hrel'⟩
        · obtain ⟨next', hnext', hrel'⟩ :=
            hright.flip_isSimulation hrightRel action _ hstep
          exact ⟨next', .choiceRight hnext', .right hrel'⟩

/-- Choice preserves strong bisimilarity componentwise. -/
theorem choice_congr {left₁ left₂ right₁ right₂ : StaticProcess Name}
    (hleft : lts.HomBisimilarity left₁ left₂) (hright : lts.HomBisimilarity right₁ right₂) :
    lts.HomBisimilarity (.choice left₁ right₁) (.choice left₂ right₂) := by
  obtain ⟨leftRel, hleftRel, hleftBisim⟩ := hleft
  obtain ⟨rightRel, hrightRel, hrightBisim⟩ := hright
  exact ⟨ChoiceLift leftRel rightRel, .choice hleftRel hrightRel,
    choiceLift_isBisimulation hleftBisim hrightBisim⟩

/-- Lift two relations componentwise through parallel composition. -/
inductive ParallelLift
    (leftRel rightRel : StaticProcess Name → StaticProcess Name → Prop) :
    StaticProcess Name → StaticProcess Name → Prop
  | left {left₁ left₂} (related : leftRel left₁ left₂) :
      ParallelLift leftRel rightRel left₁ left₂
  | right {right₁ right₂} (related : rightRel right₁ right₂) :
      ParallelLift leftRel rightRel right₁ right₂
  | parallel {left₁ left₂ right₁ right₂}
      (left : leftRel left₁ left₂) (right : rightRel right₁ right₂) :
      ParallelLift leftRel rightRel (.parallel left₁ right₁) (.parallel left₂ right₂)

theorem parallelLift_isSimulation
    {leftRel rightRel : StaticProcess Name → StaticProcess Name → Prop}
    (hleft : lts.IsHomSimulation leftRel) (hright : lts.IsHomSimulation rightRel) :
    lts.IsHomSimulation (ParallelLift leftRel rightRel) := by
  intro source target hrel action next hstep
  cases hrel with
  | left hrel =>
      obtain ⟨next', hnext', hrel'⟩ := hleft hrel action next hstep
      exact ⟨next', hnext', .left hrel'⟩
  | right hrel =>
      obtain ⟨next', hnext', hrel'⟩ := hright hrel action next hstep
      exact ⟨next', hnext', .right hrel'⟩
  | parallel hleftRel hrightRel =>
      cases hstep with
      | parallelLeft step =>
          obtain ⟨next', hnext', hrel'⟩ := hleft hleftRel action _ step
          exact ⟨.parallel next' _, .parallelLeft hnext', .parallel hrel' hrightRel⟩
      | parallelRight step =>
          obtain ⟨next', hnext', hrel'⟩ := hright hrightRel action _ step
          exact ⟨.parallel _ next', .parallelRight hnext', .parallel hleftRel hrel'⟩
      | communicate leftStep rightStep complementary =>
          obtain ⟨left', hleft', hleftRel'⟩ := hleft hleftRel _ _ leftStep
          obtain ⟨right', hright', hrightRel'⟩ := hright hrightRel _ _ rightStep
          exact ⟨.parallel left' right', .communicate hleft' hright' complementary,
            .parallel hleftRel' hrightRel'⟩

theorem parallelLift_isBisimulation
    {leftRel rightRel : StaticProcess Name → StaticProcess Name → Prop}
    (hleft : lts.IsHomBisimulation leftRel) (hright : lts.IsHomBisimulation rightRel) :
    lts.IsHomBisimulation (ParallelLift leftRel rightRel) := by
  apply _root_.Cslib.LTS.IsBisimulation.isSimulation_iff.mpr
  constructor
  · exact parallelLift_isSimulation hleft.isSimulation hright.isSimulation
  · intro target source hrel action next hstep
    cases hrel with
    | left hrel =>
        obtain ⟨next', hnext', hrel'⟩ :=
          hleft.flip_isSimulation hrel action next hstep
        exact ⟨next', hnext', .left hrel'⟩
    | right hrel =>
        obtain ⟨next', hnext', hrel'⟩ :=
          hright.flip_isSimulation hrel action next hstep
        exact ⟨next', hnext', .right hrel'⟩
    | parallel hleftRel hrightRel =>
        cases hstep with
        | parallelLeft step =>
            obtain ⟨next', hnext', hrel'⟩ :=
              hleft.flip_isSimulation hleftRel action _ step
            exact ⟨.parallel next' _, .parallelLeft hnext', .parallel hrel' hrightRel⟩
        | parallelRight step =>
            obtain ⟨next', hnext', hrel'⟩ :=
              hright.flip_isSimulation hrightRel action _ step
            exact ⟨.parallel _ next', .parallelRight hnext', .parallel hleftRel hrel'⟩
        | communicate leftStep rightStep complementary =>
            obtain ⟨left', hleft', hleftRel'⟩ :=
              hleft.flip_isSimulation hleftRel _ _ leftStep
            obtain ⟨right', hright', hrightRel'⟩ :=
              hright.flip_isSimulation hrightRel _ _ rightStep
            exact ⟨.parallel left' right', .communicate hleft' hright'
              complementary, .parallel hleftRel' hrightRel'⟩

/-- Parallel composition preserves strong bisimilarity componentwise. -/
theorem parallel_congr {left₁ left₂ right₁ right₂ : StaticProcess Name}
    (hleft : lts.HomBisimilarity left₁ left₂) (hright : lts.HomBisimilarity right₁ right₂) :
    lts.HomBisimilarity (.parallel left₁ right₁) (.parallel left₂ right₂) := by
  obtain ⟨leftRel, hleftRel, hleftBisim⟩ := hleft
  obtain ⟨rightRel, hrightRel, hrightBisim⟩ := hright
  exact ⟨ParallelLift leftRel rightRel, .parallel hleftRel hrightRel,
    parallelLift_isBisimulation hleftBisim hrightBisim⟩

/-- Nondeterministic choice is commutative up to strong bisimilarity. -/
theorem choice_comm (left right : StaticProcess Name) :
    lts.HomBisimilarity (.choice left right) (.choice right left) := by
  let equation : StaticProcess Name → StaticProcess Name → Prop := fun source target =>
    source = .choice left right ∧ target = .choice right left
  refine ⟨EquationClosure equation, Or.inr ⟨rfl, rfl⟩,
    equationClosure_isBisimulation ?_ ?_⟩
  · rintro source target action next ⟨rfl, rfl⟩ hstep
    rw [choice_step_iff] at hstep
    exact ⟨next, choice_step_iff.mpr hstep.symm, Or.inl rfl⟩
  · rintro source target action next ⟨rfl, rfl⟩ hstep
    rw [choice_step_iff] at hstep
    exact ⟨next, choice_step_iff.mpr hstep.symm, Or.inl rfl⟩

/-- Termination is a left identity for choice. -/
theorem choice_nil_left (process : StaticProcess Name) :
    lts.HomBisimilarity (.choice .nil process) process := by
  let equation : StaticProcess Name → StaticProcess Name → Prop := fun source target =>
    source = .choice .nil process ∧ target = process
  refine ⟨EquationClosure equation, Or.inr ⟨rfl, rfl⟩,
    equationClosure_isBisimulation ?_ ?_⟩
  · rintro source target action next ⟨rfl, rfl⟩ hstep
    rw [choice_step_iff] at hstep
    rcases hstep with hnil | hstep
    · exact False.elim (nil_no_step hnil)
    · exact ⟨next, hstep, Or.inl rfl⟩
  · rintro source target action next ⟨rfl, rfl⟩ hstep
    exact ⟨next, .choiceRight hstep, Or.inl rfl⟩

/-- Choice is idempotent up to strong bisimilarity. -/
theorem choice_self (process : StaticProcess Name) :
    lts.HomBisimilarity (.choice process process) process := by
  let equation : StaticProcess Name → StaticProcess Name → Prop := fun source target =>
    source = .choice process process ∧ target = process
  refine ⟨EquationClosure equation, Or.inr ⟨rfl, rfl⟩,
    equationClosure_isBisimulation ?_ ?_⟩
  · rintro source target action next ⟨rfl, rfl⟩ hstep
    rw [choice_step_iff] at hstep
    exact ⟨next, hstep.elim id id, Or.inl rfl⟩
  · rintro source target action next ⟨rfl, rfl⟩ hstep
    exact ⟨next, .choiceLeft hstep, Or.inl rfl⟩

end Cslib.CCS.StaticProcess
