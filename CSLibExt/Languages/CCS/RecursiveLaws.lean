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
# Strong laws for recursive CCS
-/
module

public import CSLibExt.Languages.CCS.Recursion

/-!
# Strong laws for recursive CCS

This module proves that process constants unfold up to strong bisimilarity and
that the fundamental finite-choice laws remain valid in the presence of a
recursive specification.  The proofs are deliberately specification-relative:
no guardedness assumption is needed for these one-step operational laws.

The presentation follows Robin Milner, *Communication and Concurrency*,
Prentice Hall, 1989, Chapter 4 (ISBN 978-0-13-115007-2).
-/

@[expose] public section

namespace Cslib.CCS.Recursive.Process

open Cslib.CCS Cslib.LTS

variable {Name Constant : Type*} [DecidableEq Name]
variable {specification : Specification Name Constant}

/-- Reflexive closure of a relation, used to prove one-equation laws. -/
def EquationClosure (relation : Process Name Constant → Process Name Constant → Prop)
    (left right : Process Name Constant) : Prop := left = right ∨ relation left right

theorem equationClosure_isBisimulation
    {relation : Process Name Constant → Process Name Constant → Prop}
    (forward : ∀ {left right action next}, relation left right →
      Step specification left action next →
      ∃ next', Step specification right action next' ∧
        EquationClosure relation next next')
    (backward : ∀ {left right action next}, relation left right →
      Step specification right action next →
      ∃ next', Step specification left action next' ∧
        EquationClosure relation next' next) :
    (lts specification).IsHomBisimulation (EquationClosure relation) := by
  intro left right related action
  constructor
  · intro next step
    rcases related with rfl | related
    · exact ⟨next, step, Or.inl rfl⟩
    · exact forward related step
  · intro next step
    rcases related with rfl | related
    · exact ⟨next, step, Or.inl rfl⟩
    · exact backward related step

/-- A process constant has exactly the behavior of its defining equation. -/
theorem constant_unfold (constant : Constant) :
    (lts specification).HomBisimilarity (.constant constant) (specification constant) := by
  let equation : Process Name Constant → Process Name Constant → Prop := fun left right =>
    left = .constant constant ∧ right = specification constant
  refine ⟨EquationClosure equation, Or.inr ⟨rfl, rfl⟩,
    equationClosure_isBisimulation ?_ ?_⟩
  · rintro left right action next ⟨rfl, rfl⟩ step
    exact ⟨next, constant_step_iff.mp step, Or.inl rfl⟩
  · rintro left right action next ⟨rfl, rfl⟩ step
    exact ⟨next, Step.unfold step, Or.inl rfl⟩

/-- Action prefix preserves strong bisimilarity. -/
theorem prefix_congr (action : Label Name) {left right : Process Name Constant}
    (related : (lts specification).HomBisimilarity left right) :
    (lts specification).HomBisimilarity (.prefix action left) (.prefix action right) := by
  obtain ⟨relation, hrel, bisimulation⟩ := related
  let lifted : Process Name Constant → Process Name Constant → Prop := fun source target =>
    (source = .prefix action left ∧ target = .prefix action right) ∨ relation source target
  refine ⟨lifted, Or.inl ⟨rfl, rfl⟩, ?_⟩
  intro source target hrel' label
  constructor
  · intro next step
    rcases hrel' with ⟨rfl, rfl⟩ | hrel'
    · cases step
      exact ⟨right, .prefix _ _, Or.inr hrel⟩
    · obtain ⟨next', step', related'⟩ := (bisimulation hrel' label).1 next step
      exact ⟨next', step', Or.inr related'⟩
  · intro next step
    rcases hrel' with ⟨rfl, rfl⟩ | hrel'
    · cases step
      exact ⟨left, .prefix _ _, Or.inr hrel⟩
    · obtain ⟨next', step', related'⟩ := (bisimulation hrel' label).2 next step
      exact ⟨next', step', Or.inr related'⟩

/-- Lift two bisimulation relations through nondeterministic choice. -/
inductive ChoiceLift
    (leftRel rightRel : Process Name Constant → Process Name Constant → Prop) :
    Process Name Constant → Process Name Constant → Prop
  | left {left₁ left₂} (related : leftRel left₁ left₂) :
      ChoiceLift leftRel rightRel left₁ left₂
  | right {right₁ right₂} (related : rightRel right₁ right₂) :
      ChoiceLift leftRel rightRel right₁ right₂
  | choice {left₁ left₂ right₁ right₂}
      (left : leftRel left₁ left₂) (right : rightRel right₁ right₂) :
      ChoiceLift leftRel rightRel (.choice left₁ right₁) (.choice left₂ right₂)

theorem choiceLift_isSimulation
    {leftRel rightRel : Process Name Constant → Process Name Constant → Prop}
    (hleft : (lts specification).IsHomSimulation leftRel)
    (hright : (lts specification).IsHomSimulation rightRel) :
    (lts specification).IsHomSimulation (ChoiceLift leftRel rightRel) := by
  intro source target related action next step
  cases related with
  | left related =>
      obtain ⟨next', step', related'⟩ := hleft related action next step
      exact ⟨next', step', .left related'⟩
  | right related =>
      obtain ⟨next', step', related'⟩ := hright related action next step
      exact ⟨next', step', .right related'⟩
  | choice leftRelated rightRelated =>
      change Step specification (.choice _ _) action next at step
      rw [choice_step_iff] at step
      rcases step with step | step
      · obtain ⟨next', step', related'⟩ := hleft leftRelated action next step
        exact ⟨next', .choiceLeft step', .left related'⟩
      · obtain ⟨next', step', related'⟩ := hright rightRelated action next step
        exact ⟨next', .choiceRight step', .right related'⟩

theorem choiceLift_isBisimulation
    {leftRel rightRel : Process Name Constant → Process Name Constant → Prop}
    (hleft : (lts specification).IsHomBisimulation leftRel)
    (hright : (lts specification).IsHomBisimulation rightRel) :
    (lts specification).IsHomBisimulation (ChoiceLift leftRel rightRel) := by
  intro source target related action
  constructor
  · exact choiceLift_isSimulation hleft.isSimulation hright.isSimulation related action
  · intro next step
    cases related with
    | left related =>
        obtain ⟨next', step', related'⟩ := (hleft related action).2 next step
        exact ⟨next', step', .left related'⟩
    | right related =>
        obtain ⟨next', step', related'⟩ := (hright related action).2 next step
        exact ⟨next', step', .right related'⟩
    | choice leftRelated rightRelated =>
        change Step specification (.choice _ _) action next at step
        rw [choice_step_iff] at step
        rcases step with step | step
        · obtain ⟨next', step', related'⟩ := (hleft leftRelated action).2 next step
          exact ⟨next', .choiceLeft step', .left related'⟩
        · obtain ⟨next', step', related'⟩ := (hright rightRelated action).2 next step
          exact ⟨next', .choiceRight step', .right related'⟩

/-- Choice preserves strong bisimilarity componentwise. -/
theorem choice_congr {left₁ left₂ right₁ right₂ : Process Name Constant}
    (leftRelated : (lts specification).HomBisimilarity left₁ left₂)
    (rightRelated : (lts specification).HomBisimilarity right₁ right₂) :
    (lts specification).HomBisimilarity (.choice left₁ right₁) (.choice left₂ right₂) := by
  obtain ⟨leftRel, hleft, leftBisimulation⟩ := leftRelated
  obtain ⟨rightRel, hright, rightBisimulation⟩ := rightRelated
  exact ⟨ChoiceLift leftRel rightRel, .choice hleft hright,
    choiceLift_isBisimulation leftBisimulation rightBisimulation⟩

/-- Lift component relations through parallel composition.  Derivatives of a
component are included directly because an interleaving transition consumes
the outer parallel constructor. -/
inductive ParallelLift
    (leftRel rightRel : Process Name Constant → Process Name Constant → Prop) :
    Process Name Constant → Process Name Constant → Prop
  | left {left₁ left₂} (related : leftRel left₁ left₂) :
      ParallelLift leftRel rightRel left₁ left₂
  | right {right₁ right₂} (related : rightRel right₁ right₂) :
      ParallelLift leftRel rightRel right₁ right₂
  | parallel {left₁ left₂ right₁ right₂}
      (left : leftRel left₁ left₂) (right : rightRel right₁ right₂) :
      ParallelLift leftRel rightRel (.parallel left₁ right₁) (.parallel left₂ right₂)

theorem parallelLift_isSimulation
    {leftRel rightRel : Process Name Constant → Process Name Constant → Prop}
    (hleft : (lts specification).IsHomSimulation leftRel)
    (hright : (lts specification).IsHomSimulation rightRel) :
    (lts specification).IsHomSimulation (ParallelLift leftRel rightRel) := by
  intro source target related action next step
  cases related with
  | left related =>
      obtain ⟨next', step', related'⟩ := hleft related action next step
      exact ⟨next', step', .left related'⟩
  | right related =>
      obtain ⟨next', step', related'⟩ := hright related action next step
      exact ⟨next', step', .right related'⟩
  | parallel leftRelated rightRelated =>
      change Step specification (.parallel _ _) action next at step
      cases step with
      | parallelLeft componentStep =>
          obtain ⟨next', step', related'⟩ := hleft leftRelated action _ componentStep
          exact ⟨.parallel next' _, .parallelLeft step', .parallel related' rightRelated⟩
      | parallelRight componentStep =>
          obtain ⟨next', step', related'⟩ := hright rightRelated action _ componentStep
          exact ⟨.parallel _ next', .parallelRight step', .parallel leftRelated related'⟩
      | communicate leftStep rightStep complementary =>
          obtain ⟨left', leftStep', leftRelated'⟩ := hleft leftRelated _ _ leftStep
          obtain ⟨right', rightStep', rightRelated'⟩ := hright rightRelated _ _ rightStep
          exact ⟨.parallel left' right',
            .communicate leftStep' rightStep' complementary,
            .parallel leftRelated' rightRelated'⟩

theorem parallelLift_isBisimulation
    {leftRel rightRel : Process Name Constant → Process Name Constant → Prop}
    (hleft : (lts specification).IsHomBisimulation leftRel)
    (hright : (lts specification).IsHomBisimulation rightRel) :
    (lts specification).IsHomBisimulation (ParallelLift leftRel rightRel) := by
  intro source target related action
  constructor
  · exact parallelLift_isSimulation hleft.isSimulation hright.isSimulation related action
  · intro next step
    cases related with
    | left related =>
        obtain ⟨next', step', related'⟩ := (hleft related action).2 next step
        exact ⟨next', step', .left related'⟩
    | right related =>
        obtain ⟨next', step', related'⟩ := (hright related action).2 next step
        exact ⟨next', step', .right related'⟩
    | parallel leftRelated rightRelated =>
        change Step specification (.parallel _ _) action next at step
        cases step with
        | parallelLeft componentStep =>
            obtain ⟨next', step', related'⟩ := (hleft leftRelated action).2 _ componentStep
            exact ⟨.parallel next' _, .parallelLeft step',
              .parallel related' rightRelated⟩
        | parallelRight componentStep =>
            obtain ⟨next', step', related'⟩ := (hright rightRelated action).2 _ componentStep
            exact ⟨.parallel _ next', .parallelRight step',
              .parallel leftRelated related'⟩
        | communicate leftStep rightStep complementary =>
            obtain ⟨left', leftStep', leftRelated'⟩ := (hleft leftRelated _).2 _ leftStep
            obtain ⟨right', rightStep', rightRelated'⟩ := (hright rightRelated _).2 _ rightStep
            exact ⟨.parallel left' right',
              .communicate leftStep' rightStep' complementary,
              .parallel leftRelated' rightRelated'⟩

/-- Parallel composition preserves strong bisimilarity componentwise. -/
theorem parallel_congr {left₁ left₂ right₁ right₂ : Process Name Constant}
    (leftRelated : (lts specification).HomBisimilarity left₁ left₂)
    (rightRelated : (lts specification).HomBisimilarity right₁ right₂) :
    (lts specification).HomBisimilarity (.parallel left₁ right₁) (.parallel left₂ right₂) := by
  obtain ⟨leftRel, hleft, leftBisimulation⟩ := leftRelated
  obtain ⟨rightRel, hright, rightBisimulation⟩ := rightRelated
  exact ⟨ParallelLift leftRel rightRel, .parallel hleft hright,
    parallelLift_isBisimulation leftBisimulation rightBisimulation⟩

/-- Parallel composition is commutative up to strong bisimilarity. -/
theorem parallel_comm (left right : Process Name Constant) :
    (lts specification).HomBisimilarity (.parallel left right) (.parallel right left) := by
  let equation : Process Name Constant → Process Name Constant → Prop := fun source target =>
    ∃ first second, source = .parallel first second ∧ target = .parallel second first
  refine ⟨EquationClosure equation, Or.inr ⟨left, right, rfl, rfl⟩,
    equationClosure_isBisimulation ?_ ?_⟩
  · rintro source target action next ⟨first, second, rfl, rfl⟩ step
    cases step with
    | parallelLeft componentStep =>
        exact ⟨.parallel second _, .parallelRight componentStep,
          Or.inr ⟨_, second, rfl, rfl⟩⟩
    | parallelRight componentStep =>
        exact ⟨.parallel _ first, .parallelLeft componentStep,
          Or.inr ⟨first, _, rfl, rfl⟩⟩
    | communicate leftStep rightStep complementary =>
        exact ⟨.parallel _ _, .communicate rightStep leftStep
          (Label.complementary_symm complementary),
          Or.inr ⟨_, _, rfl, rfl⟩⟩
  · rintro source target action next ⟨first, second, rfl, rfl⟩ step
    cases step with
    | parallelLeft componentStep =>
        exact ⟨.parallel first _, .parallelRight componentStep,
          Or.inr ⟨first, _, rfl, rfl⟩⟩
    | parallelRight componentStep =>
        exact ⟨.parallel _ second, .parallelLeft componentStep,
          Or.inr ⟨_, second, rfl, rfl⟩⟩
    | communicate leftStep rightStep complementary =>
        exact ⟨.parallel _ _, .communicate rightStep leftStep
          (Label.complementary_symm complementary),
          Or.inr ⟨_, _, rfl, rfl⟩⟩

/-- Inactive process is a left identity for parallel composition. -/
theorem parallel_nil_left (process : Process Name Constant) :
    (lts specification).HomBisimilarity (.parallel .nil process) process := by
  let equation : Process Name Constant → Process Name Constant → Prop := fun source target =>
    ∃ current, source = .parallel .nil current ∧ target = current
  refine ⟨EquationClosure equation, Or.inr ⟨process, rfl, rfl⟩,
    equationClosure_isBisimulation ?_ ?_⟩
  · rintro source target action next ⟨current, rfl, rfl⟩ step
    cases step with
    | parallelLeft impossible => exact False.elim (nil_no_step impossible)
    | parallelRight componentStep =>
        exact ⟨_, componentStep, Or.inr ⟨_, rfl, rfl⟩⟩
    | communicate impossible _ _ => exact False.elim (nil_no_step impossible)
  · rintro source target action next ⟨current, rfl, rfl⟩ step
    exact ⟨.parallel .nil next, .parallelRight step, Or.inr ⟨next, rfl, rfl⟩⟩

/-- Inactive process is a right identity for parallel composition. -/
theorem parallel_nil_right (process : Process Name Constant) :
    (lts specification).HomBisimilarity (.parallel process .nil) process :=
  (parallel_comm process .nil).trans (parallel_nil_left process)

/-- Lift a relation through one fixed restriction context. -/
inductive RestrictionLift (blocked : List Name)
    (relation : Process Name Constant → Process Name Constant → Prop) :
    Process Name Constant → Process Name Constant → Prop
  | base {left right} (related : relation left right) :
      RestrictionLift blocked relation left right
  | restriction {left right} (related : relation left right) :
      RestrictionLift blocked relation
        (.restriction blocked left) (.restriction blocked right)

theorem restrictionLift_isSimulation {blocked : List Name}
    {relation : Process Name Constant → Process Name Constant → Prop}
    (simulation : (lts specification).IsHomSimulation relation) :
    (lts specification).IsHomSimulation (RestrictionLift blocked relation) := by
  intro source target related action next step
  cases related with
  | base related =>
      obtain ⟨next', step', related'⟩ := simulation related action next step
      exact ⟨next', step', .base related'⟩
  | restriction related =>
      change Step specification (.restriction blocked _) action next at step
      rw [restriction_step_iff] at step
      obtain ⟨source', sourceStep, allowed, rfl⟩ := step
      obtain ⟨target', targetStep, related'⟩ := simulation related action source' sourceStep
      exact ⟨.restriction blocked target', .restrict targetStep allowed,
        .restriction related'⟩

theorem restrictionLift_isBisimulation {blocked : List Name}
    {relation : Process Name Constant → Process Name Constant → Prop}
    (bisimulation : (lts specification).IsHomBisimulation relation) :
    (lts specification).IsHomBisimulation (RestrictionLift blocked relation) := by
  intro source target related action
  constructor
  · exact restrictionLift_isSimulation bisimulation.isSimulation related action
  · intro next step
    cases related with
    | base related =>
        obtain ⟨next', step', related'⟩ := (bisimulation related action).2 next step
        exact ⟨next', step', .base related'⟩
    | restriction related =>
        change Step specification (.restriction blocked _) action next at step
        rw [restriction_step_iff] at step
        obtain ⟨target', targetStep, allowed, rfl⟩ := step
        obtain ⟨source', sourceStep, related'⟩ := (bisimulation related action).2 target' targetStep
        exact ⟨.restriction blocked source', .restrict sourceStep allowed,
          .restriction related'⟩

/-- Restriction preserves strong bisimilarity. -/
theorem restriction_congr (blocked : List Name) {left right : Process Name Constant}
    (related : (lts specification).HomBisimilarity left right) :
    (lts specification).HomBisimilarity
      (.restriction blocked left) (.restriction blocked right) := by
  obtain ⟨relation, hrel, bisimulation⟩ := related
  exact ⟨RestrictionLift blocked relation, .restriction hrel,
    restrictionLift_isBisimulation bisimulation⟩

/-- Lift a relation through one fixed relabelling context. -/
inductive RelabellingLift (rename : Relabelling Name)
    (relation : Process Name Constant → Process Name Constant → Prop) :
    Process Name Constant → Process Name Constant → Prop
  | base {left right} (related : relation left right) :
      RelabellingLift rename relation left right
  | relabelling {left right} (related : relation left right) :
      RelabellingLift rename relation
        (.relabelling rename left) (.relabelling rename right)

theorem relabellingLift_isSimulation {rename : Relabelling Name}
    {relation : Process Name Constant → Process Name Constant → Prop}
    (simulation : (lts specification).IsHomSimulation relation) :
    (lts specification).IsHomSimulation (RelabellingLift rename relation) := by
  intro source target related action next step
  cases related with
  | base related =>
      obtain ⟨next', step', related'⟩ := simulation related action next step
      exact ⟨next', step', .base related'⟩
  | relabelling related =>
      change Step specification (.relabelling rename _) action next at step
      rw [relabelling_step_iff] at step
      obtain ⟨sourceAction, source', sourceStep, rfl, rfl⟩ := step
      obtain ⟨target', targetStep, related'⟩ := simulation related sourceAction source' sourceStep
      exact ⟨.relabelling rename target', .relabel targetStep, .relabelling related'⟩

theorem relabellingLift_isBisimulation {rename : Relabelling Name}
    {relation : Process Name Constant → Process Name Constant → Prop}
    (bisimulation : (lts specification).IsHomBisimulation relation) :
    (lts specification).IsHomBisimulation (RelabellingLift rename relation) := by
  intro source target related action
  constructor
  · exact relabellingLift_isSimulation bisimulation.isSimulation related action
  · intro next step
    cases related with
    | base related =>
        obtain ⟨next', step', related'⟩ := (bisimulation related action).2 next step
        exact ⟨next', step', .base related'⟩
    | relabelling related =>
        change Step specification (.relabelling rename _) action next at step
        rw [relabelling_step_iff] at step
        obtain ⟨sourceAction, target', targetStep, rfl, rfl⟩ := step
        obtain ⟨source', sourceStep, related'⟩ :=
          (bisimulation related sourceAction).2 target' targetStep
        exact ⟨.relabelling rename source', .relabel sourceStep,
          .relabelling related'⟩

/-- Relabelling preserves strong bisimilarity. -/
theorem relabelling_congr (rename : Relabelling Name) {left right : Process Name Constant}
    (related : (lts specification).HomBisimilarity left right) :
    (lts specification).HomBisimilarity
      (.relabelling rename left) (.relabelling rename right) := by
  obtain ⟨relation, hrel, bisimulation⟩ := related
  exact ⟨RelabellingLift rename relation, .relabelling hrel,
    relabellingLift_isBisimulation bisimulation⟩

/-- Nondeterministic choice is commutative up to strong bisimilarity. -/
theorem choice_comm (left right : Process Name Constant) :
    (lts specification).HomBisimilarity (.choice left right) (.choice right left) := by
  let equation : Process Name Constant → Process Name Constant → Prop := fun source target =>
    source = .choice left right ∧ target = .choice right left
  refine ⟨EquationClosure equation, Or.inr ⟨rfl, rfl⟩,
    equationClosure_isBisimulation ?_ ?_⟩
  · rintro source target action next ⟨rfl, rfl⟩ step
    rw [choice_step_iff] at step
    exact ⟨next, choice_step_iff.mpr step.symm, Or.inl rfl⟩
  · rintro source target action next ⟨rfl, rfl⟩ step
    rw [choice_step_iff] at step
    exact ⟨next, choice_step_iff.mpr step.symm, Or.inl rfl⟩

/-- Inactive process is a left identity for choice. -/
theorem choice_nil_left (process : Process Name Constant) :
    (lts specification).HomBisimilarity (.choice .nil process) process := by
  let equation : Process Name Constant → Process Name Constant → Prop := fun source target =>
    source = .choice .nil process ∧ target = process
  refine ⟨EquationClosure equation, Or.inr ⟨rfl, rfl⟩,
    equationClosure_isBisimulation ?_ ?_⟩
  · rintro source target action next ⟨rfl, rfl⟩ step
    rw [choice_step_iff] at step
    rcases step with impossible | step
    · exact False.elim (nil_no_step impossible)
    · exact ⟨next, step, Or.inl rfl⟩
  · rintro source target action next ⟨rfl, rfl⟩ step
    exact ⟨next, .choiceRight step, Or.inl rfl⟩

/-- Inactive process is a right identity for choice. -/
theorem choice_nil_right (process : Process Name Constant) :
    (lts specification).HomBisimilarity (.choice process .nil) process :=
  (choice_comm process .nil).trans (choice_nil_left process)

/-- Choice is idempotent up to strong bisimilarity. -/
theorem choice_self (process : Process Name Constant) :
    (lts specification).HomBisimilarity (.choice process process) process := by
  let equation : Process Name Constant → Process Name Constant → Prop := fun source target =>
    source = .choice process process ∧ target = process
  refine ⟨EquationClosure equation, Or.inr ⟨rfl, rfl⟩,
    equationClosure_isBisimulation ?_ ?_⟩
  · rintro source target action next ⟨rfl, rfl⟩ step
    rw [choice_step_iff] at step
    exact ⟨next, step.elim id id, Or.inl rfl⟩
  · rintro source target action next ⟨rfl, rfl⟩ step
    exact ⟨next, .choiceLeft step, Or.inl rfl⟩

/-- Choice is associative up to strong bisimilarity. -/
theorem choice_assoc (first second third : Process Name Constant) :
    (lts specification).HomBisimilarity
      (.choice (.choice first second) third)
      (.choice first (.choice second third)) := by
  let equation : Process Name Constant → Process Name Constant → Prop := fun source target =>
    source = .choice (.choice first second) third ∧
      target = .choice first (.choice second third)
  refine ⟨EquationClosure equation, Or.inr ⟨rfl, rfl⟩,
    equationClosure_isBisimulation ?_ ?_⟩
  · rintro source target action next ⟨rfl, rfl⟩ step
    rw [choice_step_iff, choice_step_iff] at step
    refine ⟨next, ?_, Or.inl rfl⟩
    rcases step with (step | step) | step
    · exact .choiceLeft step
    · exact .choiceRight (.choiceLeft step)
    · exact .choiceRight (.choiceRight step)
  · rintro source target action next ⟨rfl, rfl⟩ step
    rw [choice_step_iff, choice_step_iff] at step
    refine ⟨next, ?_, Or.inl rfl⟩
    rcases step with step | step | step
    · exact .choiceLeft (.choiceLeft step)
    · exact .choiceLeft (.choiceRight step)
    · exact .choiceRight step

end Cslib.CCS.Recursive.Process
