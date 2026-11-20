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
# Weak parallel congruence for extended finite CCS
-/
module

public import CSLibExt.Languages.CCS.WeakStatic

/-!
# Weak parallel congruence for extended finite CCS

This module completes the weak static-operator theory by lifting silent,
weak, and rooted weak transitions through parallel composition. Complementary
weak transitions synchronize after arbitrary silent preparation and before
arbitrary silent cleanup. The resulting construction proves that both weak
bisimilarity and rooted observational congruence are preserved by parallel
composition in the extended CCS syntax.

The development follows Robin Milner, *Communication and Concurrency*,
Prentice Hall, 1989, Chapter 5 (ISBN 978-0-13-115007-2).
-/

@[expose] public section

namespace Cslib.CCS.StaticProcess

open Cslib.LTS

variable {Name : Type*} [DecidableEq Name]

/-- Silent reductions of the left component lift through a fixed parallel
context. -/
theorem τSTr.parallelLeft {left left' right : StaticProcess Name}
    (hclosure : lts.τSTr left left') :
    lts.τSTr (.parallel left right) (.parallel left' right) := by
  induction hclosure using Relation.ReflTransGen.head_induction_on with
  | refl => exact .refl
  | head step _ ih => exact τSTr.cons (.parallelLeft step) ih

/-- Silent reductions of the right component lift through a fixed parallel
context. -/
theorem τSTr.parallelRight {left right right' : StaticProcess Name}
    (hclosure : lts.τSTr right right') :
    lts.τSTr (.parallel left right) (.parallel left right') := by
  induction hclosure using Relation.ReflTransGen.head_induction_on with
  | refl => exact .refl
  | head step _ ih => exact τSTr.cons (.parallelRight step) ih

/-- A weak transition of the left component lifts through parallel
composition. -/
theorem STr.parallelLeft {left left' right : StaticProcess Name}
    {action : Label Name} (hstep : lts.STr left action left') :
    lts.STr (.parallel left right) action
      (.parallel left' right) := by
  cases hstep with
  | refl => exact _root_.Cslib.LTS.STr.refl
  | tr hprefix hvis hsuffix =>
      exact _root_.Cslib.LTS.STr.tr (τSTr.parallelLeft hprefix)
        (.parallelLeft hvis) (τSTr.parallelLeft hsuffix)

/-- A weak transition of the right component lifts through parallel
composition. -/
theorem STr.parallelRight {left right right' : StaticProcess Name}
    {action : Label Name} (hstep : lts.STr right action right') :
    lts.STr (.parallel left right) action
      (.parallel left right') := by
  cases hstep with
  | refl => exact _root_.Cslib.LTS.STr.refl
  | tr hprefix hvis hsuffix =>
      exact _root_.Cslib.LTS.STr.tr (τSTr.parallelRight hprefix)
        (.parallelRight hvis) (τSTr.parallelRight hsuffix)

/-- A rooted weak transition of the left component lifts through a fixed
parallel context. -/
theorem RootedWeakStep.parallelLeft {left left' right : StaticProcess Name}
    {action : Label Name} (hstep : Cslib.LTS.RootedWeakStep (lts := lts) left action left') :
    Cslib.LTS.RootedWeakStep (lts := lts) (.parallel left right) action
      (.parallel left' right) := by
  obtain ⟨before, after, hprefix, hmiddle, hsuffix⟩ := hstep
  exact ⟨.parallel before right, .parallel after right,
    τSTr.parallelLeft hprefix, .parallelLeft hmiddle,
    τSTr.parallelLeft hsuffix⟩

/-- A rooted weak transition of the right component lifts through a fixed
parallel context. -/
theorem RootedWeakStep.parallelRight {left right right' : StaticProcess Name}
    {action : Label Name} (hstep : Cslib.LTS.RootedWeakStep (lts := lts) right action right') :
    Cslib.LTS.RootedWeakStep (lts := lts) (.parallel left right) action
      (.parallel left right') := by
  obtain ⟨before, after, hprefix, hmiddle, hsuffix⟩ := hstep
  exact ⟨.parallel left before, .parallel left after,
    τSTr.parallelRight hprefix, .parallelRight hmiddle,
    τSTr.parallelRight hsuffix⟩

omit [DecidableEq Name] in
private theorem complementary_ne_tau_left {left right : Label Name}
    (h : left.Complementary right) : left ≠ .tau := by
  intro heq
  subst left
  exact Label.not_complementary_tau_left right h

omit [DecidableEq Name] in
private theorem complementary_ne_tau_right {left right : Label Name}
    (h : left.Complementary right) : right ≠ .tau :=
  complementary_ne_tau_left (Label.complementary_symm h)

/-- Complementary weak transitions synchronize to a silent closure of their
parallel composition. -/
theorem weakComplementary_parallel
    {left left' right right' : StaticProcess Name}
    {leftAction rightAction : Label Name}
    (hleft : lts.STr left leftAction left')
    (hright : lts.STr right rightAction right')
    (hcomplementary : leftAction.Complementary rightAction) :
    lts.τSTr (.parallel left right) (.parallel left' right') := by
  cases hleft with
  | refl => exact (complementary_ne_tau_left hcomplementary rfl).elim
  | tr leftPrefix leftVisible leftSuffix =>
    cases hright with
    | refl => exact (complementary_ne_tau_right hcomplementary rfl).elim
    | tr rightPrefix rightVisible rightSuffix =>
      exact τSTr.parallelLeft leftPrefix |>.trans <|
        τSTr.parallelRight rightPrefix |>.trans <|
        τSTr.cons (.communicate leftVisible rightVisible hcomplementary) <|
        (τSTr.parallelLeft leftSuffix).trans
          (τSTr.parallelRight rightSuffix)

/-- Complementary rooted weak transitions synchronize to a rooted silent
transition of their parallel composition. -/
theorem rootedComplementary_parallel
    {left left' right right' : StaticProcess Name}
    {leftAction rightAction : Label Name}
    (hleft : Cslib.LTS.RootedWeakStep (lts := lts) left leftAction left')
    (hright : Cslib.LTS.RootedWeakStep (lts := lts) right rightAction right')
    (hcomplementary : leftAction.Complementary rightAction) :
    Cslib.LTS.RootedWeakStep (lts := lts) (.parallel left right) .tau
      (.parallel left' right') := by
  obtain ⟨leftBefore, leftAfter, leftPrefix, leftVisible, leftSuffix⟩ := hleft
  obtain ⟨rightBefore, rightAfter, rightPrefix, rightVisible, rightSuffix⟩ := hright
  exact ⟨.parallel leftBefore rightBefore, .parallel leftAfter rightAfter,
    (τSTr.parallelLeft leftPrefix).trans
      (τSTr.parallelRight rightPrefix),
    .communicate leftVisible rightVisible hcomplementary,
    (τSTr.parallelLeft leftSuffix).trans
      (τSTr.parallelRight rightSuffix)⟩

/-- Match one strong transition while preserving the parallel lifting. -/
private theorem parallelLift_matchStep
    {leftRel rightRel : StaticProcess Name → StaticProcess Name → Prop}
    (hleft : lts.saturate.IsHomSimulation leftRel)
    (hright : lts.saturate.IsHomSimulation rightRel)
    {source target next : StaticProcess Name} {action : Label Name}
    (hrel : ParallelLift leftRel rightRel source target)
    (hstep : lts.Tr source action next) :
    ∃ next', lts.STr target action next' ∧
      ParallelLift leftRel rightRel next next' := by
  cases hrel with
  | left hrel =>
      obtain ⟨next', hnext', hrel'⟩ := hleft hrel action next (STr.single hstep)
      exact ⟨next', hnext', .left hrel'⟩
  | right hrel =>
      obtain ⟨next', hnext', hrel'⟩ := hright hrel action next (STr.single hstep)
      exact ⟨next', hnext', .right hrel'⟩
  | parallel hleftRel hrightRel =>
      cases hstep with
      | parallelLeft step =>
          obtain ⟨next', hnext', hrel'⟩ := hleft hleftRel _ _ (STr.single step)
          exact ⟨.parallel next' _, STr.parallelLeft hnext',
            .parallel hrel' hrightRel⟩
      | parallelRight step =>
          obtain ⟨next', hnext', hrel'⟩ := hright hrightRel _ _ (STr.single step)
          exact ⟨.parallel _ next', STr.parallelRight hnext',
            .parallel hleftRel hrel'⟩
      | communicate leftStep rightStep complementary =>
          obtain ⟨left', hleft', hleftRel'⟩ := hleft hleftRel _ _ (STr.single leftStep)
          obtain ⟨right', hright', hrightRel'⟩ :=
            hright hrightRel _ _ (STr.single rightStep)
          exact ⟨.parallel left' right',
            (sTr_τSTr_iff _).mpr
              (weakComplementary_parallel hleft' hright' complementary),
            .parallel hleftRel' hrightRel'⟩

private theorem parallelLift_matchSilent
    {leftRel rightRel : StaticProcess Name → StaticProcess Name → Prop}
    (hleft : lts.saturate.IsHomSimulation leftRel)
    (hright : lts.saturate.IsHomSimulation rightRel)
    {source target next : StaticProcess Name}
    (hrel : ParallelLift leftRel rightRel source target)
    (hclosure : lts.τSTr source next) :
    ∃ next', lts.τSTr target next' ∧
      ParallelLift leftRel rightRel next next' := by
  induction hclosure using Relation.ReflTransGen.head_induction_on generalizing target with
  | refl => exact ⟨target, Relation.ReflTransGen.refl, hrel⟩
  | head step _ ih =>
      change lts.Tr _ .tau _ at step
      obtain ⟨middle, hmiddle, hrel'⟩ := parallelLift_matchStep hleft hright hrel step
      obtain ⟨next', htail, hrel''⟩ := ih hrel'
      exact ⟨next', ((sTr_τSTr_iff _).mp hmiddle).trans htail, hrel''⟩

/-- Weak simulation is preserved by the parallel relation lifting. -/
theorem parallelLift_isWeakSimulation
    {leftRel rightRel : StaticProcess Name → StaticProcess Name → Prop}
    (hleft : lts.saturate.IsHomSimulation leftRel)
    (hright : lts.saturate.IsHomSimulation rightRel) :
    lts.saturate.IsHomSimulation (ParallelLift leftRel rightRel) := by
  intro source target hrel action next hstep
  cases hstep with
  | refl => exact ⟨target, _root_.Cslib.LTS.STr.refl, hrel⟩
  | tr hprefix hmiddle hsuffix =>
      obtain ⟨before, hbefore, hrel₁⟩ := parallelLift_matchSilent hleft hright hrel hprefix
      obtain ⟨after, hafter, hrel₂⟩ := parallelLift_matchStep hleft hright hrel₁ hmiddle
      obtain ⟨next', hnext', hrel₃⟩ := parallelLift_matchSilent hleft hright hrel₂ hsuffix
      exact ⟨next',
        _root_.Cslib.LTS.STr.comp ((sTr_τSTr_iff _).mpr hbefore) hafter
          ((sTr_τSTr_iff _).mpr hnext'),
        hrel₃⟩

omit [DecidableEq Name] in
private theorem parallelLift_of_flip
    {leftRel rightRel : StaticProcess Name → StaticProcess Name → Prop}
    {source target : StaticProcess Name}
    (hrel : ParallelLift (Function.swap leftRel) (Function.swap rightRel) source target) :
    ParallelLift leftRel rightRel target source := by
  cases hrel with
  | left hrel => exact .left hrel
  | right hrel => exact .right hrel
  | parallel hleft hright => exact .parallel hleft hright

/-- Weak bisimulation is preserved by the parallel relation lifting. -/
theorem parallelLift_isWeakBisimulation
    {leftRel rightRel : StaticProcess Name → StaticProcess Name → Prop}
    (hleft : lts.IsHomWeakBisimulation leftRel)
    (hright : lts.IsHomWeakBisimulation rightRel) :
    lts.IsHomWeakBisimulation
      (ParallelLift leftRel rightRel) := by
  apply _root_.Cslib.LTS.IsBisimulation.isSimulation_iff.mpr
  constructor
  · exact parallelLift_isWeakSimulation hleft.isSimulation hright.isSimulation
  · intro target source hrel action next hstep
    have hrel' : ParallelLift (Function.swap leftRel) (Function.swap rightRel) target source := by
      cases hrel with
      | left h => exact .left h
      | right h => exact .right h
      | parallel hl hr => exact .parallel hl hr
    obtain ⟨next', hnext', hrel''⟩ :=
      parallelLift_isWeakSimulation hleft.flip_isSimulation hright.flip_isSimulation
        hrel' action next hstep
    exact ⟨next', hnext', parallelLift_of_flip hrel''⟩

/-- Parallel composition preserves weak bisimilarity componentwise. -/
theorem parallel_weaklyBisimilar_congr
    {left₁ left₂ right₁ right₂ : StaticProcess Name}
    (hleft : WeaklyBisimilar left₁ left₂)
    (hright : WeaklyBisimilar right₁ right₂) :
    WeaklyBisimilar (.parallel left₁ right₁) (.parallel left₂ right₂) := by
  obtain ⟨leftRel, hleftRel, hleftBisim⟩ := hleft
  obtain ⟨rightRel, hrightRel, hrightBisim⟩ := hright
  exact ⟨ParallelLift leftRel rightRel, .parallel hleftRel hrightRel,
    parallelLift_isWeakBisimulation hleftBisim hrightBisim⟩

/-- Rooted observational congruence is preserved componentwise by parallel
composition. -/
theorem parallel_observationCongruent_congr
    {left₁ left₂ right₁ right₂ : StaticProcess Name}
    (hleft : ObservationCongruent left₁ left₂)
    (hright : ObservationCongruent right₁ right₂) :
    ObservationCongruent (.parallel left₁ right₁) (.parallel left₂ right₂) := by
  constructor
  · intro action next hstep
    change Step (.parallel left₁ right₁) action next at hstep
    cases hstep with
    | parallelLeft step =>
        obtain ⟨left', hrooted, hnext⟩ := hleft.1 step
        exact ⟨.parallel left' right₂, RootedWeakStep.parallelLeft hrooted,
          parallel_weaklyBisimilar_congr hnext hright.to_homWeakBisimilarity⟩
    | parallelRight step =>
        obtain ⟨right', hrooted, hnext⟩ := hright.1 step
        exact ⟨.parallel left₂ right', RootedWeakStep.parallelRight hrooted,
          parallel_weaklyBisimilar_congr hleft.to_homWeakBisimilarity hnext⟩
    | communicate leftStep rightStep syncs =>
        obtain ⟨left', hleftRooted, hleftNext⟩ := hleft.1 leftStep
        obtain ⟨right', hrightRooted, hrightNext⟩ := hright.1 rightStep
        exact ⟨.parallel left' right',
          rootedComplementary_parallel hleftRooted hrightRooted syncs,
          parallel_weaklyBisimilar_congr hleftNext hrightNext⟩
  · intro action next hstep
    change Step (.parallel left₂ right₂) action next at hstep
    cases hstep with
    | parallelLeft step =>
        obtain ⟨left', hrooted, hnext⟩ := hleft.2 step
        exact ⟨.parallel left' right₁, RootedWeakStep.parallelLeft hrooted,
          parallel_weaklyBisimilar_congr hnext hright.to_homWeakBisimilarity⟩
    | parallelRight step =>
        obtain ⟨right', hrooted, hnext⟩ := hright.2 step
        exact ⟨.parallel left₁ right', RootedWeakStep.parallelRight hrooted,
          parallel_weaklyBisimilar_congr hleft.to_homWeakBisimilarity hnext⟩
    | communicate leftStep rightStep syncs =>
        obtain ⟨left', hleftRooted, hleftNext⟩ := hleft.2 leftStep
        obtain ⟨right', hrightRooted, hrightNext⟩ := hright.2 rightStep
        exact ⟨.parallel left' right',
          rootedComplementary_parallel hleftRooted hrightRooted syncs,
          parallel_weaklyBisimilar_congr hleftNext hrightNext⟩

end Cslib.CCS.StaticProcess
