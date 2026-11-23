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
# Weak equivalence for CCS parallel composition
-/
module

public import CSLibExt.Foundations.Semantics.LTS.ObservationCongruence
public import CSLibExt.Languages.CCS.Parallel

/-!
# Weak equivalence for communicating parallel processes

This module lifts silent closures and weak transitions through parallel
contexts.  Its central construction shows how two complementary weak
transitions synchronize to a silent closure of their parallel composition.
That construction yields congruence of weak bisimilarity for CCS parallel
composition.

The development follows Robin Milner, *Communication and Concurrency*,
Prentice Hall, 1989, Chapter 5 (ISBN 978-0-13-115007-2).
-/

@[expose] public section

namespace Cslib.CCS.Process

open Cslib.LTS

variable {Name : Type*} [DecidableEq Name]

/-- Silent reductions of the left component lift through a fixed parallel
context. -/
theorem τSTr.parallelLeft {left left' right : Process (Label Name)}
    (hclosure : (communicationLTS (Name := Name)).τSTr left left') :
    (communicationLTS (Name := Name)).τSTr
      (.parallel left right) (.parallel left' right) := by
  induction hclosure using Relation.ReflTransGen.head_induction_on with
  | refl => exact .refl
  | head step _ ih => exact τSTr.cons (.parallelLeft step) ih

/-- Silent reductions of the right component lift through a fixed parallel
context. -/
theorem τSTr.parallelRight {left right right' : Process (Label Name)}
    (hclosure : (communicationLTS (Name := Name)).τSTr right right') :
    (communicationLTS (Name := Name)).τSTr
      (.parallel left right) (.parallel left right') := by
  induction hclosure using Relation.ReflTransGen.head_induction_on with
  | refl => exact .refl
  | head step _ ih => exact τSTr.cons (.parallelRight step) ih

/-- A weak transition of the left component lifts through parallel
composition. -/
theorem STr.parallelLeft {left left' right : Process (Label Name)}
    {label : Label Name}
    (hstep : (communicationLTS (Name := Name)).STr left label left') :
    (communicationLTS (Name := Name)).STr
      (.parallel left right) label (.parallel left' right) := by
  cases hstep with
  | refl => exact _root_.Cslib.LTS.STr.refl
  | tr hprefix hvis hsuffix =>
      exact _root_.Cslib.LTS.STr.tr (τSTr.parallelLeft hprefix)
        (.parallelLeft hvis) (τSTr.parallelLeft hsuffix)

/-- A weak transition of the right component lifts through parallel
composition. -/
theorem STr.parallelRight {left right right' : Process (Label Name)}
    {label : Label Name}
    (hstep : (communicationLTS (Name := Name)).STr right label right') :
    (communicationLTS (Name := Name)).STr
      (.parallel left right) label (.parallel left right') := by
  cases hstep with
  | refl => exact _root_.Cslib.LTS.STr.refl
  | tr hprefix hvis hsuffix =>
      exact _root_.Cslib.LTS.STr.tr (τSTr.parallelRight hprefix)
        (.parallelRight hvis) (τSTr.parallelRight hsuffix)

/-- A rooted weak transition of the left component lifts through a fixed
parallel context. -/
theorem RootedWeakStep.parallelLeft {left left' right : Process (Label Name)}
    {label : Label Name}
    (hstep : Cslib.LTS.RootedWeakStep
      (lts := communicationLTS (Name := Name)) left label left') :
    Cslib.LTS.RootedWeakStep (lts := (communicationLTS (Name := Name)))
      (.parallel left right) label (.parallel left' right) := by
  obtain ⟨before, after, hprefix, hmiddle, hsuffix⟩ := hstep
  exact ⟨.parallel before right, .parallel after right,
    τSTr.parallelLeft hprefix, .parallelLeft hmiddle,
    τSTr.parallelLeft hsuffix⟩

/-- A rooted weak transition of the right component lifts through a fixed
parallel context. -/
theorem RootedWeakStep.parallelRight {left right right' : Process (Label Name)}
    {label : Label Name}
    (hstep : Cslib.LTS.RootedWeakStep
      (lts := communicationLTS (Name := Name)) right label right') :
    Cslib.LTS.RootedWeakStep (lts := (communicationLTS (Name := Name)))
      (.parallel left right) label (.parallel left right') := by
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
    (h : left.Complementary right) : right ≠ .tau := by
  exact complementary_ne_tau_left (Label.complementary_symm h)

/-- Complementary weak transitions of two components synchronize to a silent
closure of their parallel composition.  Silent preparation and cleanup on
both sides are interleaved around the single communication step. -/
theorem weakComplementary_parallel
    {left left' right right' : Process (Label Name)}
    {leftLabel rightLabel : Label Name}
    (hleft : (communicationLTS (Name := Name)).STr left leftLabel left')
    (hright : (communicationLTS (Name := Name)).STr right rightLabel right')
    (hcomplementary : leftLabel.Complementary rightLabel) :
    (communicationLTS (Name := Name)).τSTr
      (.parallel left right) (.parallel left' right') := by
  cases hleft with
  | refl => exact (complementary_ne_tau_left hcomplementary rfl).elim
  | tr leftPrefix leftVisible leftSuffix =>
    cases hright with
    | refl => exact (complementary_ne_tau_right hcomplementary rfl).elim
    | tr rightPrefix rightVisible rightSuffix =>
      exact τSTr.parallelLeft leftPrefix |>.trans <|
        τSTr.parallelRight rightPrefix |>.trans <|
        τSTr.cons (.communicate leftVisible rightVisible
          (Label.synchronize_eq_some_iff.mpr ⟨rfl, hcomplementary⟩)) <|
        (τSTr.parallelLeft leftSuffix).trans
          (τSTr.parallelRight rightSuffix)

/-- Complementary rooted weak transitions synchronize to a rooted silent
transition of their parallel composition.  Unlike the weak version, the
result records the actual communication step and cannot collapse to an empty
silent closure. -/
theorem rootedComplementary_parallel
    {left left' right right' : Process (Label Name)}
    {leftLabel rightLabel : Label Name}
    (hleft : Cslib.LTS.RootedWeakStep (lts := (communicationLTS (Name := Name)))
      left leftLabel left')
    (hright : Cslib.LTS.RootedWeakStep (lts := (communicationLTS (Name := Name)))
      right rightLabel right')
    (hcomplementary : leftLabel.Complementary rightLabel) :
    Cslib.LTS.RootedWeakStep (lts := (communicationLTS (Name := Name)))
      (.parallel left right) .tau (.parallel left' right') := by
  obtain ⟨leftBefore, leftAfter, leftPrefix, leftVisible, leftSuffix⟩ := hleft
  obtain ⟨rightBefore, rightAfter, rightPrefix, rightVisible, rightSuffix⟩ := hright
  exact ⟨.parallel leftBefore rightBefore, .parallel leftAfter rightAfter,
    (τSTr.parallelLeft leftPrefix).trans
      (τSTr.parallelRight rightPrefix),
    .communicate leftVisible rightVisible
      (Label.synchronize_eq_some_iff.mpr ⟨rfl, hcomplementary⟩),
    (τSTr.parallelLeft leftSuffix).trans
      (τSTr.parallelRight rightSuffix)⟩

/-- Match one strong transition while preserving the parallel lifting. -/
private theorem parallelLift_matchStep
    {leftRel rightRel : Process (Label Name) → Process (Label Name) → Prop}
    (hleft : (communicationLTS (Name := Name)).saturate.IsHomSimulation leftRel)
    (hright : (communicationLTS (Name := Name)).saturate.IsHomSimulation rightRel)
    {source target next : Process (Label Name)} {label : Label Name}
    (hrel : ParallelLift leftRel rightRel source target)
    (hstep : (communicationLTS (Name := Name)).Tr source label next) :
    ∃ next', (communicationLTS (Name := Name)).STr target label next' ∧
      ParallelLift leftRel rightRel next next' := by
  cases hrel with
  | left hrel =>
      obtain ⟨next', hnext', hrel'⟩ := hleft hrel label next (STr.single hstep)
      exact ⟨next', hnext', .left hrel'⟩
  | right hrel =>
      obtain ⟨next', hnext', hrel'⟩ := hright hrel label next (STr.single hstep)
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
      | communicate leftStep rightStep syncs =>
          obtain ⟨rfl, complementary⟩ := Label.synchronize_eq_some_iff.mp syncs
          obtain ⟨left', hleft', hleftRel'⟩ := hleft hleftRel _ _ (STr.single leftStep)
          obtain ⟨right', hright', hrightRel'⟩ :=
            hright hrightRel _ _ (STr.single rightStep)
          exact ⟨.parallel left' right',
            (sTr_τSTr_iff _).mpr
              (weakComplementary_parallel hleft' hright' complementary),
            .parallel hleftRel' hrightRel'⟩

/-- Match a silent closure while preserving the parallel lifting. -/
private theorem parallelLift_matchSilent
    {leftRel rightRel : Process (Label Name) → Process (Label Name) → Prop}
    (hleft : (communicationLTS (Name := Name)).saturate.IsHomSimulation leftRel)
    (hright : (communicationLTS (Name := Name)).saturate.IsHomSimulation rightRel)
    {source target next : Process (Label Name)}
    (hrel : ParallelLift leftRel rightRel source target)
    (hclosure : (communicationLTS (Name := Name)).τSTr source next) :
    ∃ next', (communicationLTS (Name := Name)).τSTr target next' ∧
      ParallelLift leftRel rightRel next next' := by
  induction hclosure using Relation.ReflTransGen.head_induction_on generalizing target with
  | refl => exact ⟨target, Relation.ReflTransGen.refl, hrel⟩
  | head step _ ih =>
      change (communicationLTS (Name := Name)).Tr _ .tau _ at step
      obtain ⟨middle, hmiddle, hrel'⟩ := parallelLift_matchStep hleft hright hrel step
      obtain ⟨next', htail, hrel''⟩ := ih hrel'
      exact ⟨next', ((sTr_τSTr_iff _).mp hmiddle).trans htail, hrel''⟩

/-- Weak simulation is preserved by the parallel relation lifting. -/
theorem parallelLift_isWeakSimulation
    {leftRel rightRel : Process (Label Name) → Process (Label Name) → Prop}
    (hleft : (communicationLTS (Name := Name)).saturate.IsHomSimulation leftRel)
    (hright : (communicationLTS (Name := Name)).saturate.IsHomSimulation rightRel) :
    (communicationLTS (Name := Name)).saturate.IsHomSimulation
      (ParallelLift leftRel rightRel) := by
  intro source target hrel label next hstep
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
/-- Reverse a parallel lift whose component relations have been flipped. -/
private theorem parallelLift_of_flip
    {leftRel rightRel : Process (Label Name) → Process (Label Name) → Prop}
    {source target : Process (Label Name)}
    (hrel : ParallelLift (Function.swap leftRel) (Function.swap rightRel) source target) :
    ParallelLift leftRel rightRel target source := by
  cases hrel with
  | left hrel => exact .left hrel
  | right hrel => exact .right hrel
  | parallel hleft hright => exact .parallel hleft hright

/-- Weak bisimulation is preserved by the parallel relation lifting. -/
theorem parallelLift_isWeakBisimulation
    {leftRel rightRel : Process (Label Name) → Process (Label Name) → Prop}
    (hleft : (communicationLTS (Name := Name)).IsHomWeakBisimulation leftRel)
    (hright : (communicationLTS (Name := Name)).IsHomWeakBisimulation rightRel) :
    (communicationLTS (Name := Name)).IsHomWeakBisimulation
      (ParallelLift leftRel rightRel) := by
  apply _root_.Cslib.LTS.IsBisimulation.isSimulation_iff.mpr
  constructor
  · exact parallelLift_isWeakSimulation hleft.isSimulation hright.isSimulation
  · intro target source hrel label next hstep
    have hrel' : ParallelLift (Function.swap leftRel) (Function.swap rightRel) target source := by
      cases hrel with
      | left h => exact .left h
      | right h => exact .right h
      | parallel hl hr => exact .parallel hl hr
    obtain ⟨next', hnext', hrel''⟩ :=
      parallelLift_isWeakSimulation hleft.flip_isSimulation hright.flip_isSimulation
        hrel' label next hstep
    exact ⟨next', hnext', parallelLift_of_flip hrel''⟩

/-- Parallel composition preserves weak bisimilarity componentwise. -/
theorem parallel_weaklyBisimilar_congr
    {left₁ left₂ right₁ right₂ : Process (Label Name)}
    (hleft : (communicationLTS (Name := Name)).HomWeakBisimilarity left₁ left₂)
    (hright : (communicationLTS (Name := Name)).HomWeakBisimilarity right₁ right₂) :
    (communicationLTS (Name := Name)).HomWeakBisimilarity
      (.parallel left₁ right₁) (.parallel left₂ right₂) := by
  obtain ⟨leftRel, hleftRel, hleftBisim⟩ := hleft
  obtain ⟨rightRel, hrightRel, hrightBisim⟩ := hright
  exact ⟨ParallelLift leftRel rightRel, .parallel hleftRel hrightRel,
    parallelLift_isWeakBisimulation hleftBisim hrightBisim⟩

/-- Rooted weak bisimilarity is preserved componentwise by communicating
parallel composition.  The communication cases use rooted matches from both
components, so the synchronizing silent action remains observable at the
root. -/
theorem parallel_rootedWeaklyBisimilar_congr
    {left₁ left₂ right₁ right₂ : Process (Label Name)}
    (hleft : Cslib.LTS.RootedWeaklyBisimilar
      (lts := communicationLTS (Name := Name)) left₁ left₂)
    (hright : Cslib.LTS.RootedWeaklyBisimilar
      (lts := communicationLTS (Name := Name)) right₁ right₂) :
    Cslib.LTS.RootedWeaklyBisimilar (lts := (communicationLTS (Name := Name)))
      (.parallel left₁ right₁) (.parallel left₂ right₂) := by
  constructor
  · intro label next hstep
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
        obtain ⟨rfl, complementary⟩ := Label.synchronize_eq_some_iff.mp syncs
        obtain ⟨left', hleftRooted, hleftNext⟩ := hleft.1 leftStep
        obtain ⟨right', hrightRooted, hrightNext⟩ := hright.1 rightStep
        exact ⟨.parallel left' right',
          rootedComplementary_parallel hleftRooted hrightRooted complementary,
          parallel_weaklyBisimilar_congr hleftNext hrightNext⟩
  · intro label next hstep
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
        obtain ⟨rfl, complementary⟩ := Label.synchronize_eq_some_iff.mp syncs
        obtain ⟨left', hleftRooted, hleftNext⟩ := hleft.2 leftStep
        obtain ⟨right', hrightRooted, hrightNext⟩ := hright.2 rightStep
        exact ⟨.parallel left' right',
          rootedComplementary_parallel hleftRooted hrightRooted complementary,
          parallel_weaklyBisimilar_congr hleftNext hrightNext⟩

/-- Commutativity of parallel composition at the weak-equivalence level. -/
theorem parallel_comm_weaklyBisimilar (left right : Process (Label Name)) :
    (communicationLTS (Name := Name)).HomWeakBisimilarity
      (.parallel left right) (.parallel right left) :=
  HomBisimilarity.to_homWeakBisimilarity
    (parallel_comm left right)

/-- The terminated process is a left identity for parallel composition under
weak bisimilarity. -/
theorem parallel_nil_left_weaklyBisimilar (process : Process (Label Name)) :
    (communicationLTS (Name := Name)).HomWeakBisimilarity
      (.parallel .nil process) process :=
  HomBisimilarity.to_homWeakBisimilarity
    (parallel_nil_left process)

/-- The terminated process is a right identity for parallel composition under
weak bisimilarity. -/
theorem parallel_nil_right_weaklyBisimilar (process : Process (Label Name)) :
    (communicationLTS (Name := Name)).HomWeakBisimilarity
      (.parallel process .nil) process :=
  HomBisimilarity.to_homWeakBisimilarity
    (parallel_nil_right process)

end Cslib.CCS.Process
