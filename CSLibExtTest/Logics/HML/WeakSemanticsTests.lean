/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Ported from fairinternal/formal-math at `110ea10c9842e17ce0f7478a72b3abe4346ddab1`.
Original formalization by Zeina Migeed (@migeed-z); ported with permission.
-/

module

public import CSLibExt.Logics.HML.WeakSemantics

/-!
# Tests for weak observation logic

These tests use a small transition system in which one process delays a visible
action by a silent step.  They exercise formula semantics, weak-bisimulation
invariance, and finite-depth approximants.
-/

namespace CslibTest.Logics.HML.WeakSemantics

open Cslib.Semantics LTS ObservationFormula

inductive State where
  | delayed
  | ready
  | direct
  | done
  | blocked
  deriving DecidableEq

inductive Label where
  | tau
  | visible
  | blocked
  deriving DecidableEq

open State Label

local instance : Cslib.HasTau Label := ⟨tau⟩

inductive Step : State → Label → State → Prop
  | delay : Step delayed tau ready
  | readyVisible : Step ready visible done
  | directVisible : Step direct visible done
  | blockedStep : Step blocked Label.blocked done

def system : Cslib.LTS State Label := ⟨Step⟩

inductive DelayedDirect : State → State → Prop
  | initial : DelayedDirect delayed direct
  | readyPair : DelayedDirect ready direct
  | donePair : DelayedDirect done done

theorem delayedDirect_isWeakBisimulation :
    system.IsHomWeakBisimulation DelayedDirect := by
  apply _root_.Cslib.LTS.IsSWBisimulation.isWeakBisimulation
  intro left right hrel label
  constructor
  · intro next hstep
    cases hrel with
    | initial =>
        cases hstep
        exact ⟨direct, _root_.Cslib.LTS.STr.refl, .readyPair⟩
    | readyPair =>
        cases hstep
        exact ⟨done, _root_.Cslib.LTS.STr.single .directVisible, .donePair⟩
    | donePair => cases hstep
  · intro next hstep
    cases hrel with
    | initial =>
        cases hstep
        exact ⟨done,
          _root_.Cslib.LTS.STr.tr
            (Relation.ReflTransGen.head .delay _root_.Cslib.LTS.τSTr.refl)
            .readyVisible _root_.Cslib.LTS.τSTr.refl,
          .donePair⟩
    | readyPair =>
        cases hstep
        exact ⟨done, _root_.Cslib.LTS.STr.single .readyVisible, .donePair⟩
    | donePair => cases hstep

theorem delayed_weaklyBisimilar_direct :
    system.HomWeakBisimilarity delayed direct :=
  ⟨DelayedDirect, .initial, delayedDirect_isWeakBisimulation⟩

theorem ready_no_tau {next : State} : ¬ Step ready tau next := by
  intro hstep
  cases hstep

theorem direct_no_tau {next : State} : ¬ Step direct tau next := by
  intro hstep
  cases hstep

theorem blocked_no_tau {next : State} : ¬ Step blocked tau next := by
  intro hstep
  cases hstep

theorem silentClosure_eq_of_no_tau {source target : State}
    (hno : ∀ next, ¬ Step source tau next)
    (hclosure : system.τSTr source target) : target = source := by
  induction hclosure using Relation.ReflTransGen.head_induction_on with
  | refl => rfl
  | head hstep _ _ => exact (hno _ hstep).elim

theorem delayedWeakVisible : system.STr delayed visible done :=
  _root_.Cslib.LTS.STr.tr
    (Relation.ReflTransGen.head .delay _root_.Cslib.LTS.τSTr.refl)
    .readyVisible _root_.Cslib.LTS.τSTr.refl

/-- Split a weak step with a visible label whose silent prefix must be
trivial: the silent prefix is empty, the middle step carries the label, and
the suffix is an ordinary weak step. -/
private theorem str_split_of_ne {s t : State} {μ : Label} (hne : μ ≠ tau)
    (h : system.STr s μ t) :
    ∃ before after, system.τSTr s before ∧ system.Tr before μ after ∧
      system.τSTr after t := by
  cases h with
  | refl => exact absurd rfl hne
  | tr hprefix hmiddle hsuffix => exact ⟨_, _, hprefix, hmiddle, hsuffix⟩

theorem delayed_not_weak_blocked {next : State} :
    ¬ system.STr delayed Label.blocked next := by
  intro hstep
  obtain ⟨before, after, hprefix, hmiddle, _⟩ :=
    str_split_of_ne (by decide : Label.blocked ≠ tau) hstep
  cases hprefix with
  | refl => cases hmiddle
  | tail _ hlast =>
      cases hlast
      cases hmiddle

theorem direct_not_weak_blocked {next : State} :
    ¬ system.STr direct Label.blocked next := by
  intro hstep
  obtain ⟨before, after, hprefix, hmiddle, _⟩ :=
    str_split_of_ne (by decide : Label.blocked ≠ tau) hstep
  have hbefore := silentClosure_eq_of_no_tau (fun target => direct_no_tau) hprefix
  subst before
  cases hmiddle

def canFinish : ObservationFormula Label := .diamond visible .top

def cannotBlock : ObservationFormula Label := .box Label.blocked .bottom

def useful : ObservationFormula Label := .conj canFinish cannotBlock

example : Satisfies system delayed canFinish := by
  exact ⟨done, delayedWeakVisible, trivial⟩

example : Satisfies system direct canFinish := by
  exact ⟨done, _root_.Cslib.LTS.STr.single .directVisible, trivial⟩

/-- After unfolding the formula abbreviation, `rw` applies the historical
compatibility theorem directly. -/
example : Satisfies system delayed cannotBlock := by
  unfold cannotBlock
  rw [satisfies_box_iff]
  intro next hstep
  exact (delayed_not_weak_blocked hstep).elim

example : Satisfies system delayed useful :=
  ⟨by exact ⟨done, delayedWeakVisible, trivial⟩,
    by
      unfold cannotBlock
      rw [satisfies_box_iff]
      intro next hstep
      exact (delayed_not_weak_blocked hstep).elim⟩

example : LogicallyEquivalent (lts := system) delayed direct :=
  Cslib.Semantics.LTS.HomWeakBisimilarity.logicallyEquivalent
    delayed_weaklyBisimilar_direct

example (formula : ObservationFormula Label) :
    Satisfies system delayed formula ↔
      Satisfies system direct formula :=
  Cslib.Semantics.LTS.HomWeakBisimilarity.satisfies_iff
    delayed_weaklyBisimilar_direct formula

example (depth : Nat) :
    WeakApproximation system depth delayed direct :=
  Cslib.Semantics.LTS.HomWeakBisimilarity.weakApproximation
    delayed_weaklyBisimilar_direct depth

example : WeakApproximation system 1 delayed direct := by
  exact Cslib.Semantics.LTS.HomWeakBisimilarity.weakApproximation
    delayed_weaklyBisimilar_direct 1

example : WeakApproximation system 0 delayed blocked := by
  trivial

example : ¬ WeakApproximation system 1 delayed blocked := by
  intro happrox
  have hvis : system.STr delayed visible done := delayedWeakVisible
  obtain ⟨next, hblocked, hnext⟩ := happrox.1 hvis
  obtain ⟨before, after, hprefix, hmiddle, _⟩ :=
    str_split_of_ne (by decide : Label.visible ≠ tau) hblocked
  have hbefore := silentClosure_eq_of_no_tau (fun target => blocked_no_tau) hprefix
  subst before
  cases hmiddle

example : canFinish.modalDepth = 1 := rfl

example : useful.modalDepth = 1 := rfl

example {left right : State}
    (happrox : WeakApproximation system 1 left right) :
    Satisfies system left canFinish ↔
      Satisfies system right canFinish :=
  happrox.satisfies_iff canFinish (by decide)

example : Satisfies system direct
    (.conjunction [canFinish, cannotBlock]) := by
  rw [satisfies_conjunction_iff]
  intro formula hmem
  simp at hmem
  rcases hmem with rfl | rfl
  · exact ⟨done, _root_.Cslib.LTS.STr.single .directVisible, trivial⟩
  · unfold cannotBlock
    rw [satisfies_box_iff]
    intro next hstep
    exact (direct_not_weak_blocked hstep).elim

section CslibBridge

/-- In canonical CSLib HML over the saturated system, `delayed` can finish: the silent prefix
before the visible step is absorbed by saturation. -/
example : Cslib.Logic.Modal.Satisfies (satModel system).toModal delayed canFinish.tr :=
  (satisfies_iff system canFinish delayed).1
    ⟨done, delayedWeakVisible, trivial⟩

/-- In canonical CSLib HML over the saturated system, `delayed` cannot perform `blocked`. -/
example : ¬ Cslib.Logic.Modal.Satisfies (satModel system).toModal delayed
    (ObservationFormula.diamond Label.blocked .top).tr := fun h => by
  obtain ⟨next, hstep, -⟩ := (satisfies_iff system _ delayed).2 h
  exact delayed_not_weak_blocked hstep

/-- The weakly bisimilar states `delayed` and `direct` agree on every translated formula in
canonical CSLib HML over the saturated system. -/
example (formula : ObservationFormula Label) :
    Cslib.Logic.Modal.Satisfies (satModel system).toModal delayed formula.tr ↔
      Cslib.Logic.Modal.Satisfies (satModel system).toModal direct formula.tr := by
  rw [← satisfies_iff system, ← satisfies_iff system]
  exact Cslib.Semantics.LTS.HomWeakBisimilarity.satisfies_iff
    delayed_weaklyBisimilar_direct formula

/-- Observations agree with their translations in the alignment-free weak-step
model (the bridge construction, exercised here through the shared `tr` translation). -/
example (s : State) (φ : ObservationFormula Label) :
    Satisfies system s φ ↔
      Cslib.Logic.Modal.Satisfies (toWeakHMLModel system).toModal s φ.tr :=
  satisfies_iff_toWeakHMLModel system s φ

/-- `done` satisfies `⟨tau⟩⊤` in the alignment-free model: the silent reflexive
closure needs no steps. -/
example : Cslib.Logic.Modal.Satisfies (toWeakHMLModel system).toModal done
    ((.diamond tau .top) : ObservationFormula Label).tr :=
  (satisfies_iff_toWeakHMLModel _ _ _).mp
    ⟨done, _root_.Cslib.LTS.STr.refl, trivial⟩

/-- `delayed` satisfies `⟨visible⟩⊤ ∧ ¬⊥` in the alignment-free model: the silent
prefix is absorbed by the weak-step frame, with no saturation involved. -/
example : Cslib.Logic.Modal.Satisfies (toWeakHMLModel system).toModal delayed
    ((.conj (.diamond visible .top) (.neg .bottom)) : ObservationFormula Label).tr := by
  apply (satisfies_iff_toWeakHMLModel _ _ _).mp
  refine ⟨⟨done, ?_, trivial⟩, not_satisfies_bottom delayed⟩
  exact delayedWeakVisible

end CslibBridge

end CslibTest.Logics.HML.WeakSemantics
