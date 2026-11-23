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

module

public import CSLibExt.Foundations.Semantics.LTS.WeakBisimulation

@[expose] public section

/-!
# Client tests for weak bisimulation

These examples exercise silent closure, weak visible transitions, the embedding
of strong bisimilarity, and a genuinely weak equivalence that is not a strong
bisimilarity.
-/

namespace Cslib.LTS.WeakBisimulationTests

open Cslib.LTS

inductive Label where
  | tau
  | visible
  deriving DecidableEq

inductive State where
  | delayed
  | ready
  | direct
  | done
  deriving DecidableEq

open Label State

local instance : Cslib.HasTau Label := ⟨tau⟩

/-- `delayed` silently becomes `ready`, which performs the same visible action
as `direct`. -/
inductive Step : State → Label → State → Prop
  | delay : Step delayed tau ready
  | readyVisible : Step ready visible done
  | directVisible : Step direct visible done

def exampleLTS : _root_.Cslib.LTS State Label := ⟨Step⟩

example : exampleLTS.τSTr delayed ready :=
  τSTr.cons .delay τSTr.refl

example : exampleLTS.STr delayed visible done := by
  exact _root_.Cslib.LTS.STr.tr
    (τSTr.cons .delay τSTr.refl) .readyVisible τSTr.refl

example : exampleLTS.STr delayed tau delayed :=
  STr.refl

/-- The relation witnessing that a silent delay is observationally invisible. -/
inductive DelayRelation : State → State → Prop
  | initial : DelayRelation delayed direct
  | ready : DelayRelation ready direct
  | done : DelayRelation done done

theorem delayRelation_isWeakBisimulation :
    IsWeakBisimulation exampleLTS exampleLTS DelayRelation := by
  apply _root_.Cslib.LTS.IsSWBisimulation.isWeakBisimulation
  intro left right hrel label
  constructor
  · intro left' hstep
    cases hrel with
    | initial =>
        cases hstep
        exact ⟨direct, STr.refl, .ready⟩
    | ready =>
        cases hstep
        exact ⟨done, STr.single .directVisible, .done⟩
    | done => cases hstep
  · intro right' hstep
    cases hrel with
    | initial =>
        cases hstep
        exact ⟨done,
          _root_.Cslib.LTS.STr.tr
            (τSTr.cons .delay τSTr.refl) .readyVisible
            τSTr.refl,
          .done⟩
    | ready =>
        cases hstep
        exact ⟨done, STr.single .readyVisible, .done⟩
    | done => cases hstep

theorem delayed_weaklyBisimilar_direct :
    HomWeakBisimilarity exampleLTS delayed direct :=
  ⟨DelayRelation, .initial, delayRelation_isWeakBisimulation⟩

example : exampleLTS.saturate.HasOutLabel delayed visible := by
  exact ⟨done, _root_.Cslib.LTS.STr.tr
    (τSTr.cons .delay τSTr.refl) .readyVisible τSTr.refl⟩

example : exampleLTS.saturate.outgoingLabels delayed =
    exampleLTS.saturate.outgoingLabels direct :=
  delayed_weaklyBisimilar_direct.outgoingLabels_saturate_eq

example : exampleLTS.saturate.MTr delayed [visible] done := by
  exact _root_.Cslib.LTS.MTr.stepL
    (_root_.Cslib.LTS.STr.tr
      (τSTr.cons .delay τSTr.refl) .readyVisible τSTr.refl)
    _root_.Cslib.LTS.MTr.refl

example : HomWeakBisimilarity exampleLTS done done :=
  HomWeakBisimilarity.refl done

example (left middle right : State)
    (hleft : HomWeakBisimilarity exampleLTS left middle)
    (hright : HomWeakBisimilarity exampleLTS middle right) :
    HomWeakBisimilarity exampleLTS left right :=
  hleft.trans hright

example {left right : State} (h : exampleLTS.HomBisimilarity left right) :
    HomWeakBisimilarity exampleLTS left right :=
  HomBisimilarity.to_homWeakBisimilarity h

/-- The delayed and direct states are not strongly bisimilar: the direct state
cannot match the initial silent transition. -/
theorem delayed_not_bisimilar_direct :
    ¬exampleLTS.HomBisimilarity delayed direct := by
  rintro ⟨relation, hrel, hbisim⟩
  obtain ⟨next, hstep, _⟩ := hbisim.follow_fst hrel Step.delay
  cases hstep

end Cslib.LTS.WeakBisimulationTests
