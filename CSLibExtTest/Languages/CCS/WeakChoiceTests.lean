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

public import CSLibExt.Languages.CCS.WeakChoice

/-!
# Tests for weak CCS choice semantics

The examples distinguish ordinary weak bisimilarity from its rooted congruence
and exercise the congruence laws for prefix and choice.
-/

namespace CslibTest.CCS.WeakChoice

open Cslib.LTS
open Cslib.CCS Cslib.CCS.Process

inductive Action where
  | tau
  | a
  | b
  deriving DecidableEq

open Action

local instance : Cslib.HasTau Action := ⟨tau⟩

abbrev Proc := Process Action
abbrev system := lts (Action := Action)

def stopped : Proc := .nil
def aThenStop : Proc := .prefix a stopped
def delayedA : Proc := .prefix tau aThenStop
def bThenStop : Proc := .prefix b stopped

theorem aThenStop_no_tau {next : Proc} : ¬ Step aThenStop tau next := by
  intro hstep
  change Step (.prefix a stopped) tau next at hstep
  rw [prefix_step_iff] at hstep
  exact Action.noConfusion hstep.1

theorem bThenStop_no_tau {next : Proc} : ¬ Step bThenStop tau next := by
  intro hstep
  change Step (.prefix b stopped) tau next at hstep
  rw [prefix_step_iff] at hstep
  exact Action.noConfusion hstep.1

theorem choice_no_tau {next : Proc} :
    ¬ Step (.choice aThenStop bThenStop) tau next := by
  intro hstep
  rw [choice_step_iff] at hstep
  exact hstep.elim aThenStop_no_tau bThenStop_no_tau

theorem silentClosure_eq_of_no_tau {source target : Proc}
    (hno : ∀ next, ¬ Step source tau next)
    (hclosure : system.τSTr source target) : target = source := by
  induction hclosure using Relation.ReflTransGen.head_induction_on with
  | refl => rfl
  | head hstep _ _ => exact (hno _ hstep).elim

theorem aThenStop_not_weak_b {target : Proc} :
    ¬ system.STr aThenStop b target := by
  intro hstep
  cases hstep with
  | tr hprefix hvisible _ =>
    have hbefore := silentClosure_eq_of_no_tau (fun next => aThenStop_no_tau) hprefix
    rw [hbefore] at hvisible
    change Step (.prefix a stopped) b _ at hvisible
    rw [prefix_step_iff] at hvisible
    exact Action.noConfusion hvisible.1

example : system.HomWeakBisimilarity delayedA aThenStop := by
  exact tau_prefix_weaklyBisimilar aThenStop

example : ObservationCongruent (.prefix a delayedA) (.prefix a aThenStop) := by
  exact prefix_observationCongruent a (tau_prefix_weaklyBisimilar aThenStop)

example : ObservationCongruent
    (.choice (.prefix a delayedA) bThenStop)
    (.choice (.prefix a aThenStop) bThenStop) := by
  apply choice_observationCongruent
  · exact prefix_observationCongruent a (tau_prefix_weaklyBisimilar aThenStop)
  · exact observationCongruent_refl bThenStop

example : ObservationCongruent
    (.choice aThenStop bThenStop) (.choice bThenStop aThenStop) := by
  exact choice_comm_observationCongruent aThenStop bThenStop

example : ObservationCongruent
    (.choice (.choice aThenStop bThenStop) stopped)
    (.choice aThenStop (.choice bThenStop stopped)) := by
  exact choice_assoc_observationCongruent aThenStop bThenStop stopped

example : ObservationCongruent (.choice aThenStop aThenStop) aThenStop := by
  exact choice_idem_observationCongruent aThenStop

example : ObservationCongruent (.choice stopped aThenStop) aThenStop := by
  exact choice_nil_left_observationCongruent aThenStop

example {left middle right : Proc}
    (hleft : ObservationCongruent left middle)
    (hright : ObservationCongruent middle right) :
    ObservationCongruent left right :=
  hleft.trans hright

/-- Silent-prefix elimination is not rooted: the prefixed process has an
initial silent transition, while the visible-prefix process cannot match it by
a rooted silent transition. -/
theorem delayedA_not_observationCongruent :
    ¬ ObservationCongruent delayedA aThenStop := by
  intro hcongr
  have hstep : Step delayedA tau aThenStop := .prefix _ _
  obtain ⟨target, hrooted, _⟩ := hcongr.1 hstep
  obtain ⟨before, after, hprefix, hmiddle, _⟩ := hrooted
  have hbefore := silentClosure_eq_of_no_tau (fun next => aThenStop_no_tau) hprefix
  subst before
  exact aThenStop_no_tau hmiddle

/-- Consequently, ordinary weak bisimilarity is not preserved by adding the
same choice context. -/
theorem weak_bisimilarity_not_choice_congruence :
    ¬ system.HomWeakBisimilarity
      (.choice delayedA bThenStop) (.choice aThenStop bThenStop) := by
  intro hbisim
  have htau : Step (.choice delayedA bThenStop) tau aThenStop :=
    .choiceLeft (.prefix _ _)
  obtain ⟨right', hright', hnext⟩ :=
    hbisim.tr htau
  replace hright' := (Cslib.LTS.sTr_τSTr_iff system).mp hright'
  have hright := silentClosure_eq_of_no_tau (fun next => choice_no_tau) hright'
  subst right'
  have hbEnabled : system.saturate.HasOutLabel (.choice aThenStop bThenStop) b :=
    ⟨stopped, STr.single (.choiceRight (.prefix _ _))⟩
  have henabled :=
    (HomWeakBisimilarity.hasOutLabel_saturate_iff hnext b).mpr hbEnabled
  obtain ⟨target, hweak⟩ := henabled
  exact aThenStop_not_weak_b hweak

end CslibTest.CCS.WeakChoice
