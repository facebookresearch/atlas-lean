/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Ported from fairinternal/formal-math at `290c48922e071d1e4267dd103a14e73b547adf60`.
Original formalization by Zeina Migeed (@migeed-z); ported with permission.
-/

/-
# CCS restriction and relabelling
-/
module

public import CSLibExt.Languages.CCS.Parallel

/-!
# CCS restriction and relabelling

This module extends the finite CCS language with the static operators of
restriction and relabelling.  Restrictions are finite lists of channel names,
and relabellings are finite tables with identity as the default.  This syntax
keeps equality decidable while making the CCS invariants structural: silent
actions cannot be restricted or renamed, and inputs and outputs are renamed
in complementary pairs.

The presentation follows Robin Milner, *Communication and Concurrency*,
Prentice Hall, 1989, Chapters 2--3 (ISBN 978-0-13-115007-2).
-/

@[expose] public section

namespace Cslib.CCS

/-- A visible CCS label, excluding the silent action. -/
inductive VisibleLabel (Name : Type*) where
  | input (name : Name)
  | output (name : Name)
  deriving DecidableEq

namespace VisibleLabel

variable {Name : Type*}

/-- Reverse the polarity of a visible label. -/
def complement : VisibleLabel Name → VisibleLabel Name
  | .input name => .output name
  | .output name => .input name

/-- Include a visible label into the full CCS label type. -/
def toLabel : VisibleLabel Name → Label Name
  | .input name => .input name
  | .output name => .output name

@[simp] theorem complement_complement (label : VisibleLabel Name) :
    label.complement.complement = label := by
  cases label <;> rfl

theorem toLabel_complementary (label : VisibleLabel Name) :
    label.toLabel.Complementary label.complement.toLabel := by
  cases label <;> simp [toLabel, complement, Label.Complementary]

end VisibleLabel

/-- A finite CCS relabelling. Each table entry gives the signed image of an
input name; the image of the corresponding output is its complement. The
first matching entry wins and names absent from the table map identically. -/
structure Relabelling (Name : Type*) where
  entries : List (Name × VisibleLabel Name)
  deriving DecidableEq

namespace Relabelling

variable {Name : Type*} [DecidableEq Name]

def applyEntries : List (Name × VisibleLabel Name) → Name → VisibleLabel Name
  | [], name => .input name
  | (source, target) :: rest, name =>
      if name = source then target else applyEntries rest name

/-- Apply a finite relabelling, using the identity outside its table. -/
def apply (rename : Relabelling Name) (name : Name) : VisibleLabel Name :=
  applyEntries rename.entries name

@[simp] theorem apply_empty (name : Name) :
    (Relabelling.mk []).apply name = .input name := rfl

@[simp] theorem apply_cons_self (source : Name) (target : VisibleLabel Name)
    (rest : List (Name × VisibleLabel Name)) :
    (Relabelling.mk ((source, target) :: rest)).apply source = target := by
  simp [apply, applyEntries]

theorem apply_cons_of_ne {source name : Name} {target : VisibleLabel Name}
    (rest : List (Name × VisibleLabel Name))
    (hne : name ≠ source) :
    (Relabelling.mk ((source, target) :: rest)).apply name =
      (Relabelling.mk rest).apply name := by
  simp [apply, applyEntries, hne]

end Relabelling

/-- Finite CCS processes with syntax-level restriction and relabelling.

Unlike function-valued operators, finite lists and tables preserve decidable
equality of processes and cannot express relabellings that alter `tau` or fail
to preserve complementary visible actions. -/
inductive StaticProcess (Name : Type*) where
  | nil
  | prefix (action : Label Name) (continuation : StaticProcess Name)
  | choice (left right : StaticProcess Name)
  | parallel (left right : StaticProcess Name)
  | restriction (blocked : List Name) (process : StaticProcess Name)
  | relabelling (rename : Relabelling Name) (process : StaticProcess Name)
  deriving DecidableEq

namespace StaticProcess

variable {Name : Type*} [DecidableEq Name]

/-- Embed the previously developed finite CCS fragment into the language with
static operators. -/
def ofProcess : Process (Label Name) → StaticProcess Name
  | .nil => .nil
  | .prefix action continuation => .prefix action (ofProcess continuation)
  | .choice left right => .choice (ofProcess left) (ofProcess right)
  | .parallel left right => .parallel (ofProcess left) (ofProcess right)

/-- Relabel a CCS action.  Silent actions stay silent, and both polarities of
a visible channel use the same channel table. -/
def relabelAction (rename : Relabelling Name) : Label Name → Label Name
  | .tau => .tau
  | .input name => (rename.apply name).toLabel
  | .output name => (rename.apply name).complement.toLabel

@[simp] theorem relabelAction_tau (rename : Relabelling Name) :
    relabelAction rename (.tau : Label Name) = .tau := rfl

@[simp] theorem relabelAction_input (rename : Relabelling Name) (name : Name) :
    relabelAction rename (.input name) = (rename.apply name).toLabel := rfl

@[simp] theorem relabelAction_output (rename : Relabelling Name) (name : Name) :
    relabelAction rename (.output name) = (rename.apply name).complement.toLabel := rfl

/-- Relabelling preserves the complementary-action invariant used by CCS
synchronization. -/
theorem relabelAction_complementary {left right : Label Name}
    (h : left.Complementary right) (rename : Relabelling Name) :
    (relabelAction rename left).Complementary (relabelAction rename right) := by
  cases left with
  | tau => exact False.elim (Label.not_complementary_tau_left right h)
  | input leftName =>
      cases right with
      | tau => exact False.elim (Label.not_complementary_tau_right (.input leftName) h)
      | input rightName => exact False.elim h
      | output rightName =>
          change leftName = rightName at h
          subst rightName
          exact VisibleLabel.toLabel_complementary (rename.apply leftName)
  | output leftName =>
      cases right with
      | tau => exact False.elim (Label.not_complementary_tau_right (.output leftName) h)
      | input rightName =>
          change leftName = rightName at h
          subst rightName
          exact Label.complementary_symm
            (VisibleLabel.toLabel_complementary (rename.apply leftName))
      | output rightName => exact False.elim h

/-- A restriction always permits `tau` and permits a visible action exactly
when its channel is absent from the finite blocked-name list. -/
def Allowed (blocked : List Name) : Label Name → Prop
  | .tau => True
  | .input name => name ∉ blocked
  | .output name => name ∉ blocked

/-- Whether a finite restriction permits an action is decidable. -/
instance instDecidableAllowed (blocked : List Name) (action : Label Name) :
    Decidable (Allowed blocked action) := by
  cases action <;> simp only [Allowed] <;> infer_instance

omit [DecidableEq Name] in
@[simp] theorem allowed_tau (blocked : List Name) :
    Allowed blocked (.tau : Label Name) := trivial

omit [DecidableEq Name] in
@[simp] theorem allowed_input (blocked : List Name) (name : Name) :
    Allowed blocked (.input name) ↔ name ∉ blocked := Iff.rfl

omit [DecidableEq Name] in
@[simp] theorem allowed_output (blocked : List Name) (name : Name) :
    Allowed blocked (.output name) ↔ name ∉ blocked := Iff.rfl

/-- Structural operational semantics for finite CCS with static operators. -/
inductive Step : StaticProcess Name → Label Name → StaticProcess Name → Prop
  | prefix (action) (continuation) : Step (.prefix action continuation) action continuation
  | choiceLeft {left right next action} (step : Step left action next) :
      Step (.choice left right) action next
  | choiceRight {left right next action} (step : Step right action next) :
      Step (.choice left right) action next
  | parallelLeft {left right next action} (step : Step left action next) :
      Step (.parallel left right) action (.parallel next right)
  | parallelRight {left right next action} (step : Step right action next) :
      Step (.parallel left right) action (.parallel left next)
  | communicate {left right left' right' leftAction rightAction}
      (leftStep : Step left leftAction left') (rightStep : Step right rightAction right')
      (complementary : leftAction.Complementary rightAction) :
      Step (.parallel left right) .tau (.parallel left' right')
  | restrict {blocked process next action}
      (step : Step process action next) (allowed : Allowed blocked action) :
      Step (.restriction blocked process) action (.restriction blocked next)
  | relabel {rename process next action} (step : Step process action next) :
      Step (.relabelling rename process) (relabelAction rename action)
        (.relabelling rename next)

/-- The labelled transition system of finite CCS with static operators. -/
def lts : Cslib.LTS (StaticProcess Name) (Label Name) := ⟨Step⟩

open Cslib.LTS

theorem nil_no_step {action : Label Name} {next : StaticProcess Name} :
    ¬Step .nil action next := by
  intro h
  cases h

theorem prefix_step_iff {head action : Label Name} {continuation next : StaticProcess Name} :
    Step (.prefix head continuation) action next ↔
      action = head ∧ next = continuation := by
  constructor
  · intro h
    cases h
    exact ⟨rfl, rfl⟩
  · rintro ⟨rfl, rfl⟩
    exact .prefix _ _

theorem choice_step_iff {left right next : StaticProcess Name} {action : Label Name} :
    Step (.choice left right) action next ↔ Step left action next ∨ Step right action next := by
  constructor
  · intro h
    cases h with
    | choiceLeft step => exact Or.inl step
    | choiceRight step => exact Or.inr step
  · rintro (step | step)
    · exact .choiceLeft step
    · exact .choiceRight step

theorem restriction_step_iff {blocked : List Name} {process next : StaticProcess Name}
    {action : Label Name} :
    Step (.restriction blocked process) action next ↔
      ∃ process', Step process action process' ∧ Allowed blocked action ∧
        next = .restriction blocked process' := by
  constructor
  · intro h
    cases h with
    | restrict step allowed => exact ⟨_, step, allowed, rfl⟩
  · rintro ⟨process', step, allowed, rfl⟩
    exact .restrict step allowed

theorem relabelling_step_iff {rename : Relabelling Name}
    {process next : StaticProcess Name} {action : Label Name} :
    Step (.relabelling rename process) action next ↔
      ∃ sourceAction process', Step process sourceAction process' ∧
        action = relabelAction rename sourceAction ∧
        next = .relabelling rename process' := by
  constructor
  · intro h
    cases h with
    | relabel step => exact ⟨_, _, step, rfl, rfl⟩
  · rintro ⟨sourceAction, process', step, rfl, rfl⟩
    exact .relabel step

/-- Lift a relation through one fixed restriction context. -/
inductive RestrictionLift (blocked : List Name)
    (relation : StaticProcess Name → StaticProcess Name → Prop) :
    StaticProcess Name → StaticProcess Name → Prop
  | base {left right} (related : relation left right) : RestrictionLift blocked relation left right
  | restriction {left right} (related : relation left right) :
      RestrictionLift blocked relation (.restriction blocked left) (.restriction blocked right)

theorem restrictionLift_isSimulation {blocked : List Name}
    {relation : StaticProcess Name → StaticProcess Name → Prop}
    (hsim : lts.IsHomSimulation relation) :
    lts.IsHomSimulation (RestrictionLift blocked relation) := by
  intro source target hrel action next hstep
  cases hrel with
  | base hrel =>
      obtain ⟨next', hnext', hrel'⟩ := hsim.follow hrel hstep
      exact ⟨next', hnext', .base hrel'⟩
  | restriction hrel =>
      change Step (.restriction blocked _) action next at hstep
      rw [restriction_step_iff] at hstep
      obtain ⟨source', hsource', allowed, rfl⟩ := hstep
      obtain ⟨target', htarget', hrel'⟩ := hsim.follow hrel hsource'
      exact ⟨.restriction blocked target', .restrict htarget' allowed, .restriction hrel'⟩

theorem restrictionLift_isBisimulation {blocked : List Name}
    {relation : StaticProcess Name → StaticProcess Name → Prop}
    (hbisim : lts.IsHomBisimulation relation) :
    lts.IsHomBisimulation (RestrictionLift blocked relation) := by
  intro source target hrel action
  constructor
  · intro next hstep
    cases hrel with
    | base hrel =>
        obtain ⟨next', hnext', hrel'⟩ := (hbisim hrel _).1 next hstep
        exact ⟨next', hnext', .base hrel'⟩
    | restriction hrel =>
        change Step (.restriction blocked _) action next at hstep
        rw [restriction_step_iff] at hstep
        obtain ⟨source', hsource', allowed, rfl⟩ := hstep
        obtain ⟨target', htarget', hrel'⟩ := (hbisim hrel _).1 _ hsource'
        exact ⟨.restriction blocked target', .restrict htarget' allowed, .restriction hrel'⟩
  · intro next hstep
    cases hrel with
    | base hrel =>
        obtain ⟨next', hnext', hrel'⟩ := (hbisim hrel _).2 next hstep
        exact ⟨next', hnext', .base hrel'⟩
    | restriction hrel =>
        change Step (.restriction blocked _) action next at hstep
        rw [restriction_step_iff] at hstep
        obtain ⟨target', htarget', allowed, rfl⟩ := hstep
        obtain ⟨source', hsource', hrel'⟩ := (hbisim hrel _).2 _ htarget'
        exact ⟨.restriction blocked source', .restrict hsource' allowed, .restriction hrel'⟩

/-- Restriction preserves strong bisimilarity. -/
theorem restriction_congr (blocked : List Name) {left right : StaticProcess Name}
    (h : lts.HomBisimilarity left right) :
    lts.HomBisimilarity (.restriction blocked left) (.restriction blocked right) := by
  obtain ⟨relation, hrel, hbisim⟩ := h
  exact ⟨RestrictionLift blocked relation, .restriction hrel,
    restrictionLift_isBisimulation hbisim⟩

/-- Lift a relation through one fixed relabelling context. -/
inductive RelabellingLift (rename : Relabelling Name)
    (relation : StaticProcess Name → StaticProcess Name → Prop) :
    StaticProcess Name → StaticProcess Name → Prop
  | base {left right} (related : relation left right) : RelabellingLift rename relation left right
  | relabelling {left right} (related : relation left right) :
      RelabellingLift rename relation (.relabelling rename left) (.relabelling rename right)

theorem relabellingLift_isSimulation {rename : Relabelling Name}
    {relation : StaticProcess Name → StaticProcess Name → Prop}
    (hsim : lts.IsHomSimulation relation) :
    lts.IsHomSimulation (RelabellingLift rename relation) := by
  intro source target hrel action next hstep
  cases hrel with
  | base hrel =>
      obtain ⟨next', hnext', hrel'⟩ := hsim.follow hrel hstep
      exact ⟨next', hnext', .base hrel'⟩
  | relabelling hrel =>
      change Step (.relabelling rename _) action next at hstep
      rw [relabelling_step_iff] at hstep
      obtain ⟨sourceAction, source', hsource', rfl, rfl⟩ := hstep
      obtain ⟨target', htarget', hrel'⟩ := hsim.follow hrel hsource'
      exact ⟨.relabelling rename target', .relabel htarget', .relabelling hrel'⟩

theorem relabellingLift_isBisimulation {rename : Relabelling Name}
    {relation : StaticProcess Name → StaticProcess Name → Prop}
    (hbisim : lts.IsHomBisimulation relation) :
    lts.IsHomBisimulation (RelabellingLift rename relation) := by
  intro source target hrel action
  constructor
  · intro next hstep
    cases hrel with
    | base hrel =>
        obtain ⟨next', hnext', hrel'⟩ := (hbisim hrel _).1 next hstep
        exact ⟨next', hnext', .base hrel'⟩
    | relabelling hrel =>
        change Step (.relabelling rename _) action next at hstep
        rw [relabelling_step_iff] at hstep
        obtain ⟨sourceAction, source', hsource', rfl, rfl⟩ := hstep
        obtain ⟨target', htarget', hrel'⟩ := (hbisim hrel _).1 _ hsource'
        exact ⟨.relabelling rename target', .relabel htarget', .relabelling hrel'⟩
  · intro next hstep
    cases hrel with
    | base hrel =>
        obtain ⟨next', hnext', hrel'⟩ := (hbisim hrel _).2 next hstep
        exact ⟨next', hnext', .base hrel'⟩
    | relabelling hrel =>
        change Step (.relabelling rename _) action next at hstep
        rw [relabelling_step_iff] at hstep
        obtain ⟨sourceAction, target', htarget', rfl, rfl⟩ := hstep
        obtain ⟨source', hsource', hrel'⟩ := (hbisim hrel _).2 _ htarget'
        exact ⟨.relabelling rename source', .relabel hsource', .relabelling hrel'⟩

/-- Relabelling preserves strong bisimilarity. -/
theorem relabelling_congr (rename : Relabelling Name) {left right : StaticProcess Name}
    (h : lts.HomBisimilarity left right) :
    lts.HomBisimilarity (.relabelling rename left) (.relabelling rename right) := by
  obtain ⟨relation, hrel, hbisim⟩ := h
  exact ⟨RelabellingLift rename relation, .relabelling hrel,
    relabellingLift_isBisimulation hbisim⟩

end StaticProcess

end Cslib.CCS
