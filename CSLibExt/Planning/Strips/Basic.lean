/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Cslib.Foundations.Semantics.LTS.Basic
public import Mathlib.Data.Finset.Basic

/-!
# Propositional STRIPS semantics

A finite propositional STRIPS task has an initial state, a goal state, and a
finite list of operators. A state is a finset of true atoms. An operator has
precondition, add, and delete finsets; it is applicable when its preconditions
are contained in the state, and progression first deletes and then adds.

The task view as a labelled transition system uses the canonical `Cslib.LTS`,
with operators as labels. A valid plan is exactly a finite execution whose
final state contains the goal. This file covers only semantics and
reachability; PLANSAT complexity is a separate slice.

## Main declarations

* `Operator`: one STRIPS operator with `pre`, `add`, and `del` atom finsets.
* `Task`: initial state, goal, and operator list.
* `Task.toLTS`: the progression labelled transition system.
* `Task.Executes`: finite plan execution from one state to another.
* `Task.executes_iff_mtr`: plan execution is multistep LTS transition.
* `Task.planExists_iff_goalReachable`: a valid plan exists exactly when a
  goal-containing state is reachable.
-/

@[expose] public section

set_option autoImplicit false

namespace Cslib.Planning.Strips

/-- A STRIPS state: the finset of atoms true in the state. -/
abbrev State (α : Type*) := Finset α

/-- A propositional STRIPS operator. -/
structure Operator (α : Type*) where
  /-- Atoms that must be true before the operator can fire. -/
  pre : Finset α
  /-- Atoms made true by the operator. -/
  add : Finset α
  /-- Atoms made false by the operator, before adds are applied. -/
  del : Finset α
deriving DecidableEq

/-- A finite propositional STRIPS task. -/
structure Task (α : Type*) where
  /-- Initial state. -/
  init : State α
  /-- Goal atoms that must all be true in a successful final state. -/
  goal : Finset α
  /-- Available operators. -/
  ops : List (Operator α)
deriving DecidableEq

/-- An operator is applicable in a state when all its preconditions hold. -/
protected def Operator.applicable {α : Type*} (op : Operator α) (s : State α) : Prop :=
  op.pre ⊆ s

/-- STRIPS progression: delete first, then add. If an atom is both deleted and
added, the add effect wins. -/
protected def Operator.apply {α : Type*} [DecidableEq α] (op : Operator α) (s : State α) :
    State α :=
  (s \ op.del) ∪ op.add

/-- Membership in a progressed state: an atom survives if it was present and
not deleted, or it is added. -/
theorem Operator.mem_apply {α : Type*} [DecidableEq α] (op : Operator α) (s : State α)
    (a : α) :
    a ∈ op.apply s ↔ (a ∈ s ∧ a ∉ op.del) ∨ a ∈ op.add := by
  simp [Operator.apply, Finset.mem_union, Finset.mem_sdiff]

/-- Add effects are present after progression. -/
theorem Operator.add_subset_apply {α : Type*} [DecidableEq α] (op : Operator α)
    (s : State α) :
    op.add ⊆ op.apply s :=
  Finset.subset_union_right

/-- Progression creates no atoms outside the old state and the add effects. -/
theorem Operator.apply_subset {α : Type*} [DecidableEq α] (op : Operator α) (s : State α) :
    op.apply s ⊆ s ∪ op.add := by
  intro a ha
  rw [Operator.mem_apply] at ha
  cases ha with
  | inl h => exact Finset.mem_union_left _ h.1
  | inr h => exact Finset.mem_union_right _ h

/-- Finite execution of a plan: `task.Executes s plan s'` means starting from
`s`, successively firing the operators in `plan` (each must belong to the task
and be applicable) ends in `s'`. -/
inductive Task.Executes {α : Type*} [DecidableEq α] (task : Task α) :
    State α → List (Operator α) → State α → Prop where
  | nil {s : State α} : task.Executes s [] s
  | cons {s s' : State α} {op : Operator α} {plan : List (Operator α)}
      (hmem : op ∈ task.ops) (happ : op.applicable s)
      (h : task.Executes (op.apply s) plan s') :
      task.Executes s (op :: plan) s'

/-- The progression labelled transition system of a STRIPS task. Labels are
operators, states are atom finsets, and a transition fires one applicable
task operator. -/
protected def Task.toLTS {α : Type*} [DecidableEq α] (task : Task α) :
    LTS (State α) (Operator α) where
  Tr s op s' := op ∈ task.ops ∧ op.applicable s ∧ s' = op.apply s

/-- Transitions in the STRIPS LTS are exactly applicable task operators. -/
theorem Task.toLTS_tr_iff {α : Type*} [DecidableEq α] (task : Task α) (s : State α)
    (op : Operator α) (s' : State α) :
    task.toLTS.Tr s op s' ↔ op ∈ task.ops ∧ op.applicable s ∧ s' = op.apply s :=
  Iff.rfl

/-- Plan execution is exactly multistep transition in the STRIPS LTS, with the
plan itself as the label trace. -/
theorem Task.executes_iff_mtr {α : Type*} [DecidableEq α] (task : Task α) {s s' : State α}
    {plan : List (Operator α)} :
    task.Executes s plan s' ↔ task.toLTS.MTr s plan s' := by
  constructor
  · intro h
    induction h with
    | nil => exact LTS.MTr.refl
    | cons hmem happ _ ih => exact LTS.MTr.stepL ⟨hmem, happ, rfl⟩ ih
  · intro h
    induction h with
    | refl => exact Task.Executes.nil
    | stepL htr _ ih =>
      obtain ⟨hmem, happ, rfl⟩ := htr
      exact Task.Executes.cons hmem happ ih

/-- A plan is valid for a task when executing it from the initial state reaches
a state containing every goal atom. -/
protected def Task.ValidPlan {α : Type*} [DecidableEq α] (task : Task α)
    (plan : List (Operator α)) : Prop :=
  ∃ s, task.Executes task.init plan s ∧ task.goal ⊆ s

/-- Some valid plan exists for the task. -/
protected def Task.PlanExists {α : Type*} [DecidableEq α] (task : Task α) : Prop :=
  ∃ plan, task.ValidPlan plan

/-- A state containing the goal is reachable in the STRIPS LTS. -/
protected def Task.GoalReachable {α : Type*} [DecidableEq α] (task : Task α) : Prop :=
  ∃ s, task.toLTS.CanReach task.init s ∧ task.goal ⊆ s

/-- The empty plan is valid exactly when the goal already holds initially. -/
theorem Task.validPlan_nil_iff {α : Type*} [DecidableEq α] (task : Task α) :
    task.ValidPlan [] ↔ task.goal ⊆ task.init := by
  constructor
  · rintro ⟨s, hex, hgoal⟩
    cases hex
    exact hgoal
  · intro hgoal
    exact ⟨task.init, Task.Executes.nil, hgoal⟩

/-- A valid plan exists exactly when a goal-containing state is reachable in
the progression LTS. -/
theorem Task.planExists_iff_goalReachable {α : Type*} [DecidableEq α] (task : Task α) :
    task.PlanExists ↔ task.GoalReachable := by
  constructor
  · rintro ⟨plan, s, hex, hgoal⟩
    exact ⟨s, ⟨plan, (task.executes_iff_mtr).mp hex⟩, hgoal⟩
  · rintro ⟨s, ⟨plan, hmtr⟩, hgoal⟩
    exact ⟨plan, s, (task.executes_iff_mtr).mpr hmtr, hgoal⟩

/-- With no operators, an initially false goal has no valid plan. -/
theorem Task.not_planExists_of_ops_nil {α : Type*} [DecidableEq α] (task : Task α)
    (hops : task.ops = []) (hgoal : ¬ task.goal ⊆ task.init) :
    ¬ task.PlanExists := by
  rintro ⟨plan, s, hex, hgoal_s⟩
  cases hex with
  | nil => exact hgoal hgoal_s
  | cons hmem _ _ =>
    rw [hops] at hmem
    simp at hmem

end Cslib.Planning.Strips
