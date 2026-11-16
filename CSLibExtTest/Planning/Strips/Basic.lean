/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.Planning.Strips.Basic
public import Mathlib.Tactic.NormNum

@[expose] public section

/-!
# Tests for propositional STRIPS semantics
-/

set_option autoImplicit false

open Cslib.Planning.Strips

namespace CSLibExtTest.Planning.Strips

/-- Move from atom `0` to atom `1`: require `0`, forbid `1`, delete `0`, add `1`. -/
def move : Operator (Fin 2) where
  prePos := {0}
  preNeg := {1}
  add := {1}
  del := {0}

/-- An operator blocked by a negative precondition when atom `1` is present. -/
def blocked : Operator (Fin 2) where
  prePos := ∅
  preNeg := {1}
  add := {0}
  del := ∅

/-- A one-step task: start at `0`, goal `1` true and `0` false. -/
def moveTask : Cslib.Planning.Strips.Task (Fin 2) where
  init := {0}
  goalPos := {1}
  goalNeg := {0}
  ops := [move]

/-- A task with the same init/goal but no operators. -/
def noOpsTask : Cslib.Planning.Strips.Task (Fin 2) where
  init := {0}
  goalPos := {1}
  goalNeg := {0}
  ops := []

/-- Already at the goal `{1}`, with only the blocked operator available. -/
def blockedGoalTask : Cslib.Planning.Strips.Task (Fin 2) where
  init := {1}
  goalPos := {1}
  goalNeg := {0}
  ops := [blocked]

/-- The concrete operator and task are well-formed in Bylander's sense. -/
example : moveTask.WellFormed := by
  constructor
  · intro op hop
    simp [moveTask] at hop
    subst hop
    simp [Operator.WellFormed, move]
  · decide

/-- Progression of the applicable move gives `{1}`. -/
example : move.apply ({0} : State (Fin 2)) = {1} := by
  decide

/-- The deleted/negative-goal atom is absent after progression. -/
example : (0 : Fin 2) ∉ move.apply ({0} : State (Fin 2)) := by
  decide

/-- With disjoint add/delete effects, add-then-delete equals delete-then-add
on the concrete state. -/
example :
    move.apply ({0} : State (Fin 2)) =
      (({0} : State (Fin 2)) \ move.del) ∪ move.add :=
  Operator.apply_eq_deleteFirst_of_disjoint move _ (by decide)

/-- A negative precondition can block: Bylander's raw result is the identity
when `1` is already true. -/
example : blocked.result ({1} : State (Fin 2)) = {1} :=
  Operator.result_eq_self_of_not_applicable blocked _ (by
    simp [blocked, Operator.applicable])

/-- Bylander's total semantics accepts `[blocked]` from the already-goal
state `{1}`: the inapplicable operator is an identity step. -/
example : blockedGoalTask.ResultExecutes {1} [blocked] {1} :=
  Cslib.Planning.Strips.Task.ResultExecutes.cons (by simp [blockedGoalTask])
    Cslib.Planning.Strips.Task.ResultExecutes.nil

/-- Hence `[blocked]` is a valid total plan for `blockedGoalTask`, even
though `blocked` is not applicable in its initial state. -/
example : blockedGoalTask.ValidPlan [blocked] :=
  ⟨{1}, Cslib.Planning.Strips.Task.ResultExecutes.cons
      (by simp [blockedGoalTask])
      Cslib.Planning.Strips.Task.ResultExecutes.nil,
    by simp [blockedGoalTask, Cslib.Planning.Strips.Task.IsGoalState]⟩

/-- Deleting that identity step leaves a strict execution to the same state. -/
example :
    ∃ strictPlan,
      blockedGoalTask.Executes blockedGoalTask.init strictPlan {1} := by
  have h : blockedGoalTask.ResultExecutes {1} [blocked] {1} :=
    Cslib.Planning.Strips.Task.ResultExecutes.cons (by simp [blockedGoalTask])
      Cslib.Planning.Strips.Task.ResultExecutes.nil
  exact h.exists_executes

/-- The one-operator total plan is valid, including the negative goal. -/
example : moveTask.ValidPlan [move] :=
  ⟨{1}, Cslib.Planning.Strips.Task.ResultExecutes.cons (by simp [moveTask])
      Cslib.Planning.Strips.Task.ResultExecutes.nil,
    by simp [moveTask, Cslib.Planning.Strips.Task.IsGoalState]⟩

/-- The same goal is strictly LTS-reachable, through total plan existence. -/
example : moveTask.GoalReachable := by
  rw [← Cslib.Planning.Strips.Task.planExists_iff_goalReachable]
  exact ⟨[move], ⟨{1},
    Cslib.Planning.Strips.Task.ResultExecutes.cons (by simp [moveTask])
      Cslib.Planning.Strips.Task.ResultExecutes.nil,
    by simp [moveTask, Cslib.Planning.Strips.Task.IsGoalState]⟩⟩

/-- With no operators, the non-goal initial state has no plan. -/
example : ¬ noOpsTask.PlanExists :=
  noOpsTask.not_planExists_of_ops_nil rfl (by simp [noOpsTask, Cslib.Planning.Strips.Task.IsGoalState])

/-- The empty plan is valid exactly when the initial state is a goal state. -/
example {α : Type*} [DecidableEq α] (task : Cslib.Planning.Strips.Task α) :
    task.ValidPlan [] ↔ task.IsGoalState task.init :=
  task.validPlan_nil_iff

/-- Strict plan execution is strict LTS multistep transition. -/
example {α : Type*} [DecidableEq α] (task : Cslib.Planning.Strips.Task α)
    {s s' : State α} {plan : List (Operator α)} :
    task.Executes s plan s' ↔ task.toLTS.MTr s plan s' :=
  task.executes_iff_mtr

/-- Total result execution is total LTS multistep transition, exact traces
included. -/
example {α : Type*} [DecidableEq α] (task : Cslib.Planning.Strips.Task α)
    {s s' : State α} {plan : List (Operator α)} :
    task.ResultExecutes s plan s' ↔ task.toResultLTS.MTr s plan s' :=
  task.resultExecutes_iff_resultMtr

end CSLibExtTest.Planning.Strips
