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

/-- Move from atom `0` to atom `1`: delete `0`, add `1`. -/
def move : Operator (Fin 2) where
  pre := {0}
  add := {1}
  del := {0}

/-- A one-step task: start at atom `0`, goal atom `1`. -/
def moveTask : Cslib.Planning.Strips.Task (Fin 2) where
  init := {0}
  goal := {1}
  ops := [move]

/-- A task with the same init/goal but no operators. -/
def noOpsTask : Cslib.Planning.Strips.Task (Fin 2) where
  init := {0}
  goal := {1}
  ops := []

/-- Progression deletes before adding: the result is `{1}`, not `{0, 1}`. -/
example : move.apply ({0} : State (Fin 2)) = {1} := by
  decide

/-- The deleted atom is absent after progression, so delete effects matter. -/
example : (0 : Fin 2) ∉ move.apply ({0} : State (Fin 2)) := by
  decide

/-- The one-operator plan is valid. -/
example : moveTask.ValidPlan [move] :=
  ⟨{1}, Cslib.Planning.Strips.Task.Executes.cons (by simp [moveTask]) (by simp [moveTask, move, Operator.applicable]) Cslib.Planning.Strips.Task.Executes.nil,
    by decide⟩

/-- The same goal is LTS-reachable, through the plan-existence theorem. -/
example : moveTask.GoalReachable := by
  rw [← Cslib.Planning.Strips.Task.planExists_iff_goalReachable]
  exact ⟨[move], ⟨{1},
    Cslib.Planning.Strips.Task.Executes.cons (by simp [moveTask]) (by simp [moveTask, move, Operator.applicable]) Cslib.Planning.Strips.Task.Executes.nil,
    by decide⟩⟩

/-- With no operators, the false goal has no plan. -/
example : ¬ noOpsTask.PlanExists :=
  noOpsTask.not_planExists_of_ops_nil rfl (by decide)

/-- The empty plan is valid exactly in the already-goal case, as an example. -/
example {α : Type*} [DecidableEq α] (task : Cslib.Planning.Strips.Task α) :
    task.ValidPlan [] ↔ task.goal ⊆ task.init :=
  task.validPlan_nil_iff

/-- Plan execution is LTS multistep transition, as an example. -/
example {α : Type*} [DecidableEq α] (task : Cslib.Planning.Strips.Task α) {s s' : State α}
    {plan : List (Operator α)} :
    task.Executes s plan s' ↔ task.toLTS.MTr s plan s' :=
  task.executes_iff_mtr

end CSLibExtTest.Planning.Strips
