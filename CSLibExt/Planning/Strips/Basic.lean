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

This file follows the propositional STRIPS model in Bylander (1994), Section
2.1, as also used by the repository's bounded-STRIPS wanted specification. A
state is a finset of true atoms. An operator has positive and negative
preconditions and positive and negative postconditions (add and delete lists).
It is applicable when every positive precondition is true and no negative
precondition is true. Bylander's one-step result is `(S ∪ add) \ del` for an
applicable operator and `S` otherwise. Goals likewise have positive and
negative parts.

The file exposes two execution views. The strict progression LTS fires only
applicable operators. Following Bylander, the total result LTS treats an
inapplicable operator as an identity step, and `Task.ValidPlan` uses this
total result semantics. Deleting the identity steps from a total execution
gives a strict execution to the same final state, so total plan existence and
strict goal reachability agree. This file covers only semantics and
reachability; PLANSAT complexity is a separate slice.

## References

* T. Bylander, "The computational complexity of propositional STRIPS
  planning", Artificial Intelligence 69 (1994), Section 2.1.

## Main declarations

* `Operator`: positive/negative preconditions and add/delete effects.
* `Task`: initial state, positive/negative goals, and operator list.
* `Operator.result`: Bylander's total one-step result operation.
* `Task.toLTS`: the strict progression labelled transition system.
* `Task.toResultLTS`: Bylander's total result labelled transition system.
* `Task.Executes`: strict finite plan execution from one state to another.
* `Task.ResultExecutes`: total Bylander plan execution; inapplicable
  operators are identity steps.
* `Task.executes_iff_mtr` and `Task.resultExecutes_iff_resultMtr`: each
  execution relation is multistep transition in its LTS.
* `Task.planExists_iff_goalReachable`: a total valid plan exists exactly
  when a goal state is strictly reachable.
-/

@[expose] public section

set_option autoImplicit false

namespace Cslib.Planning.Strips

/-- A STRIPS state: the finset of atoms true in the state. -/
abbrev State (α : Type*) := Finset α

/-- A propositional STRIPS operator in Bylander's form: positive and negative
preconditions, then positive postconditions (add list) and negative
postconditions (delete list). -/
structure Operator (α : Type*) where
  /-- Atoms that must be true before the operator can fire. -/
  prePos : Finset α
  /-- Atoms that must be false before the operator can fire. -/
  preNeg : Finset α
  /-- Atoms made true by the operator. -/
  add : Finset α
  /-- Atoms made false by the operator. -/
  del : Finset α
deriving DecidableEq

/-- A finite propositional STRIPS task. -/
structure Task (α : Type*) where
  /-- Initial state. -/
  init : State α
  /-- Atoms that must be true in a goal state. -/
  goalPos : Finset α
  /-- Atoms that must be false in a goal state. -/
  goalNeg : Finset α
  /-- Available operators. -/
  ops : List (Operator α)
deriving DecidableEq

/-- An operator's preconditions and postconditions are satisfiable
conjunctions: no atom is both positively and negatively required, and no atom
is both added and deleted. -/
protected def Operator.WellFormed {α : Type*} (op : Operator α) : Prop :=
  Disjoint op.prePos op.preNeg ∧ Disjoint op.add op.del

/-- A task is well-formed when every operator is well-formed and the positive
and negative goals are disjoint. -/
protected def Task.WellFormed {α : Type*} (task : Task α) : Prop :=
  (∀ op ∈ task.ops, op.WellFormed) ∧ Disjoint task.goalPos task.goalNeg

/-- An operator is applicable in a state when all positive preconditions hold
and no negative precondition holds. -/
protected def Operator.applicable {α : Type*} (op : Operator α)
    (s : State α) : Prop :=
  op.prePos ⊆ s ∧ Disjoint op.preNeg s

/-- Progression for an applicable operator, in Bylander's order:
`(s ∪ add) \ del`. On well-formed operators (`Disjoint add del`) this agrees
with delete-first progression; see
`Operator.apply_eq_deleteFirst_of_disjoint`. -/
protected def Operator.apply {α : Type*} [DecidableEq α] (op : Operator α)
    (s : State α) : State α :=
  (s ∪ op.add) \ op.del

/-- Bylander's total one-step result: apply an applicable operator, and leave
the state unchanged if its preconditions fail. `Task.ResultExecutes` and
`Task.ValidPlan` use this total step; `Task.Executes` and `Task.toLTS`
retain the strict applicable-only view. -/
protected def Operator.result {α : Type*} [DecidableEq α] (op : Operator α)
    (s : State α) : State α :=
  if op.prePos ⊆ s ∧ Disjoint op.preNeg s then op.apply s else s

/-- Membership in a progressed state: an atom is present when it was present
or added, and not deleted. -/
theorem Operator.mem_apply {α : Type*} [DecidableEq α] (op : Operator α)
    (s : State α) (a : α) :
    a ∈ op.apply s ↔ (a ∈ s ∨ a ∈ op.add) ∧ a ∉ op.del := by
  simp [Operator.apply, Finset.mem_union, Finset.mem_sdiff]

/-- For well-formed effects, Bylander's add-then-delete progression agrees
with delete-then-add progression. -/
theorem Operator.apply_eq_deleteFirst_of_disjoint {α : Type*}
    [DecidableEq α] (op : Operator α) (s : State α)
    (hdisj : Disjoint op.add op.del) :
    op.apply s = (s \ op.del) ∪ op.add := by
  ext a
  by_cases hadd : a ∈ op.add
  · have hnotdel : a ∉ op.del := fun hdel =>
      (Finset.disjoint_left.mp hdisj) hadd hdel
    simp [Operator.mem_apply, hadd, hnotdel]
  · simp [Operator.mem_apply, hadd]

/-- The total result operation applies an applicable operator. -/
theorem Operator.result_eq_apply_of_applicable {α : Type*} [DecidableEq α]
    (op : Operator α) (s : State α) (h : op.applicable s) :
    op.result s = op.apply s := by
  unfold Operator.result
  exact ite_eq_left h

/-- The total result operation leaves the state unchanged when the operator
is not applicable, as in Bylander's raw `Result`. -/
theorem Operator.result_eq_self_of_not_applicable {α : Type*}
    [DecidableEq α] (op : Operator α) (s : State α)
    (h : ¬ op.applicable s) :
    op.result s = s := by
  unfold Operator.result
  exact ite_eq_right h

/-- A state satisfies the task goal when every positive goal atom is true and
no negative goal atom is true. -/
protected def Task.IsGoalState {α : Type*} (task : Task α) (s : State α) :
    Prop :=
  task.goalPos ⊆ s ∧ Disjoint task.goalNeg s

/-- Strict finite execution of a plan: `task.Executes s plan s'` means
starting from `s`, successively firing the operators in `plan` (each must
belong to the task and be applicable) ends in `s'`. -/
inductive Task.Executes {α : Type*} [DecidableEq α] (task : Task α) :
    State α → List (Operator α) → State α → Prop where
  | nil {s : State α} : task.Executes s [] s
  | cons {s s' : State α} {op : Operator α} {plan : List (Operator α)}
      (hmem : op ∈ task.ops) (happ : op.applicable s)
      (h : task.Executes (op.apply s) plan s') :
      task.Executes s (op :: plan) s'

/-- Total Bylander execution of a plan: `task.ResultExecutes s plan s'` means
starting from `s`, successively replacing the state by `Operator.result` for
each operator in `plan` ends in `s'`. Every operator must belong to the task,
but an inapplicable operator is an identity step rather than making the plan
inexecutable. -/
inductive Task.ResultExecutes {α : Type*} [DecidableEq α] (task : Task α) :
    State α → List (Operator α) → State α → Prop where
  | nil {s : State α} : task.ResultExecutes s [] s
  | cons {s s' : State α} {op : Operator α} {plan : List (Operator α)}
      (hmem : op ∈ task.ops)
      (h : task.ResultExecutes (op.result s) plan s') :
      task.ResultExecutes s (op :: plan) s'

/-- Every strict execution is a total result execution with the same trace. -/
theorem Task.Executes.toResultExecutes {α : Type*} [DecidableEq α]
    {task : Task α} {s s' : State α} {plan : List (Operator α)}
    (h : task.Executes s plan s') :
    task.ResultExecutes s plan s' := by
  induction h with
  | nil => exact Task.ResultExecutes.nil
  | cons hmem happ _ ih =>
    apply Task.ResultExecutes.cons hmem
    rwa [Operator.result_eq_apply_of_applicable _ _ happ]

/-- Every total result execution has a strict execution to the same final
state: the strict trace is obtained by deleting the operators that were
inapplicable (hence identity steps) in the total execution. -/
theorem Task.ResultExecutes.exists_executes {α : Type*} [DecidableEq α]
    {task : Task α} {s s' : State α} {plan : List (Operator α)}
    (h : task.ResultExecutes s plan s') :
    ∃ strictPlan, task.Executes s strictPlan s' := by
  refine h.rec (motive := fun s _plan s' _ =>
    ∃ strictPlan, task.Executes s strictPlan s') ?_ ?_
  · intro _s
    exact ⟨[], Task.Executes.nil⟩
  · intro s _s' op _plan hmem _ ih
    by_cases happ : op.applicable s
    · obtain ⟨strictPlan, hstrict⟩ := ih
      refine ⟨op :: strictPlan, ?_⟩
      apply Task.Executes.cons hmem happ
      rwa [Operator.result_eq_apply_of_applicable _ _ happ] at hstrict
    · obtain ⟨strictPlan, hstrict⟩ := ih
      refine ⟨strictPlan, ?_⟩
      rwa [Operator.result_eq_self_of_not_applicable _ _ happ] at hstrict

/-- The strict progression labelled transition system of a STRIPS task.
Labels are operators, states are atom finsets, and a transition fires one
applicable task operator. -/
protected def Task.toLTS {α : Type*} [DecidableEq α] (task : Task α) :
    LTS (State α) (Operator α) where
  Tr s op s' := op ∈ task.ops ∧ op.applicable s ∧ s' = op.apply s

/-- Transitions in the STRIPS LTS are exactly applicable task operators. -/
theorem Task.toLTS_tr_iff {α : Type*} [DecidableEq α] (task : Task α)
    (s : State α) (op : Operator α) (s' : State α) :
    task.toLTS.Tr s op s' ↔ op ∈ task.ops ∧ op.applicable s ∧ s' = op.apply s :=
  Iff.rfl

/-- Strict plan execution is exactly multistep transition in the strict
STRIPS LTS, with the plan itself as the label trace. -/
theorem Task.executes_iff_mtr {α : Type*} [DecidableEq α] (task : Task α)
    {s s' : State α} {plan : List (Operator α)} :
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

/-- Bylander's total result labelled transition system of a STRIPS task.
A transition labelled by a task operator replaces the state by that
operator's total result: progression if applicable, and the same state if
not. -/
protected def Task.toResultLTS {α : Type*} [DecidableEq α] (task : Task α) :
    LTS (State α) (Operator α) where
  Tr s op s' := op ∈ task.ops ∧ s' = op.result s

/-- Transitions in the total result LTS are exactly task operators taken by
`Operator.result`. -/
theorem Task.toResultLTS_tr_iff {α : Type*} [DecidableEq α] (task : Task α)
    (s : State α) (op : Operator α) (s' : State α) :
    task.toResultLTS.Tr s op s' ↔ op ∈ task.ops ∧ s' = op.result s :=
  Iff.rfl

/-- Total Bylander plan execution is exactly multistep transition in the
total result LTS, with the plan itself as the label trace. In particular, a
trace may contain inapplicable operators as identity steps. -/
theorem Task.resultExecutes_iff_resultMtr {α : Type*} [DecidableEq α]
    (task : Task α) {s s' : State α} {plan : List (Operator α)} :
    task.ResultExecutes s plan s' ↔ task.toResultLTS.MTr s plan s' := by
  constructor
  · intro h
    induction h with
    | nil => exact LTS.MTr.refl
    | cons hmem _ ih => exact LTS.MTr.stepL ⟨hmem, rfl⟩ ih
  · intro h
    induction h with
    | refl => exact Task.ResultExecutes.nil
    | stepL htr _ ih =>
      obtain ⟨hmem, rfl⟩ := htr
      exact Task.ResultExecutes.cons hmem ih

/-- A plan is valid for a task, in Bylander's total `Result` semantics, when
executing it from the initial state by `Operator.result` reaches a goal
state. Inapplicable operators in the plan are identity steps. -/
protected def Task.ValidPlan {α : Type*} [DecidableEq α] (task : Task α)
    (plan : List (Operator α)) : Prop :=
  ∃ s, task.ResultExecutes task.init plan s ∧ task.IsGoalState s

/-- Some valid plan exists for the task. -/
protected def Task.PlanExists {α : Type*} [DecidableEq α] (task : Task α) :
    Prop :=
  ∃ plan, task.ValidPlan plan

/-- A goal state is reachable in the strict progression LTS. -/
protected def Task.GoalReachable {α : Type*} [DecidableEq α] (task : Task α) :
    Prop :=
  ∃ s, task.toLTS.CanReach task.init s ∧ task.IsGoalState s

/-- A goal state is reachable in Bylander's total result LTS. -/
protected def Task.ResultGoalReachable {α : Type*} [DecidableEq α]
    (task : Task α) : Prop :=
  ∃ s, task.toResultLTS.CanReach task.init s ∧ task.IsGoalState s

/-- The empty plan is valid exactly when the initial state is a goal state. -/
theorem Task.validPlan_nil_iff {α : Type*} [DecidableEq α] (task : Task α) :
    task.ValidPlan [] ↔ task.IsGoalState task.init := by
  constructor
  · rintro ⟨s, hex, hgoal⟩
    cases hex
    exact hgoal
  · intro hgoal
    exact ⟨task.init, Task.ResultExecutes.nil, hgoal⟩

/-- A total valid plan exists exactly when a goal state is reachable in
Bylander's total result LTS. -/
theorem Task.planExists_iff_resultGoalReachable {α : Type*} [DecidableEq α]
    (task : Task α) :
    task.PlanExists ↔ task.ResultGoalReachable := by
  constructor
  · rintro ⟨plan, s, hex, hgoal⟩
    exact ⟨s, ⟨plan, (task.resultExecutes_iff_resultMtr).mp hex⟩, hgoal⟩
  · rintro ⟨s, ⟨plan, hmtr⟩, hgoal⟩
    exact ⟨plan, s, (task.resultExecutes_iff_resultMtr).mpr hmtr, hgoal⟩

/-- A total valid plan exists exactly when a goal state is reachable in the
strict progression LTS. The total-to-strict direction deletes inapplicable
identity steps from the total plan; the converse uses the same trace. -/
theorem Task.planExists_iff_goalReachable {α : Type*} [DecidableEq α]
    (task : Task α) :
    task.PlanExists ↔ task.GoalReachable := by
  constructor
  · rintro ⟨plan, s, hex, hgoal⟩
    obtain ⟨strictPlan, hstrict⟩ := hex.exists_executes
    exact ⟨s, ⟨strictPlan, (task.executes_iff_mtr).mp hstrict⟩, hgoal⟩
  · rintro ⟨s, ⟨plan, hmtr⟩, hgoal⟩
    exact ⟨plan, s, ((task.executes_iff_mtr).mpr hmtr).toResultExecutes, hgoal⟩

/-- Total result goal reachability and strict goal reachability coincide:
identity steps add traces, but no new reachable states. -/
theorem Task.resultGoalReachable_iff_goalReachable {α : Type*}
    [DecidableEq α] (task : Task α) :
    task.ResultGoalReachable ↔ task.GoalReachable :=
  task.planExists_iff_resultGoalReachable.symm.trans
    task.planExists_iff_goalReachable

/-- With no operators, a non-goal initial state has no valid plan. -/
theorem Task.not_planExists_of_ops_nil {α : Type*} [DecidableEq α]
    (task : Task α) (hops : task.ops = [])
    (hgoal : ¬ task.IsGoalState task.init) :
    ¬ task.PlanExists := by
  rintro ⟨plan, s, hex, hgoal_s⟩
  cases hex with
  | nil => exact hgoal hgoal_s
  | cons hmem _ =>
    rw [hops] at hmem
    simp at hmem

end Cslib.Planning.Strips
