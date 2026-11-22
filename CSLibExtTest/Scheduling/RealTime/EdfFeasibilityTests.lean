/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Tests for EDF feasibility
-/

module

public import CSLibExt.Scheduling.RealTime.PeriodicTasks
public import Mathlib.Algebra.BigOperators.Group.Finset.Defs
public import Mathlib.Data.Finset.Filter
public import Mathlib.Data.Finset.Image
public import Mathlib.Data.Finset.Max
public import Mathlib.Data.Finset.Union
public import Mathlib.Data.Fintype.Defs
public import Mathlib.Data.Rat.Defs
public import Mathlib.Order.Defs.LinearOrder
public import Mathlib.Order.Fin.Basic
public import Mathlib.Order.Interval.Finset.Nat

import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Tactic.NormNum

/-!
# Tests for EDF feasibility

Decidable checks of deadline-driven scheduling on concrete task sets:
utilization values, hyperperiod values, exact overflow slots, and the
no-idle witness before the first overflow. Proofs are deferred to Stage B
(`decide` for the schedule computations, `norm_num` for the rational
utilization arithmetic, which does not reduce by `decide`).
-/

@[expose] public section

namespace Cslib.Scheduling.RealTime

/-- Boundary task set: `(1, 2)`, `(1, 3)`, `(1, 6)` at phase `0`. -/
def boundaryTasks : TaskSet (Fin 3) := fun i =>
  match i.val with
  | 0 => ⟨1, 2, 0, by decide, by decide⟩
  | 1 => ⟨1, 3, 0, by decide, by decide⟩
  | _ => ⟨1, 6, 0, by decide, by decide⟩

/-- Overfull task set: `(2, 3)`, `(2, 4)` at phase `0`. -/
def overfullTasks : TaskSet (Fin 2) := fun i =>
  match i.val with
  | 0 => ⟨2, 3, 0, by decide, by decide⟩
  | _ => ⟨2, 4, 0, by decide, by decide⟩

/-- Single feasible task `(2, 5)` at phase `0`. -/
def singleFeasible : TaskSet (Fin 1) := fun _ => ⟨2, 5, 0, by decide, by decide⟩

/-- Single infeasible task `(4, 3)` at phase `0`. -/
def singleInfeasible : TaskSet (Fin 1) := fun _ => ⟨4, 3, 0, by decide, by decide⟩

theorem boundary_utilization : utilization boundaryTasks = 1 := by
  simp [utilization, boundaryTasks, Fin.sum_univ_three]
  norm_num

theorem boundary_hyperperiod : hyperperiod boundaryTasks = 6 := by
  decide

theorem boundary_no_overflow_before_hyperperiod :
    ∀ t ∈ Finset.range 6, ∀ i, ∀ k ∈ Finset.range 6,
      deadline boundaryTasks i k = t →
        (boundaryTasks i).C ≤
          receivedWork boundaryTasks
            (produceSchedule boundaryTasks (deadlineRule boundaryTasks)) i k t := by
  decide

theorem overfull_utilization : utilization overfullTasks = 7 / 6 := by
  simp [utilization, overfullTasks, Fin.sum_univ_two]
  norm_num

theorem overfull_hyperperiod : hyperperiod overfullTasks = 12 := by
  decide

theorem overfull_overflow_at_nine :
    deadline overfullTasks 0 2 = 9 ∧
      receivedWork overfullTasks
          (produceSchedule overfullTasks (deadlineRule overfullTasks)) 0 2 9 <
        (overfullTasks 0).C := by
  decide

theorem overfull_no_overflow_before_nine :
    ∀ t ∈ Finset.range 9, ∀ i, ∀ k ∈ Finset.range 9,
      deadline overfullTasks i k = t →
        (overfullTasks i).C ≤
          receivedWork overfullTasks
            (produceSchedule overfullTasks (deadlineRule overfullTasks)) i k t := by
  decide

theorem overfull_busy_before_nine :
    ∀ s ∈ Finset.range 9,
      produceSchedule overfullTasks (deadlineRule overfullTasks) s ≠ none := by
  decide

theorem single_feasible_hyperperiod : hyperperiod singleFeasible = 5 := by
  decide

theorem single_feasible_util : utilization singleFeasible ≤ 1 := by
  simp [utilization, singleFeasible]
  norm_num

theorem single_feasible_no_overflow :
    ∀ t ∈ Finset.range 6, ∀ i, ∀ k ∈ Finset.range 6,
      deadline singleFeasible i k = t →
        (singleFeasible i).C ≤
          receivedWork singleFeasible
            (produceSchedule singleFeasible (deadlineRule singleFeasible)) i k t := by
  decide

theorem single_infeasible_overflow_at_three :
    deadline singleInfeasible 0 0 = 3 ∧
      receivedWork singleInfeasible
          (produceSchedule singleInfeasible (deadlineRule singleInfeasible)) 0 0
            3 <
        (singleInfeasible 0).C := by
  decide

end Cslib.Scheduling.RealTime
