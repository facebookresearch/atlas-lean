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

public import CSLibExt.Scheduling.RealTime.EdfFeasibility
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
no-idle witness before the first overflow. Schedule computations are
checked by `decide`, rational utilization arithmetic by `simp`/`norm_num`,
and the consumer tests below exercise the EDF feasibility API directly.
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

/-- Single phased task `(4, 3)` at phase `5`. -/
def phasedUnit : TaskSet (Fin 1) := fun _ => ⟨4, 3, 5, by decide, by decide⟩

/-- Two phased tasks `(3, 5)` at phases `2` and `5`. -/
def phasedPair : TaskSet (Fin 2) := fun i =>
  match i.val with
  | 0 => ⟨3, 5, 2, by decide, by decide⟩
  | _ => ⟨3, 5, 5, by decide, by decide⟩

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

theorem boundary_maxPhase : maxPhase boundaryTasks = 0 := by
  decide

theorem phasedUnit_maxPhase : maxPhase phasedUnit = 5 := by
  decide

theorem phasedPair_maxPhase : maxPhase phasedPair = 5 := by
  decide

theorem boundary_inside_demand :
    (insideRequests boundaryTasks 0 6).sum (fun p => (boundaryTasks p.1).C) = 6 := by
  decide

theorem phasedUnit_inside_demand :
    (insideRequests phasedUnit 5 8).sum (fun p => (phasedUnit p.1).C) = 4 := by
  decide

theorem boundary_feasible :
    Feasible boundaryTasks (produceSchedule boundaryTasks (deadlineRule boundaryTasks)) := by
  apply (edf_feasible_iff_util_le_one _).mpr
  simp [boundary_utilization]

theorem overfull_not_feasible :
    ¬ Feasible overfullTasks (produceSchedule overfullTasks (deadlineRule overfullTasks)) := by
  rw [edf_feasible_iff_util_le_one, overfull_utilization]
  norm_num

theorem phasedUnit_utilization : utilization phasedUnit = 4 / 3 := by
  simp [utilization, phasedUnit]

theorem phasedPair_utilization : utilization phasedPair = 6 / 5 := by
  simp [utilization, phasedPair, Fin.sum_univ_two]
  norm_num

theorem phasedUnit_not_feasible :
    ¬ Feasible phasedUnit (produceSchedule phasedUnit (deadlineRule phasedUnit)) := by
  rw [edf_feasible_iff_util_le_one, phasedUnit_utilization]
  norm_num

theorem phasedPair_not_feasible :
    ¬ Feasible phasedPair (produceSchedule phasedPair (deadlineRule phasedPair)) := by
  rw [edf_feasible_iff_util_le_one, phasedPair_utilization]
  norm_num

theorem phasedUnit_firstOverflow :
    firstOverflow phasedUnit (produceSchedule phasedUnit (deadlineRule phasedUnit)) = some 8 := by
  rw [firstOverflow_eq_some_iff]
  constructor
  · refine ⟨0, 0, by decide, by decide⟩
  · intro s hs
    rintro ⟨i, k, hdead, _⟩
    have h8 : 8 ≤ deadline phasedUnit i k := by
      show 8 ≤ 5 + (k + 1) * 3
      omega
    omega

theorem phasedUnit_busy_window : ∀ s, windowStart phasedUnit 8 ≤ s → s < 8 →
    produceSchedule phasedUnit (deadlineRule phasedUnit) s ≠ none := by
  intro s hlo hhi
  exact edf_no_idle_before_overflow _ _ phasedUnit_firstOverflow s hlo hhi

theorem phasedUnit_window_served :
    (insideRequests phasedUnit (windowStart phasedUnit 8) 8).sum (fun p =>
        receivedWork phasedUnit
          (produceSchedule phasedUnit (deadlineRule phasedUnit)) p.1 p.2 8) =
      8 - windowStart phasedUnit 8 :=
  edf_window_served_eq_length _ _ phasedUnit_firstOverflow

end Cslib.Scheduling.RealTime
