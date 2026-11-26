/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.Scheduling.SingleMachine.EarliestDueDate
public import Mathlib.Algebra.Order.Group.Int
public import Mathlib.Data.Fin.VecNotation
public import Mathlib.Data.Fintype.Basic

/-!
# Earliest-due-date checks

Concrete consumers of `CSLibExt.Scheduling.SingleMachine.EarliestDueDate`: the rule on three
integer jobs, two earliest-due-date schedules of jobs with equal due dates, the empty job type,
and a negative processing time for which the conclusion fails. Elaboration checks, not results.
-/

namespace CSLibExtTest.Scheduling.SingleMachine.EarliestDueDate

open Cslib.Scheduling.SingleMachine

/-- Processing times `3, 1, 2` of three jobs. -/
def p : Fin 3 → ℤ := ![3, 1, 2]

/-- Due dates `2, 6, 3` of the three jobs: the earliest-due-date order is `0, 2, 1`. -/
def d : Fin 3 → ℤ := ![2, 6, 3]

theorem p_nonneg : ∀ j, 0 ≤ p j := by decide

-- The schedule `0, 2, 1` has maximum lateness `2`, at most that of every schedule.
example {σ : List (Fin 3)} (hσ : IsSchedule σ) : ((2 : ℤ) : WithBot ℤ) ≤ maxLateness p d σ := by
  have h : maxLateness p d [0, 2, 1] = ((2 : ℤ) : WithBot ℤ) := by decide
  rw [← h]
  exact maxLateness_le_of_pairwise_dueDate_le p_nonneg hσ ⟨by decide, by decide⟩ (by decide)

-- Some schedule lists the jobs by nondecreasing due date.
example : ∃ τ : List (Fin 3), IsSchedule τ ∧ τ.Pairwise fun i j => d i ≤ d j :=
  exists_isSchedule_pairwise_dueDate_le d

-- Jobs `0` and `1` share a due date, so both orders are earliest-due-date schedules, and the
-- rule gives them the same maximum lateness.
example : maxLateness (![2, 5] : Fin 2 → ℤ) ![4, 4] [0, 1] =
    maxLateness (![2, 5] : Fin 2 → ℤ) ![4, 4] [1, 0] := by
  have hp : ∀ j, 0 ≤ (![2, 5] : Fin 2 → ℤ) j := by decide
  have h₀ : IsSchedule [(0 : Fin 2), 1] := ⟨by decide, by decide⟩
  have h₁ : IsSchedule [(1 : Fin 2), 0] := ⟨by decide, by decide⟩
  exact le_antisymm (maxLateness_le_of_pairwise_dueDate_le hp h₁ h₀ (by decide))
    (maxLateness_le_of_pairwise_dueDate_le hp h₀ h₁ (by decide))

-- No jobs: the empty schedule is an earliest-due-date schedule, with maximum lateness `⊥`.
example (p d : Fin 0 → ℤ) : maxLateness p d [] ≤ maxLateness p d [] :=
  maxLateness_le_of_pairwise_dueDate_le (fun j => j.elim0) ⟨List.nodup_nil, fun j => j.elim0⟩
    ⟨List.nodup_nil, fun j => j.elim0⟩ List.Pairwise.nil

-- Without nonnegative processing times the rule can fail: with processing times `0` and `-10`
-- and due dates `0` and `1`, the earliest-due-date schedule `0, 1` has maximum lateness `0` but
-- the schedule `1, 0` has maximum lateness `-10`.
example :
    ¬ maxLateness (![0, -10] : Fin 2 → ℤ) ![0, 1] [0, 1] ≤
      maxLateness (![0, -10] : Fin 2 → ℤ) ![0, 1] [1, 0] := by
  decide

end CSLibExtTest.Scheduling.SingleMachine.EarliestDueDate
