/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.Scheduling.SingleMachine.CompletionTime
public import Mathlib.Data.Fin.VecNotation
import Mathlib.Algebra.BigOperators.Fin

/-!
# Single-machine completion-time checks

Concrete consumers of `CSLibExt.Scheduling.SingleMachine.CompletionTime`: completion times along
a three-job schedule, a job missing from the list, a repeated job, the exchange identity on a
concrete swap, and the empty job type. Elaboration checks, not results.
-/

namespace CSLibExtTest.Scheduling.SingleMachine.CompletionTime

open Cslib.Scheduling.SingleMachine

/-- Processing times `3, 1, 2` of three jobs. -/
def p : Fin 3 → ℕ := ![3, 1, 2]

/-- Weights `1, 4, 2` of the three jobs. -/
def w : Fin 3 → ℕ := ![1, 4, 2]

example : IsSchedule [(1 : Fin 3), 2, 0] := ⟨by decide, by decide⟩

example : ¬ IsSchedule [(1 : Fin 3), 2] := fun h => by simpa using h.2 0

example : ¬ IsSchedule [(1 : Fin 3), 2, 0, 1] := fun h => by simpa using h.1

-- Jobs `1, 2, 0` finish at `1`, `1 + 2` and `1 + 2 + 3`.
example : completionTime p [1, 2, 0] 1 = 1 := by decide
example : completionTime p [1, 2, 0] 2 = 3 := by decide
example : completionTime p [1, 2, 0] 0 = 6 := by decide

-- A job missing from the list gets the sum over the whole list.
example : completionTime p [1, 2] 0 = 3 := by decide

-- A repeated job completes at its first occurrence.
example : completionTime p [0, 1, 0] 0 = 3 := by decide

example : totalWeightedCompletionTime p w [1, 2, 0] = 4 * 1 + 2 * 3 + 1 * 6 := by
  simp [totalWeightedCompletionTime, Fin.sum_univ_three, completionTime, p, w]

example : totalWeightedCompletionTime p w [0, 1, 2] = 1 * 3 + 4 * 4 + 2 * 6 := by
  simp [totalWeightedCompletionTime, Fin.sum_univ_three, completionTime, p, w]

-- Over a schedule the sum over all jobs is the sum along the list.
example : totalWeightedCompletionTime p w [1, 2, 0] =
    ([1, 2, 0].map fun j => w j * completionTime p [1, 2, 0] j).sum :=
  totalWeightedCompletionTime_eq_sum_map p w ⟨by decide, by decide⟩

-- Swapping the adjacent jobs `0` and `1` behind job `2`: `22 + 4 * 3 = 33 + 1 * 1`.
example : totalWeightedCompletionTime p w [2, 1, 0] + w 1 * p 0 =
    totalWeightedCompletionTime p w [2, 0, 1] + w 0 * p 1 :=
  totalWeightedCompletionTime_swap p w (l₁ := [2]) (l₂ := []) (by decide)

-- The empty list is the only schedule of no jobs, and its objective is `0`.
example : IsSchedule ([] : List Empty) := ⟨List.nodup_nil, fun j => j.elim⟩

example (p w : Empty → ℕ) : totalWeightedCompletionTime p w [] = 0 := by
  simp [totalWeightedCompletionTime]

end CSLibExtTest.Scheduling.SingleMachine.CompletionTime
