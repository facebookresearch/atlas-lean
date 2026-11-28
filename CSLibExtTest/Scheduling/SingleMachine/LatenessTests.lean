/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.Scheduling.SingleMachine.Lateness
public import Mathlib.Algebra.Order.Group.Int
public import Mathlib.Basic.Real.Basic
public import Mathlib.Data.Fin.VecNotation
public import Mathlib.Data.Fintype.Basic
import Mathlib.Tactic.NormNum

/-!
# Maximum-lateness checks

Concrete consumers of `CSLibExt.Scheduling.SingleMachine.Lateness`: the maximum lateness of three
integer jobs in two orders, a job missing from the list, a repeated job, negative lateness, the
empty job type, and real data. Elaboration checks, not results.
-/

namespace CSLibExtTest.Scheduling.SingleMachine.Lateness

open Cslib.Scheduling.SingleMachine

/-- Processing times `3, 1, 2` of three jobs. -/
def p : Fin 3 → ℤ := ![3, 1, 2]

/-- Due dates `2, 6, 3` of the three jobs. -/
def d : Fin 3 → ℤ := ![2, 6, 3]

-- In the order `0, 2, 1` the jobs complete at `3`, `5` and `6`, with latenesses `3 - 2`, `5 - 3`
-- and `6 - 6`: the maximum is `2`.
example : maxLateness p d [0, 2, 1] = ((2 : ℤ) : WithBot ℤ) := by decide

-- In the order `1, 0, 2` the latenesses are `1 - 6`, `4 - 2` and `6 - 3`: the maximum is `3`.
example : maxLateness p d [1, 0, 2] = ((3 : ℤ) : WithBot ℤ) := by decide

-- A job missing from the list counts too, completing at the list's total processing time `5`.
-- With due dates `2, 0, 3` its lateness `5 - 0` is the maximum, while the listed jobs alone would
-- give `2`.
example : maxLateness p ![2, 0, 3] [0, 2] = ((5 : ℤ) : WithBot ℤ) := by decide

-- A repeated job completes at its first occurrence: in the list `0, 0, 2` job `0` completes at `3`
-- and job `2` at `3 + 3 + 2 = 8`, as does the missing job `1`. With due dates `0, 9, 4` the
-- latenesses are `3`, `-1` and `4`, so the maximum is `4`; completing job `0` at its last
-- occurrence, `6`, would give `6`.
example : maxLateness p ![0, 9, 4] [0, 0, 2] = ((4 : ℤ) : WithBot ℤ) := by decide

-- With late due dates every job is early, and the maximum lateness is negative.
example : maxLateness p (fun _ => 10) [0, 2, 1] = ((-4 : ℤ) : WithBot ℤ) := by decide

-- The lateness of each job is at most the maximum.
example (j : Fin 3) : ((completionTime p [0, 2, 1] j - d j : ℤ) : WithBot ℤ) ≤
    maxLateness p d [0, 2, 1] :=
  le_maxLateness p d [0, 2, 1] j

-- The maximum over no jobs is `⊥`, below every value.
example (p d : Fin 0 → ℤ) : maxLateness p d [] = ⊥ := maxLateness_of_isEmpty p d []

example (p d : Fin 0 → ℤ) : maxLateness p d [] < ((-100 : ℤ) : WithBot ℤ) := by
  rw [maxLateness_of_isEmpty]
  exact WithBot.bot_lt_coe _

-- Real processing times and due dates.
example : maxLateness (fun _ : Fin 1 => (1 / 2 : ℝ)) (fun _ => 1) [0] =
    ((-1 / 2 : ℝ) : WithBot ℝ) := by
  norm_num [maxLateness, completionTime]

end CSLibExtTest.Scheduling.SingleMachine.Lateness
