/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.Algorithms.Lean.Approximation.ListScheduling
public meta import CSLibExt.Algorithms.Lean.Approximation.ListScheduling
import Mathlib.Algebra.BigOperators.Fin

/-!
# List scheduling and LPT tests

Executed fixtures check makespans, machine contents and costs on Graham's tight instances: for
`m = 3`, LPT on `5, 5, 4, 4, 3, 3, 3` has makespan `11 = 4m - 1` against the optimum `9 = 3m`,
and list scheduling of six unit jobs followed by a job of length `3` has makespan `5 = 2m - 1`
against `3 = m`. The bound theorems are instantiated on those instances with explicit optimal
schedules, so both ratios are attained exactly.
-/

set_option autoImplicit false

namespace Cslib.Algorithms.Lean.Scheduling

open Cslib.Algorithms.Lean.TimeM

private meta def machines {m : ℕ} (σ : Fin m → List ℕ) : List (List ℕ) :=
  (List.finRange m).map σ

private meta def checkLS (label : String) (m : ℕ) [NeZero m] (ps : List ℕ)
    (expected : ℕ) (cost : ℕ) : IO Unit := do
  let r := listSchedule m ps
  unless makespan r.ret == expected && r.time == cost do
    throw (IO.userError s!"{label}: makespan {makespan r.ret}, cost {r.time}")
  IO.println s!"{label}: {machines r.ret}, makespan {makespan r.ret}, cost {r.time}"

private meta def checkLPT (label : String) (m : ℕ) [NeZero m] (ps : List ℕ)
    (expected : ℕ) : IO Unit := do
  let r := lpt m ps
  unless makespan r.ret == expected do
    throw (IO.userError s!"{label}: makespan {makespan r.ret}")
  IO.println s!"{label}: {machines r.ret}, makespan {makespan r.ret}, cost {r.time}"

#eval checkLS "no jobs" 3 [] 0 0
#eval checkLS "one machine" 1 [4, 2, 7] 13 3
#eval checkLS "Graham 1966 tight, m = 3" 3 [1, 1, 1, 1, 1, 1, 3] 5 21
#eval checkLS "longest last, m = 2" 2 [1, 1, 2] 3 6
#eval checkLPT "LPT fixes the 1966 instance" 3 [1, 1, 1, 1, 1, 1, 3] 3
#eval checkLPT "Graham 1969 tight, m = 3" 3 [5, 5, 4, 4, 3, 3, 3] 11
#eval checkLPT "Graham 1969 tight, shuffled" 3 [3, 4, 5, 3, 4, 3, 5] 11
#eval checkLPT "Graham 1969 tight, m = 2" 2 [3, 3, 2, 2, 2] 7
#eval checkLPT "no jobs" 2 [] 0
#eval checkLPT "zero-length jobs" 2 [0, 0, 5] 5

/-- An optimal schedule for `5, 5, 4, 4, 3, 3, 3` on three machines, of makespan `9`. -/
private def opt1969 : Fin 3 → List ℕ := fun i => [[5, 4], [5, 4], [3, 3, 3]].getD i.val []

private theorem opt1969_isScheduleOf : IsScheduleOf opt1969 [5, 5, 4, 4, 3, 3, 3] := by
  unfold IsScheduleOf
  simp only [Fin.sum_univ_succ, Finset.univ_eq_empty, Finset.sum_empty, add_zero,
    Multiset.coe_add]
  exact Multiset.coe_eq_coe.2 (by decide)

example : makespan opt1969 = 9 := by decide +kernel

/-- LPT attains Graham's `(4m - 1) / (3m)` bound with equality here: `3 * 3 * 11 = 11 * 9`. -/
example : 3 * 3 * makespan (lpt 3 [5, 5, 4, 4, 3, 3, 3]).ret ≤ (4 * 3 - 1) * makespan opt1969 :=
  lpt_approx _ _ opt1969_isScheduleOf

/-- An optimal schedule for six unit jobs and a job of length `3`, of makespan `3`. -/
private def opt1966 : Fin 3 → List ℕ := fun i => [[3], [1, 1, 1], [1, 1, 1]].getD i.val []

private theorem opt1966_isScheduleOf : IsScheduleOf opt1966 [1, 1, 1, 1, 1, 1, 3] := by
  unfold IsScheduleOf
  simp only [Fin.sum_univ_succ, Finset.univ_eq_empty, Finset.sum_empty, add_zero,
    Multiset.coe_add]
  exact Multiset.coe_eq_coe.2 (by decide)

example : 3 * makespan (listSchedule 3 [1, 1, 1, 1, 1, 1, 3]).ret ≤
    (2 * 3 - 1) * makespan opt1966 :=
  listSchedule_approx _ _ opt1966_isScheduleOf

example : IsScheduleOf (lpt 3 [5, 5, 4, 4, 3, 3, 3]).ret [5, 5, 4, 4, 3, 3, 3] :=
  lpt_isScheduleOf _

example (m : ℕ) [NeZero m] (ps : List ℕ) : (listSchedule m ps).time = ps.length * m :=
  listSchedule_time ps

example (m : ℕ) [NeZero m] (ps : List ℕ) :
    (lpt m ps).time ≤ ps.length * Nat.clog 2 ps.length + ps.length * m :=
  lpt_time_le ps

#print axioms listSchedule
#print axioms lpt
#print axioms listSchedule_approx
#print axioms lpt_approx
#print axioms listSchedule_isScheduleOf
#print axioms lpt_isScheduleOf
#print axioms listSchedule_time
#print axioms lpt_time_le

end Cslib.Algorithms.Lean.Scheduling
