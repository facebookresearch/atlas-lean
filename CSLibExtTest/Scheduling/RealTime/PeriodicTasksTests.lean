/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.Scheduling.RealTime.PeriodicTasks
public import Mathlib.Order.Fin.Basic

/-!
# Tests for periodic tasks and fixed-priority preemptive schedules

Concrete task sets scheduled under rate-monotonic and deadline-driven
rules, checking produced-slot traces, overflow times and utilization.
-/

@[expose] public section

namespace Cslib.Scheduling.RealTime.Tests

open Cslib.Scheduling.RealTime

/-- Rate-monotonic rule: fixed priority by period; smaller period is urgent. -/
def rmRule {ι : Type*} [Fintype ι] (tasks : TaskSet ι) : PriorityRule ι ℕ :=
  fun i _ => (tasks i).T

/-- Tasks for T1 and T2: `(1, 2)` and `(1, 3)` with phases `0`. -/
def tasksT1 : TaskSet (Fin 2) :=
  fun i =>
    if i = 0 then ⟨1, 2, 0, by decide, by decide⟩
    else ⟨1, 3, 0, by decide, by decide⟩

theorem T1_trace_rm :
    let sched := produceSchedule tasksT1 (rmRule tasksT1)
    sched 0 = some 0 ∧
      sched 1 = some 1 ∧
      sched 2 = some 0 ∧
      sched 3 = some 1 ∧
      sched 4 = some 0 ∧
      sched 5 = none := by
  decide

theorem T1_no_overflow_rm :
    let sched := produceSchedule tasksT1 (rmRule tasksT1)
    ¬ RequestOverflow tasksT1 sched 0 0 ∧
      ¬ RequestOverflow tasksT1 sched 0 1 ∧
      ¬ RequestOverflow tasksT1 sched 0 2 ∧
      ¬ RequestOverflow tasksT1 sched 1 0 ∧
      ¬ RequestOverflow tasksT1 sched 1 1 := by
  decide

theorem T2_trace_edf :
    let sched := produceSchedule tasksT1 (deadlineRule tasksT1)
    sched 0 = some 0 ∧
      sched 1 = some 1 ∧
      sched 2 = some 0 ∧
      sched 3 = some 1 ∧
      sched 4 = some 0 ∧
      sched 5 = none := by
  decide

theorem T2_no_overflow_edf :
    let sched := produceSchedule tasksT1 (deadlineRule tasksT1)
    ¬ RequestOverflow tasksT1 sched 0 0 ∧
      ¬ RequestOverflow tasksT1 sched 0 1 ∧
      ¬ RequestOverflow tasksT1 sched 0 2 ∧
      ¬ RequestOverflow tasksT1 sched 1 0 ∧
      ¬ RequestOverflow tasksT1 sched 1 1 := by
  decide

/-- Tasks for T3: `(2, 3)` and `(2, 4)` with phases `0`. -/
def tasksT3 : TaskSet (Fin 2) :=
  fun i =>
    if i = 0 then ⟨2, 3, 0, by decide, by decide⟩
    else ⟨2, 4, 0, by decide, by decide⟩

theorem T3_rm_first_request_work :
    receivedWork tasksT3 (produceSchedule tasksT3 (rmRule tasksT3)) 1 0 4 =
      1 := by
  decide

theorem T3_rm_overflow_at_4 :
    OverflowAt tasksT3 (produceSchedule tasksT3 (rmRule tasksT3)) 4 := by
  exact ⟨1, 0, rfl, by decide⟩

theorem T3b_edf_trace :
    let sched := produceSchedule tasksT3 (deadlineRule tasksT3)
    sched 0 = some 0 ∧
      sched 1 = some 0 ∧
      sched 2 = some 1 ∧
      sched 3 = some 1 ∧
      sched 4 = some 0 ∧
      sched 5 = some 0 ∧
      sched 6 = some 1 ∧
      sched 7 = some 1 ∧
      sched 8 = some 0 := by
  decide

theorem T3b_edf_first_overflow_at_9 :
    let sched := produceSchedule tasksT3 (deadlineRule tasksT3)
    receivedWork tasksT3 sched 0 2 9 = 1 ∧
      OverflowAt tasksT3 sched 9 ∧
      ∀ t, t < 9 → ¬ OverflowAt tasksT3 sched t := by
  refine ⟨?_, ?_, ?_⟩
  · decide
  · exact ⟨0, 2, rfl, by decide⟩
  · intro t ht hov
    obtain ⟨i, k, hdead, hro⟩ := hov
    have hk9 : k < 9 := by
      by_cases hi : i = 0
      · have h := hdead
        simp [deadline, tasksT3, hi] at h
        omega
      · have h := hdead
        simp [deadline, tasksT3, hi] at h
        omega
    have hfin : ∀ i' : Fin 2, ∀ k' : Fin 9, ∀ t' : Fin 9,
        deadline tasksT3 i' k'.val = t'.val →
          ¬ RequestOverflow tasksT3
            (produceSchedule tasksT3 (deadlineRule tasksT3)) i' k'.val := by
      decide
    exact hfin i ⟨k, hk9⟩ ⟨t, ht⟩ hdead hro

theorem T4_slot_zero_runs_highest_priority {ι : Type*} {π : Type*} [Fintype ι] [LinearOrder ι]
    [LinearOrder π] [Nonempty ι] (tasks : TaskSet ι) (rule : PriorityRule ι π)
    (hphase : ∀ i, (tasks i).phase = 0) :
    ∃! i,
      produceSchedule tasks rule 0 = some i ∧
        ∀ j, rule i 0 < rule j 0 ∨ (rule i 0 = rule j 0 ∧ i ≤ j) := by
  have hrel : ∀ i, release tasks i 0 = 0 := by
    intro i
    simp [release, hphase i]
  have hdead : ∀ i, deadline tasks i 0 = (tasks i).T := by
    intro i
    simp [deadline, hphase i]
  have hrw : ∀ i, receivedWork tasks (produceSchedule tasks rule) i 0 0 = 0 := by
    intro i
    simp [receivedWork, hrel i]
  have hlive : ∀ i, IsLive tasks (produceSchedule tasks rule) i 0 0 := by
    intro i
    unfold IsLive
    rw [hrel i, hdead i, hrw i]
    exact ⟨le_rfl, (tasks i).hT, (tasks i).hC⟩
  have hcr : ∀ i, currentRequest tasks i 0 = some 0 := by
    intro i
    simp only [currentRequest, hphase i]
    rw [ite_eq_right (by decide : ¬ (0 : ℕ) < 0)]
    have h00 : ((0 : ℕ) - 0) / (tasks i).T = 0 := by
      have hsub : (0 : ℕ) - 0 = 0 := by decide
      rw [hsub]
      exact Nat.zero_div _
    rw [h00]
  obtain ⟨i0⟩ := ‹Nonempty ι›
  have hne : produceSchedule tasks rule 0 ≠ none := by
    intro hnone
    have hspec := (produceSchedule_spec tasks rule 0).1 hnone
    exact hspec ⟨i0, 0, hlive i0⟩
  obtain ⟨i, hi⟩ := Option.ne_none_iff_exists'.mp hne
  obtain ⟨k, hlk, hcrk, hmin'⟩ := (produceSchedule_spec tasks rule 0).2 i hi
  have hk0 : k = 0 := by
    have h0 := hcr i
    rw [hcrk] at h0
    exact Option.some_inj.mp h0
  subst hk0
  refine ⟨i, ⟨hi, ?_⟩, ?_⟩
  · intro j
    exact hmin' j 0 (hlive j)
  · intro i' hpair
    obtain ⟨hi', _⟩ := hpair
    exact (Option.some_inj.mp (hi.symm.trans hi')).symm

/-- Task for T5: a single task `(3, 2)` with phase `0`. -/
def tasksT5 : TaskSet (Fin 1) := fun _ => ⟨3, 2, 0, by decide, by decide⟩

theorem T5_first_request_bounded {π : Type*} [LinearOrder π]
    (rule : PriorityRule (Fin 1) π) :
    receivedWork tasksT5 (produceSchedule tasksT5 rule) 0 0 2 ≤ 2 := by
  have hrel : release tasksT5 0 0 = 0 := by decide
  have hdead : deadline tasksT5 0 0 = 2 := by decide
  have hmin : min 2 2 = 2 := by decide
  unfold receivedWork
  rw [hrel, hdead, hmin]
  refine le_trans (Finset.card_filter_le _ _) ?_
  decide

theorem T5_overflow_at_2 {π : Type*} [LinearOrder π] (rule : PriorityRule (Fin 1) π) :
    OverflowAt tasksT5 (produceSchedule tasksT5 rule) 2 := by
  have hle := T5_first_request_bounded rule
  have hlt :
      receivedWork tasksT5 (produceSchedule tasksT5 rule) 0 0 2 < 3 :=
    Nat.lt_of_le_of_lt hle (by decide)
  exact ⟨0, 0, rfl, hlt⟩

theorem T5_not_feasible {π : Type*} [LinearOrder π] (rule : PriorityRule (Fin 1) π) :
    ¬ Feasible tasksT5 (produceSchedule tasksT5 rule) := by
  intro h
  obtain ⟨i, k, _, hro⟩ := T5_overflow_at_2 rule
  exact h i k hro

theorem T5_utilization : utilization tasksT5 = 3 / 2 := by
  have huniv : (Finset.univ : Finset (Fin 1)) = {(0 : Fin 1)} := by
    apply Finset.ext
    intro a
    constructor
    · intro _
      exact Finset.mem_singleton.mpr (Fin.eq_zero a)
    · intro _
      exact Finset.mem_univ a
  simp only [utilization, huniv, Finset.sum, tasksT5]
  simp

theorem T3_rm_trace_30 :
    let sched := produceSchedule tasksT3 (rmRule tasksT3)
    sched 0 = some 0 ∧
      sched 1 = some 0 ∧
      sched 2 = some 1 ∧
      sched 3 = some 0 ∧
      sched 4 = some 0 ∧
      sched 5 = some 1 ∧
      sched 6 = some 0 ∧
      sched 7 = some 0 ∧
      sched 8 = some 1 ∧
      sched 9 = some 0 ∧
      sched 10 = some 0 ∧
      sched 11 = some 1 ∧
      sched 12 = some 0 ∧
      sched 13 = some 0 ∧
      sched 14 = some 1 ∧
      sched 15 = some 0 ∧
      sched 16 = some 0 ∧
      sched 17 = some 1 ∧
      sched 18 = some 0 ∧
      sched 19 = some 0 ∧
      sched 20 = some 1 ∧
      sched 21 = some 0 ∧
      sched 22 = some 0 ∧
      sched 23 = some 1 ∧
      sched 24 = some 0 ∧
      sched 25 = some 0 ∧
      sched 26 = some 1 ∧
      sched 27 = some 0 ∧
      sched 28 = some 0 ∧
      sched 29 = some 1 := by
  decide

end Cslib.Scheduling.RealTime.Tests
