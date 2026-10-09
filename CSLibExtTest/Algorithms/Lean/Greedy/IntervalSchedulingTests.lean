/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.Algorithms.Lean.Greedy.IntervalScheduling
import all CSLibExt.Algorithms.Lean.Greedy.IntervalScheduling
import all Cslib.Algorithms.Lean.Sort.Merge
import all Cslib.Algorithms.Lean.MergeSort.MergeSort
import all Init.Data.List.Sort.Basic

@[expose] public section

set_option autoImplicit false

namespace Cslib.Algorithms.Lean.TimeM

open scoped List

private structure Activity where
  id : Nat
  start : Nat
  finish : Nat
deriving DecidableEq

private def activity (id start finish : Nat) : Activity :=
  { id, start, finish }

private def touching : List Activity :=
  [activity 2 1 2, activity 1 0 1]

private def chain : List Activity :=
  [activity 3 2 3, activity 1 0 1, activity 4 3 4, activity 2 1 2]

private def nested : List Activity :=
  [activity 1 0 10, activity 2 1 2, activity 3 2 3]

private def earliestStartCounterexample : List Activity :=
  [activity 1 0 10, activity 2 1 2, activity 3 2 3, activity 4 3 4]

private def clrsActivities : List Activity :=
  [ activity 8 8 11,
    activity 3 0 6,
    activity 11 12 16,
    activity 5 3 9,
    activity 1 1 4,
    activity 10 2 14,
    activity 7 6 10,
    activity 4 5 7,
    activity 9 8 12,
    activity 2 3 5,
    activity 6 5 9 ]

private def equalFinish : List Activity :=
  [activity 1 0 3, activity 2 1 3, activity 3 3 4]

private def repeated : List Activity :=
  [activity 1 0 2, activity 2 0 2, activity 3 0 2]

private def incompatible : List Activity :=
  [activity 1 0 5, activity 2 1 4, activity 3 2 3]

example :
      (intervalSchedule Activity.start Activity.finish ([] : List Activity)).ret = [] := by
  simp [intervalSchedule, List.finRange]

example :
    (intervalSchedule Activity.start Activity.finish ([] : List Activity)).time = 0 := by
  simp [intervalSchedule, List.finRange]

example :
    (intervalSchedule Activity.start Activity.finish [activity 1 2 5]).ret =
      [activity 1 2 5] := by
  simp [intervalSchedule, List.finRange, intervalSchedule.scan]

example :
    (intervalSchedule Activity.start Activity.finish [activity 1 2 5]).time = 0 := by
  simp [intervalSchedule, List.finRange, intervalSchedule.scan]

example :
    (intervalSchedule Activity.start Activity.finish touching).ret =
      [activity 1 0 1, activity 2 1 2] := by
  simp [intervalSchedule, List.finRange, List.mergeSort, intervalSchedule.scan, touching, activity]

example :
    (intervalSchedule Activity.start Activity.finish chain).ret =
      [activity 1 0 1, activity 2 1 2, activity 3 2 3, activity 4 3 4] := by
  simp [intervalSchedule, List.finRange, List.mergeSort, intervalSchedule.scan, chain, activity]

example :
    (intervalSchedule Activity.start Activity.finish nested).ret =
      [activity 2 1 2, activity 3 2 3] := by
  simp [intervalSchedule, List.finRange, List.mergeSort, intervalSchedule.scan, nested, activity]

example :
    (intervalSchedule Activity.start Activity.finish earliestStartCounterexample).ret =
      [activity 2 1 2, activity 3 2 3, activity 4 3 4] := by
  simp [intervalSchedule, List.finRange, List.mergeSort, intervalSchedule.scan,
    earliestStartCounterexample, activity]

example :
    (intervalSchedule Activity.start Activity.finish clrsActivities).ret.length = 4 := by
  simp [intervalSchedule, List.finRange, List.mergeSort, intervalSchedule.scan, clrsActivities,
    activity]

example :
    List.Pairwise (IntervalCompatible Activity.start Activity.finish)
      (intervalSchedule Activity.start Activity.finish clrsActivities).ret :=
  (intervalSchedule_correct Activity.start Activity.finish clrsActivities (by decide)).2.1

example (ys : List Activity)
    (hsub : ys <+~ clrsActivities)
    (hfeasible : List.Pairwise (IntervalCompatible Activity.start Activity.finish) ys) :
    ys.length ≤
      (intervalSchedule Activity.start Activity.finish clrsActivities).ret.length :=
  (intervalSchedule_correct Activity.start Activity.finish clrsActivities (by decide)).2.2
    ys hsub hfeasible

example :
    (intervalSchedule Activity.start Activity.finish equalFinish).ret.length = 2 := by
  simp [intervalSchedule, List.finRange, List.mergeSort, intervalSchedule.scan, equalFinish,
    activity]

example :
    List.Pairwise (IntervalCompatible Activity.start Activity.finish)
      (intervalSchedule Activity.start Activity.finish equalFinish).ret :=
  (intervalSchedule_correct Activity.start Activity.finish equalFinish (by decide)).2.1

example :
    (intervalSchedule Activity.start Activity.finish repeated).ret.length = 1 := by
  simp [intervalSchedule, List.finRange, List.mergeSort, intervalSchedule.scan, repeated, activity]

example :
    (intervalSchedule Activity.start Activity.finish incompatible).ret.length = 1 := by
  simp [intervalSchedule, List.finRange, List.mergeSort, intervalSchedule.scan, incompatible,
    activity]

example :
    (intervalSchedule Activity.start Activity.finish chain).ret.length = chain.length := by
  simp [intervalSchedule, List.finRange, List.mergeSort, intervalSchedule.scan, chain, activity]

-- Identical values are separate input occurrences, not a finite set of activities.
example : (intervalSchedule id (fun a : Nat => a + 1) [0, 0, 1]).ret = [0, 1] := by
  simp [intervalSchedule, List.finRange, List.mergeSort, intervalSchedule.scan]

example : (intervalSchedule id (fun a : Nat => a + 1) [0, 0, 1]).ret.Subperm [0, 0, 1] :=
  (intervalSchedule_correct id (fun a : Nat => a + 1) [0, 0, 1] (by decide)).1

example : (intervalSchedule Activity.start Activity.finish touching).time = 2 := by
  simp [intervalSchedule, List.finRange, List.mergeSortM, intervalSchedule.scan, touching, activity]

-- The endpoint contract does not restrict activities to nonnegative times.
example : (intervalSchedule id (fun a : Int => a + 1) [-1, -3, -2]).ret = [-3, -2, -1] := by
  simp [intervalSchedule, List.finRange, List.mergeSort, intervalSchedule.scan]

example :
    ¬(∀ a ∈ [activity 1 2 2], Activity.start a < Activity.finish a) := by
  decide

example :
    ¬(∀ a ∈ [activity 1 3 2], Activity.start a < Activity.finish a) := by
  decide

example (a b : Activity)
    (h : IntervalCompatible Activity.start Activity.finish a b) :
    IntervalCompatible Activity.start Activity.finish b a :=
  h.symm

example (xs : List Activity) :
    (intervalSchedule Activity.start Activity.finish xs).time ≤
      xs.length * Nat.clog 2 xs.length + (xs.length - 1) :=
  intervalSchedule_time Activity.start Activity.finish xs

universe u v

example {ι : Type u} {τ : Type v} [LinearOrder τ]
    (start finish : ι → τ) (xs : List ι) : TimeM Nat (List ι) :=
  intervalSchedule start finish xs

example {ι : Type u} {τ : Type v} [LinearOrder τ]
    (start finish : ι → τ) (xs : List ι)
    (hproper : ∀ a ∈ xs, start a < finish a) :
    (intervalSchedule start finish xs).ret <+~ xs ∧
      List.Pairwise (IntervalCompatible start finish)
        (intervalSchedule start finish xs).ret ∧
      ∀ ys, ys <+~ xs →
        List.Pairwise (IntervalCompatible start finish) ys →
        ys.length ≤ (intervalSchedule start finish xs).ret.length :=
  intervalSchedule_correct start finish xs hproper

end Cslib.Algorithms.Lean.TimeM
