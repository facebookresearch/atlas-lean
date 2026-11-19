/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.Algorithms.Lean.DataStructures.BraunTree.Sorting

/-!
# Sorting API tests

The time bounds and `O(n log n)` theorems applied to concrete
inputs, and the `heapify` API (`heapify_snd`, `heapify_correct`,
`braun_heapify`, `heap_heapify`, `mset_heapify`) on examples.
All are theorem applications: no computation is needed.
-/

@[expose] public section

set_option autoImplicit false

namespace Cslib.Algorithms.Lean.BraunTree.SortingAPITests

open BraunTree
open BraunTree.Sorting
open BraunTree.Complete

/-- `t_heap_of_A` bound on `[3, 1, 2]`. -/
example : T_heapOfA [3, 1, 2] ≤ [3, 1, 2].length * (height (heapOfA [3, 1, 2]) + 1) :=
  T_heapOfA_bound _

/-- `t_heap_of_A` log bound on `[3, 1, 2]`. -/
example : T_heapOfA [3, 1, 2] ≤ [3, 1, 2].length * (nlog2 ([3, 1, 2].length + 1) + 1) :=
  T_heapOfA_log_bound _

/-- `t_list_of_A` bound on a small heap. -/
example : tListOfA (heapOfA [3, 1, 2]) ≤
    2 * height (heapOfA [3, 1, 2]) * size (heapOfA [3, 1, 2]) :=
  tListOfA_bound _

/-- `t_sortA`: `O(n log n)` for Algorithm A on `[3, 1, 2]`. -/
example : T_heapOfA [3, 1, 2] + tListOfA (heapOfA [3, 1, 2]) ≤
    3 * [3, 1, 2].length * (nlog2 ([3, 1, 2].length + 1) + 1) :=
  t_sortA _

/-- `t_heap_of_B` bound on `[3, 1, 2]`. -/
example : T_heapOfB [3, 1, 2] ≤ 6 * [3, 1, 2].length + 1 :=
  tHeapOfB_bound _

/-- `t_sortB`: `O(n log n)` for Algorithm B on `[3, 1, 2]`. -/
example : T_heapOfB [3, 1, 2] + tListOfB' (heapOfB [3, 1, 2]) ≤
    3 * [3, 1, 2].length * (nlog2 ([3, 1, 2].length + 1) + 3) + 1 :=
  t_sortB _

/-- `t_list_of_B` log bound on a small heap. -/
example : tListOfB' (heapOfB [3, 1, 2]) ≤
    3 * (nlog2 (size (heapOfB [3, 1, 2]) + 1) + 1) * size (heapOfB [3, 1, 2]) :=
  tListOfB_log_bound _ (braun_heapify (le_refl _))

/-- `heapify_snd` on an example. -/
example : (heapify 2 [5, 1, 4, 2]).2 = [5, 1, 4, 2].drop 2 :=
  heapify_snd 2 _ (by decide)

/-- `heapify_correct` on an example: size, heap, Braun, multiset. -/
example : size (heapify 2 [5, 1, 4, 2]).1 = 2 ∧
    Heap (heapify 2 [5, 1, 4, 2]).1 ∧ Braun (heapify 2 [5, 1, 4, 2]).1 ∧
    msetTree (heapify 2 [5, 1, 4, 2]).1 = (([5, 1] : List Nat) : Multiset Nat) := by
  obtain ⟨h1, h2, h3, h4⟩ := heapify_correct 2 [5, 1, 4, 2] (by decide)
    (heapify 2 [5, 1, 4, 2]).1 (heapify 2 [5, 1, 4, 2]).2 rfl
  refine ⟨h1, h2, h3, ?_⟩
  rw [h4]
  rfl

/-- `t_heapify` bound on an example. -/
example : tHeapify 2 [5, 1, 4, 2] ≤ 5 * 2 + 1 :=
  t_heapify_bound (by decide)

end Cslib.Algorithms.Lean.BraunTree.SortingAPITests
