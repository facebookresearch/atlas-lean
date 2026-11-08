/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.Algorithms.Lean.DataStructures.BinaryHeap.Cost

/-!
# Imported sift-up cost clients

Generic clients exercise the public bounds; concrete examples check actual branch counts.
-/

public section

set_option autoImplicit false

namespace Cslib.Algorithms.Lean.BinaryHeapCostTests

theorem ret_refinement {α : Type} [LinearOrder α] (a : Array α) (i : Nat) :
    (TimeM.siftUp a i).ret = Cslib.Algorithms.Lean.siftUp a i :=
  TimeM.ret_siftUp a i

theorem comparison_bound {α : Type} [LinearOrder α] (a : Array α) (i : Nat) :
    (TimeM.siftUp a i).time.1 ≤ Nat.log2 (i + 1) :=
  TimeM.comparisons_siftUp_le_log2 a i

theorem swap_bound {α : Type} [LinearOrder α] (a : Array α) (i : Nat) :
    (TimeM.siftUp a i).time.2 ≤ Nat.log2 (i + 1) :=
  TimeM.swaps_siftUp_le_log2 a i

theorem event_bound {α : Type} [LinearOrder α] (a : Array α) (i : Nat) :
    (TimeM.siftUp a i).time.1 + (TimeM.siftUp a i).time.2 ≤ 2 * Nat.log2 (i + 1) :=
  TimeM.events_siftUp_le_log2 a i

theorem parent_depth (i : Nat) (hi : 0 < i) :
    Nat.log2 (heapParent i + 1) + 1 = Nat.log2 (i + 1) :=
  log2_heapParent_add_one i hi

theorem root_zero {α : Type} [LinearOrder α] (a : Array α) :
    (TimeM.siftUp a 0).time = (0, 0) :=
  TimeM.time_siftUp_zero a

theorem invalid_zero {α : Type} [LinearOrder α] (a : Array α) (i : Nat) (hi : a.size ≤ i) :
    (TimeM.siftUp a i).time = (0, 0) :=
  TimeM.time_siftUp_of_size_le a i hi

theorem empty_cost : (TimeM.siftUp (#[] : Array Nat) 0).time = (0, 0) := by
  decide +kernel

theorem singleton_root_cost : (TimeM.siftUp #[4] 0).time = (0, 0) := by
  decide +kernel

theorem invalid_cost : (TimeM.siftUp #[4] 1).time = (0, 0) := by
  decide +kernel

theorem no_swap_cost : (TimeM.siftUp #[1, 4, 3, 7] 3).time = (1, 0) := by
  decide +kernel

theorem early_stop_cost : (TimeM.siftUp #[1, 4, 3, 2] 3).time = (2, 1) := by
  decide +kernel

theorem full_height_cost : (TimeM.siftUp #[1, 4, 3, 0] 3).time = (2, 2) := by
  decide +kernel

theorem duplicate_cost : (TimeM.siftUp #[1, 1, 1, 1] 3).time = (1, 0) := by
  decide +kernel

end Cslib.Algorithms.Lean.BinaryHeapCostTests
