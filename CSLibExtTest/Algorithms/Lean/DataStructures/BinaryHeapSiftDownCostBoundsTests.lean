/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import CSLibExt.Algorithms.Lean.DataStructures.BinaryHeap.SiftDownCost

open Cslib.Algorithms.Lean

section
variable {α : Type} [LinearOrder α] (a : Array α) (i : Nat)

example : (TimeM.siftDown a i).ret = siftDown a i := TimeM.ret_siftDown a i
example : (TimeM.siftDown a i).time.1 ≤
    2 * (Nat.log2 a.size - Nat.log2 (i + 1)) := TimeM.siftDown_comparisons_le a i
example : (TimeM.siftDown a i).time.2 ≤
    Nat.log2 a.size - Nat.log2 (i + 1) := TimeM.siftDown_swaps_le a i
example : (TimeM.siftDown a i).time.1 + (TimeM.siftDown a i).time.2 ≤
    3 * (Nat.log2 a.size - Nat.log2 (i + 1)) := TimeM.siftDown_time_le a i
example (h : a.size ≤ heapLeft i) : (TimeM.siftDown a i).time = (0, 0) :=
  TimeM.time_siftDown_of_heapLeft_ge a i h
example (h : a.size ≤ i) : (TimeM.siftDown a i).time = (0, 0) :=
  TimeM.time_siftDown_of_size_le a i h
end

#print axioms log2_smallerChild_add_one
#print axioms log2_smallerChild_le_size
#print axioms TimeM.ret_timedSmallerChild
#print axioms TimeM.ret_siftDown
#print axioms TimeM.time_timedSmallerChild
#print axioms TimeM.time_timedSmallerChild_of_none
#print axioms TimeM.siftDown_swaps_le
#print axioms TimeM.siftDown_comparisons_le
#print axioms TimeM.siftDown_time_le
#print axioms TimeM.time_siftDown_of_smallerChild_none
#print axioms TimeM.time_siftDown_of_heapLeft_ge
#print axioms TimeM.time_siftDown_of_size_le
