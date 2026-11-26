/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import CSLibExt.Algorithms.Lean.Sort.BottomUpHeap
meta import CSLibExt.Algorithms.Lean.Sort.BottomUpHeap
import CSLibExt.Algorithms.Lean.Sort.Heap

/-! # Tests for heapsort with bottom-up heap construction

Concrete runs check boundary inputs, duplicates and the comparison counter. The examples
exercise the public theorems from an importing module and compare the output with heap sort by
repeated insertion.
-/

set_option autoImplicit false

open Cslib.Algorithms.Lean

#guard bottomUpHeapSort ([] : List Nat) == []
#guard bottomUpHeapSort [7] == [7]
#guard bottomUpHeapSort [3, 1, 3, 2, 1] == [1, 1, 2, 3, 3]
#guard bottomUpHeapSort [5, 4, 3, 2, 1] == [1, 2, 3, 4, 5]
#guard bottomUpHeapSort [1, 2, 3, 4, 5, 6, 7] == [1, 2, 3, 4, 5, 6, 7]

#guard (TimeM.bottomUpHeapSort ([] : List Nat)).time == (0, 0)
#guard (TimeM.bottomUpHeapSort [7]).time == (0, 1)
#guard (TimeM.bottomUpHeapSort [5, 4, 3, 2, 1]).ret == [1, 2, 3, 4, 5]
-- The comparison bound `2 n (⌊log₂ n⌋ + 1)` on a few inputs of each length up to twelve.
#guard (List.range 13).all fun n =>
  [List.range n, (List.range n).reverse, (List.range n).map (· % 3)].all fun xs =>
    (TimeM.bottomUpHeapSort xs).time.1 ≤ 2 * n * (Nat.log 2 n + 1)

section
variable {α : Type} [LinearOrder α] (xs : List α)

example : (TimeM.bottomUpHeapSort xs).ret = bottomUpHeapSort xs :=
  TimeM.ret_bottomUpHeapSort xs

example : List.Pairwise (· ≤ ·) (bottomUpHeapSort xs) ∧ (bottomUpHeapSort xs).Perm xs :=
  bottomUpHeapSort_correct xs

example : (TimeM.bottomUpHeapSort xs).time.1 ≤ 2 * xs.length * (Nat.log 2 xs.length + 1) :=
  (TimeM.bottomUpHeapSort_correct_comparisons_le xs).2.2

-- Both heapsorts return the unique sorted permutation of their input.
example : bottomUpHeapSort xs = heapSort xs :=
  ((bottomUpHeapSort_correct xs).2.trans (heapSort_perm xs).symm).eq_of_pairwise
    (fun _ _ _ _ hab hba => le_antisymm hab hba) (bottomUpHeapSort_correct xs).1
    (heapSort_sorted xs)
end

#print axioms bottomUpHeapSort_correct
#print axioms TimeM.ret_bottomUpHeapSort
#print axioms TimeM.bottomUpHeapSort_correct_comparisons_le
