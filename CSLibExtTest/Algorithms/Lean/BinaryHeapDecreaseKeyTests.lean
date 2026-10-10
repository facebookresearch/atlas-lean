/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.Algorithms.Lean.DataStructures.BinaryHeap.DecreaseKey
public meta import CSLibExt.Algorithms.Lean.DataStructures.BinaryHeap.DecreaseKey

/-!
# Runtime tests for binary-heap decrease-key
-/

public section

namespace Cslib.Algorithms.Lean.BinaryHeapDecreaseKeyTests

set_option autoImplicit false

def singleton : MinHeap Nat := MinHeap.empty.push 4

def base : MinHeap Nat :=
  MinHeap.empty.push 1 |>.push 4 |>.push 2 |>.push 7 |>.push 8 |>.push 9 |>.push 6

def duplicateBase : MinHeap Nat :=
  MinHeap.empty.push 1 |>.push 2 |>.push 1 |>.push 3 |>.push 2 |>.push 4 |>.push 2

theorem singleton_data_before : singleton.data = #[4] := by
  simp [singleton, MinHeap.push, MinHeap.empty, siftUp]

theorem base_data_before : base.data = #[1, 4, 2, 7, 8, 9, 6] := by
  simp [base, MinHeap.push, MinHeap.empty, siftUp, heapParent]

theorem duplicate_data_before : duplicateBase.data = #[1, 2, 1, 3, 2, 4, 2] := by
  simp [duplicateBase, MinHeap.push, MinHeap.empty, siftUp, heapParent]

def singletonDecrease : MinHeap Nat :=
  singleton.decreaseKey ⟨0, by simp [singleton_data_before]⟩ 2 (by
    simp [singleton_data_before])

def equalDecrease : MinHeap Nat :=
  base.decreaseKey ⟨4, by simp [base_data_before]⟩ 8 (by simp [base_data_before])

def noSwapDecrease : MinHeap Nat :=
  base.decreaseKey ⟨3, by simp [base_data_before]⟩ 5 (by simp [base_data_before])

def oneSwapDecrease : MinHeap Nat :=
  base.decreaseKey ⟨3, by simp [base_data_before]⟩ 3 (by simp [base_data_before])

def severalSwapDecrease : MinHeap Nat :=
  base.decreaseKey ⟨6, by simp [base_data_before]⟩ 0 (by simp [base_data_before])

def duplicateDecrease : MinHeap Nat :=
  duplicateBase.decreaseKey ⟨6, by simp [duplicate_data_before]⟩ 1 (by
    simp [duplicate_data_before])

theorem singleton_data : singletonDecrease.data.toList = [2] := by
  simp [singletonDecrease, MinHeap.decreaseKey, singleton_data_before, siftUp]

theorem singleton_min : singletonDecrease.min? = some 2 := by
  simp [singletonDecrease, MinHeap.decreaseKey, MinHeap.min?, singleton_data_before,
    siftUp]

theorem equal_data : equalDecrease.data.toList = [1, 4, 2, 7, 8, 9, 6] := by
  simp [equalDecrease, MinHeap.decreaseKey, base_data_before, siftUp, heapParent]

theorem equal_elements : equalDecrease.elements = base.elements := by
  simp [equalDecrease, MinHeap.decreaseKey, MinHeap.elements, base_data_before, siftUp,
    heapParent]

theorem no_swap_data : noSwapDecrease.data.toList = [1, 4, 2, 5, 8, 9, 6] := by
  simp [noSwapDecrease, MinHeap.decreaseKey, base_data_before, siftUp, heapParent]

theorem one_swap_data : oneSwapDecrease.data.toList = [1, 3, 2, 4, 8, 9, 6] := by
  simp [oneSwapDecrease, MinHeap.decreaseKey, base_data_before, siftUp, heapParent]

theorem several_swaps_data :
    severalSwapDecrease.data.toList = [0, 4, 1, 7, 8, 9, 2] := by
  simp [severalSwapDecrease, MinHeap.decreaseKey, base_data_before, siftUp, heapParent]

theorem several_swaps_size : severalSwapDecrease.data.size = base.data.size := by
  exact base.decreaseKey_size ⟨6, by simp [base_data_before]⟩ 0 (by
    simp [base_data_before])

theorem several_swaps_min : severalSwapDecrease.min? = some 0 := by
  simp [severalSwapDecrease, MinHeap.decreaseKey, MinHeap.min?, base_data_before,
    siftUp, heapParent]

theorem duplicate_data :
    duplicateDecrease.data.toList = [1, 2, 1, 3, 2, 4, 1] := by
  simp [duplicateDecrease, MinHeap.decreaseKey, duplicate_data_before, siftUp,
    heapParent]

theorem duplicate_old_count :
    Multiset.count 2 duplicateDecrease.elements = 2 := by
  simp [duplicateDecrease, MinHeap.decreaseKey, MinHeap.elements, duplicate_data_before,
    siftUp, heapParent]

theorem duplicate_new_count :
    Multiset.count 1 duplicateDecrease.elements = 3 := by
  simp [duplicateDecrease, MinHeap.decreaseKey, MinHeap.elements, duplicate_data_before,
    siftUp, heapParent]

theorem duplicate_min : duplicateDecrease.min? = some 1 := by
  simp [duplicateDecrease, MinHeap.decreaseKey, MinHeap.min?, duplicate_data_before,
    siftUp, heapParent]

theorem empty_has_no_index : IsEmpty (Fin (MinHeap.empty : MinHeap Nat).data.size) := by
  simp [MinHeap.empty]

theorem larger_replacement_rejected :
    ¬5 ≤ base.data[(⟨1, by simp [base_data_before]⟩ : Fin base.data.size).val] := by
  simp [base_data_before]

#eval singletonDecrease.data.toList
#eval equalDecrease.data.toList
#eval noSwapDecrease.data.toList
#eval oneSwapDecrease.data.toList
#eval severalSwapDecrease.data.toList
#eval duplicateDecrease.data.toList
#eval duplicateDecrease.data.toList.count 2
#eval duplicateDecrease.data.toList.count 1

end Cslib.Algorithms.Lean.BinaryHeapDecreaseKeyTests
