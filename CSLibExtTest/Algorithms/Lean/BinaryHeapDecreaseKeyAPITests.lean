/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.Algorithms.Lean.DataStructures.BinaryHeap.DecreaseKey

/-!
# Ordinary-client tests for binary-heap decrease-key
-/

public section

namespace Cslib.Algorithms.Lean.BinaryHeapDecreaseKeyAPITests

set_option autoImplicit false

universe u

theorem data_law {α : Type u} [LinearOrder α]
    (h : MinHeap α) (i : Fin h.data.size) (x : α)
    (hdecrease : x ≤ h.data[i.val]) :
    (h.decreaseKey i x hdecrease).data =
      siftUp (h.data.set i.val x) i.val :=
  h.decreaseKey_data i x hdecrease

theorem ordered_law {α : Type u} [LinearOrder α]
    (h : MinHeap α) (i : Fin h.data.size) (x : α)
    (hdecrease : x ≤ h.data[i.val]) :
    HeapOrdered (h.decreaseKey i x hdecrease).data :=
  h.decreaseKey_ordered i x hdecrease

theorem size_law {α : Type u} [LinearOrder α]
    (h : MinHeap α) (i : Fin h.data.size) (x : α)
    (hdecrease : x ≤ h.data[i.val]) :
    (h.decreaseKey i x hdecrease).data.size = h.data.size :=
  h.decreaseKey_size i x hdecrease

theorem elements_law {α : Type u} [LinearOrder α]
    (h : MinHeap α) (i : Fin h.data.size) (x : α)
    (hdecrease : x ≤ h.data[i.val]) :
    (h.decreaseKey i x hdecrease).elements =
      x ::ₘ h.elements.erase (h.data[i.val]) :=
  h.decreaseKey_elements i x hdecrease

end Cslib.Algorithms.Lean.BinaryHeapDecreaseKeyAPITests
