/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.Specs.Sorting
public import CSLibExt.Algorithms.Lean.Sort.Selection

/-!
# Selection sort satisfies the sorting contract

This bridge uses the existing `TimeM` selection sort and its correctness
proof. It constrains the returned list, not the algorithm's cost field.
-/

public section

universe u

namespace CSLibExt.Specs.Sorting

/-- The canonical costed selection sort satisfies the sorting contract. -/
theorem sorting_selectionSort {α : Type u} [LinearOrder α] (xs : List α) :
    SortingSpec xs
      (Cslib.Algorithms.Lean.TimeM.selectionSort xs).ret :=
  (Cslib.Algorithms.Lean.TimeM.selectionSort_correct xs).symm

end CSLibExt.Specs.Sorting
