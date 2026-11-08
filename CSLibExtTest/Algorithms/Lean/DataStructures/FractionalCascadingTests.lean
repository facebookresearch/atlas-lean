/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.Algorithms.Lean.DataStructures.FractionalCascading

/-!
# Tests for the fractional-cascading API

These client examples exercise sampling, merging, augmentation, bridge
pointers, and search through the public executable and correctness API,
including empty catalogs, duplicates, and multi-catalog augmentation.
-/

@[expose] public section

set_option autoImplicit false

namespace Cslib.Algorithms.Lean.FractionalCascadingTests

open FractionalCascading

example : sample ([] : List Nat) = [] := by decide

example : sample [7] = [7] := by decide

example : sample [1, 2, 3, 4, 5] = [1, 3, 5] := by decide

example : sample [1, 2, 3, 4] = [1, 3] := by decide

example : sample [1, 1, 1, 1] = [1, 1] := by decide

example : (sortedMerge [1, 4] [2, 3]).length = 4 := by
  rw [length_sortedMerge]; rfl

example : (sortedMerge [1, 4] [2, 3]).Pairwise (· ≤ ·) :=
  pairwise_sortedMerge _ _

example : 3 ∈ sortedMerge [1, 4] [2, 3] := by
  rw [mem_sortedMerge_iff]; exact Or.inr (by decide)

example : (augmentOne [1, 4] [2, 3, 5]).length = 4 := by
  rw [length_augmentOne]; decide

example : 5 ∈ augmentOne [1, 4] [2, 3, 5] := by
  rw [mem_augmentOne_iff]; exact Or.inr (by decide)

example : augmented ([] : List (List Nat)) = [] := by decide

example : augmented [[1, 4]] = [[1, 4]] :=
  augmented_singleton _

example : (augmented [[1, 4], [2, 3, 5], [0, 6]]).length = 3 :=
  length_augmented _

example : bridgePtr [2, 3, 5] 3 = 2 := by decide

example : bridgePtr [2, 3, 5] 0 = 0 := by decide

example : bridgePtr [2, 3, 5] 9 = 3 := by decide

example : bridges [1, 4] [2, 3, 5] = [0, 2] := by decide

example : bridges ([] : List Nat) [2, 3, 5] = [] := by decide

example : lowerBound 3 [1, 2, 3, 3, 4] = 2 := by decide

example : countLT 3 [1, 2, 3, 3, 4] = 2 := by decide

example : searchAll 3 [[1, 2, 3], [0, 5], []] = [2, 1, 0] := by decide

example : searchAll 3 ([] : List (List Nat)) = [] := by decide

example : (searchAugmented 3 [[1, 4], [2, 3, 5]]).length = 2 :=
  length_searchAugmented _ _

example (x : Nat) (cs : List (List Nat)) :
    searchAugmented x cs = (augmented cs).map (lowerBound x) :=
  searchAugmented_eq_map_lowerBound x cs

example (cs : List (List Nat)) (hcs : ∀ c ∈ cs, c.Pairwise (· ≤ ·)) :
    ∀ a ∈ augmented cs, a.Pairwise (· ≤ ·) :=
  pairwise_augmented hcs

example (x : Nat) (cs : List (List Nat)) :
    searchAll x cs = cs.map (lowerBound x) :=
  searchAll_eq_map_lowerBound x cs

example (next : List Nat) (v : Nat) : bridgePtr next v ≤ next.length :=
  bridgePtr_le_length next v

example (x : Nat) (c a : List Nat) :
    lowerBound x (augmentOne c a) =
      lowerBound x c + lowerBound x (sample a) :=
  lowerBound_augmentOne x c a

/-- The rounded-up-half sample bound is tight at even length: the sample
of a four-element catalog has exactly `(4 + 1) / 2 = 2` elements, through
the public `length_sample_le`. -/
example : (sample [1, 2, 3, 4]).length = ([1, 2, 3, 4] : List Nat).length / 2 := by
  decide

example (xs : List Nat) : (sample xs).length ≤ (xs.length + 1) / 2 :=
  length_sample_le xs

example (c a : List Nat) :
    (augmentOne c a).length ≤ c.length + (a.length + 1) / 2 :=
  length_augmentOne_le c a

#check Cslib.Algorithms.Lean.FractionalCascading.length_sample_le
#check Cslib.Algorithms.Lean.FractionalCascading.length_augmentOne_le

#print axioms Cslib.Algorithms.Lean.FractionalCascading.pairwise_augmented
#print axioms Cslib.Algorithms.Lean.FractionalCascading.searchAll_eq_map_lowerBound
#print axioms Cslib.Algorithms.Lean.FractionalCascading.lowerBound_augmentOne
#print axioms Cslib.Algorithms.Lean.FractionalCascading.length_mem_augmented_le

end Cslib.Algorithms.Lean.FractionalCascadingTests
