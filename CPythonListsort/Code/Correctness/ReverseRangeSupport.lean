/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Code.Correctness.ReverseSliceCorrectness
import Code.Correctness.SortSliceRange

/-!
# Range-facing consequences of exact slice reversal

These lemmas expose `ReverseRangeSpec.reverseRangeEntries` through the shared
half-open range and frame vocabulary used by the run-correctness proofs.
-/

namespace CPythonListsort

namespace ReverseRangeSpec

/-- Selecting exactly a reversed range returns the reverse of the original
selected whole-entry range. -/
theorem sortSliceRangeEntries_reverseRange_self
    (slice : SortSlice κ ν) (start count : Nat)
    (hstop : start + count ≤ slice.entries.size) :
    sortSliceRangeEntries
        ({ entries := reverseRangeEntries slice.entries start (start + count) } :
          SortSlice κ ν)
        start count =
      (sortSliceRangeEntries slice start count).reverse := by
  apply Array.toList_inj.mp
  rw [sortSliceRangeEntries_toList, Array.toList_reverse,
    sortSliceRangeEntries_toList]
  rw [toList_reverseRange]
  have hstartLength :
      (slice.entries.toList.take start).length = start := by
    simp
    omega
  have hmiddleLength :
      ((slice.entries.toList.drop start).take count).length = count := by
    simp
    omega
  simp [hstartLength, hmiddleLength]

/-- Exact range reversal also reverses the key projection of that same range. -/
theorem sortSliceRangeKeys_reverseRange_self
    (slice : SortSlice κ ν) (start count : Nat)
    (hstop : start + count ≤ slice.entries.size) :
    sortSliceRangeKeys
        ({ entries := reverseRangeEntries slice.entries start (start + count) } :
          SortSlice κ ν)
        start count =
      (sortSliceRangeKeys slice start count).reverse := by
  simp only [sortSliceRangeKeys]
  rw [sortSliceRangeEntries_reverseRange_self slice start count hstop]
  simp

/-- Reversing a valid range is framed by the shared
`SortSlice.EqualOutsideRange` predicate. -/
theorem equalOutsideRange_reverseRange
    (slice : SortSlice κ ν) (start count : Nat)
    (hstop : start + count ≤ slice.entries.size) :
    SortSlice.EqualOutsideRange slice
      ({ entries := reverseRangeEntries slice.entries start (start + count) } :
        SortSlice κ ν)
      start count := by
  have hsize := size_reverseRange slice.entries start (start + count)
    (by omega) hstop
  refine ⟨hsize.symm, ?_⟩
  intro otherStart otherCount hdisjoint
  apply Array.ext_getElem?
  intro offset
  simp only [sortSliceRangeEntries, Array.getElem?_extract, hsize]
  by_cases hoff :
      offset < min (otherStart + otherCount) slice.entries.size - otherStart
  · rw [if_pos hoff, if_pos hoff]
    rcases hdisjoint with hbefore | hafter
    · rw [getElem?_reverseRange_before slice.entries start (start + count)
          (otherStart + offset) (by omega) hstop (by omega)]
    · rw [getElem?_reverseRange_after slice.entries start (start + count)
          (otherStart + offset) (by omega) hstop (by omega)]
  · rw [if_neg hoff, if_neg hoff]

end ReverseRangeSpec

end CPythonListsort
