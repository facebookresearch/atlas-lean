/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Code.Transcription.SortSlice
import Mathlib

/-!
# Half-open `SortSlice` ranges and semantic frames

Correctness proofs reason about the contents moved by the transcribed pointer
operations, rather than only their allocation bounds.  This file supplies one
shared, natural-indexed vocabulary for a half-open range `[start, start + count)`
and for the assertion that an update is confined to such a range.
-/

namespace CPythonListsort

universe u v

/-- Whole key/value entries in the clipped half-open range
`[start, start + count)`. -/
def sortSliceRangeEntries (slice : SortSlice κ ν) (start count : Nat) :
    Array (SortSliceEntry κ ν) :=
  slice.entries.extract start (start + count)

/-- Key projection of `sortSliceRangeEntries`.  Payloads remain paired with
their keys in `sortSliceRangeEntries`; this projection is for the shared
sortedness and occurrence-stability specifications. -/
def sortSliceRangeKeys (slice : SortSlice κ ν) (start count : Nat) :
    Array κ :=
  (sortSliceRangeEntries slice start count).map SortSliceEntry.key

@[simp]
theorem sortSliceRangeKeys_eq_map (slice : SortSlice κ ν)
    (start count : Nat) :
    sortSliceRangeKeys slice start count =
      (sortSliceRangeEntries slice start count).map SortSliceEntry.key :=
  rfl

@[simp]
theorem sortSliceRangeEntries_zero (slice : SortSlice κ ν)
    (start : Nat) :
    sortSliceRangeEntries slice start 0 = #[] := by
  simp [sortSliceRangeEntries]

@[simp]
theorem sortSliceRangeKeys_zero (slice : SortSlice κ ν)
    (start : Nat) :
    sortSliceRangeKeys slice start 0 = #[] := by
  simp [sortSliceRangeKeys]

/-- An in-bounds range has exactly its requested number of entries. -/
theorem sortSliceRangeEntries_size (slice : SortSlice κ ν)
    (start count : Nat) (hstop : start + count ≤ slice.entries.size) :
    (sortSliceRangeEntries slice start count).size = count := by
  simp [sortSliceRangeEntries]
  omega

/-- Key projection does not change the range length. -/
theorem sortSliceRangeKeys_size (slice : SortSlice κ ν)
    (start count : Nat) (hstop : start + count ≤ slice.entries.size) :
    (sortSliceRangeKeys slice start count).size = count := by
  simp [sortSliceRangeKeys, sortSliceRangeEntries_size _ _ _ hstop]

/-- Pointwise view of an in-bounds whole-entry range. -/
theorem sortSliceRangeEntries_getElem
    (slice : SortSlice κ ν) (start count i : Nat)
    (hstop : start + count ≤ slice.entries.size) (hi : i < count) :
    (sortSliceRangeEntries slice start count)[i]'(by
      rw [sortSliceRangeEntries_size slice start count hstop]
      exact hi) = slice.entries[start + i]'(by omega) := by
  simp only [sortSliceRangeEntries]
  rw [Array.getElem_extract]

/-- Pointwise key projection of an in-bounds whole-entry range. -/
theorem sortSliceRangeKeys_getElem
    (slice : SortSlice κ ν) (start count i : Nat)
    (hstop : start + count ≤ slice.entries.size) (hi : i < count) :
    (sortSliceRangeKeys slice start count)[i]'(by
      rw [sortSliceRangeKeys_size slice start count hstop]
      exact hi) =
      (slice.entries[start + i]'(by omega)).key := by
  simp only [sortSliceRangeKeys, sortSliceRangeEntries, Array.getElem_map]
  rw [Array.getElem_extract]

/-- List view of the half-open entry range. -/
theorem sortSliceRangeEntries_toList (slice : SortSlice κ ν)
    (start count : Nat) :
    (sortSliceRangeEntries slice start count).toList =
      (slice.entries.toList.drop start).take count := by
  simp [sortSliceRangeEntries, List.extract]

/-- A whole-entry range of a sum length splits at the first summand. -/
theorem sortSliceRangeEntries_toList_add
    (slice : SortSlice κ ν) (start leftCount rightCount : Nat) :
    (sortSliceRangeEntries slice start (leftCount + rightCount)).toList =
      (sortSliceRangeEntries slice start leftCount).toList ++
        (sortSliceRangeEntries slice (start + leftCount) rightCount).toList := by
  simp only [sortSliceRangeEntries_toList, List.take_add, List.drop_drop]

/-- Dropping an initial part of a half-open entry range exposes the
corresponding later whole-entry range.  Unlike its key-only companion below,
this lemma keeps each key paired with its payload. -/
theorem sortSliceRangeEntries_toList_drop (slice : SortSlice κ ν)
    (start count skipped : Nat) :
    (sortSliceRangeEntries slice start count).toList.drop skipped =
      (sortSliceRangeEntries slice (start + skipped)
        (count - skipped)).toList := by
  rw [sortSliceRangeEntries_toList, sortSliceRangeEntries_toList]
  simp [List.drop_take, List.drop_drop]

/-- List view commutes with key projection. -/
theorem sortSliceRangeKeys_toList (slice : SortSlice κ ν)
    (start count : Nat) :
    (sortSliceRangeKeys slice start count).toList =
      ((slice.entries.toList.drop start).take count).map SortSliceEntry.key := by
  simp [sortSliceRangeKeys, sortSliceRangeEntries_toList]

/-- Dropping an initial part of a valid half-open key range exposes the
corresponding later range. -/
theorem sortSliceRangeKeys_toList_drop (slice : SortSlice κ ν)
    (start count skipped : Nat) :
    (sortSliceRangeKeys slice start count).toList.drop skipped =
      (sortSliceRangeKeys slice (start + skipped) (count - skipped)).toList := by
  rw [sortSliceRangeKeys_toList, sortSliceRangeKeys_toList]
  simp [List.drop_take, List.drop_drop]

namespace SortSlice

@[simp]
theorem read?_ofNat (slice : SortSlice κ ν) (index : Nat) :
    slice.read? (Int.ofNat index) = slice.entries[index]? := by
  simp [read?]

/-- `before` and `after` have the same extent and every half-open range
disjoint from `[start, start + count)` has exactly the same whole entries.

The quantified-range formulation is intentionally compositional: callers can
specialize it directly to the unconsumed suffix, while cell-level proofs may
establish it from their own pointwise write-frame lemmas. -/
def EqualOutsideRange (before after : SortSlice κ ν)
    (start count : Nat) : Prop :=
  before.entries.size = after.entries.size ∧
    ∀ otherStart otherCount,
      otherStart + otherCount ≤ start ∨ start + count ≤ otherStart →
        sortSliceRangeEntries before otherStart otherCount =
          sortSliceRangeEntries after otherStart otherCount

namespace EqualOutsideRange

theorem size_eq {before after : SortSlice κ ν} {start count : Nat}
    (h : EqualOutsideRange before after start count) :
    before.entries.size = after.entries.size :=
  h.1

theorem entries_eq_of_disjoint
    {before after : SortSlice κ ν} {start count : Nat}
    (h : EqualOutsideRange before after start count)
    (otherStart otherCount : Nat)
    (hdisjoint : otherStart + otherCount ≤ start ∨
      start + count ≤ otherStart) :
    sortSliceRangeEntries before otherStart otherCount =
      sortSliceRangeEntries after otherStart otherCount :=
  h.2 otherStart otherCount hdisjoint

theorem keys_eq_of_disjoint
    {before after : SortSlice κ ν} {start count : Nat}
    (h : EqualOutsideRange before after start count)
    (otherStart otherCount : Nat)
    (hdisjoint : otherStart + otherCount ≤ start ∨
      start + count ≤ otherStart) :
    sortSliceRangeKeys before otherStart otherCount =
      sortSliceRangeKeys after otherStart otherCount := by
  simp only [sortSliceRangeKeys]
  rw [h.entries_eq_of_disjoint otherStart otherCount hdisjoint]

theorem refl (slice : SortSlice κ ν) (start count : Nat) :
    EqualOutsideRange slice slice start count := by
  exact ⟨rfl, fun _ _ _ => rfl⟩

theorem symm {before after : SortSlice κ ν} {start count : Nat}
    (h : EqualOutsideRange before after start count) :
    EqualOutsideRange after before start count := by
  refine ⟨h.size_eq.symm, ?_⟩
  intro otherStart otherCount hdisjoint
  exact (h.entries_eq_of_disjoint otherStart otherCount hdisjoint).symm

theorem trans {first second third : SortSlice κ ν} {start count : Nat}
    (h₁ : EqualOutsideRange first second start count)
    (h₂ : EqualOutsideRange second third start count) :
    EqualOutsideRange first third start count := by
  refine ⟨h₁.size_eq.trans h₂.size_eq, ?_⟩
  intro otherStart otherCount hdisjoint
  exact (h₁.entries_eq_of_disjoint otherStart otherCount hdisjoint).trans
    (h₂.entries_eq_of_disjoint otherStart otherCount hdisjoint)

/-- A frame for a contained write range is also a frame for any enclosing
range. -/
theorem widen
    {before after : SortSlice κ ν}
    {smallStart smallCount bigStart bigCount : Nat}
    (h : EqualOutsideRange before after smallStart smallCount)
    (hstart : bigStart ≤ smallStart)
    (hstop : smallStart + smallCount ≤ bigStart + bigCount) :
    EqualOutsideRange before after bigStart bigCount := by
  refine ⟨h.size_eq, ?_⟩
  intro otherStart otherCount hdisjoint
  apply h.entries_eq_of_disjoint otherStart otherCount
  rcases hdisjoint with hbefore | hafter
  · exact Or.inl (by omega)
  · exact Or.inr (by omega)

/-- Extensional equality is the degenerate frame for any selected range. -/
theorem of_eq {before after : SortSlice κ ν} (h : before = after)
    (start count : Nat) : EqualOutsideRange before after start count := by
  subst after
  exact refl before start count

end EqualOutsideRange

end SortSlice

/-- Turn exact signed reads into the list form consumed by range-level
correctness invariants.  The length and stop hypotheses rule out clipping. -/
theorem sortSliceRangeEntries_toList_eq_of_reads
    (slice : SortSlice κ ν) (start count : Nat)
    (entries : List (SortSliceEntry κ ν))
    (hstop : start + count ≤ slice.entries.size)
    (hlength : entries.length = count)
    (hread : ∀ offset, offset < count →
      slice.read? (Int.ofNat (start + offset)) = entries[offset]?) :
    (sortSliceRangeEntries slice start count).toList = entries := by
  apply List.ext_getElem?
  intro offset
  by_cases hoffset : offset < count
  · have h := hread offset hoffset
    rw [SortSlice.read?_ofNat] at h
    rw [sortSliceRangeEntries_toList]
    simpa [hoffset, hstop] using h
  · rw [List.getElem?_eq_none (by
        rw [show (sortSliceRangeEntries slice start count).toList.length =
          count by simp [sortSliceRangeEntries_size _ _ _ hstop]]
        omega),
      List.getElem?_eq_none (by omega)]

end CPythonListsort
