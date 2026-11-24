/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import CSLibExt.Algorithms.Sorting.CPythonListsort.Correctness.PendingRunCorrectness
import CSLibExt.Algorithms.Sorting.CPythonListsort.Correctness.SortSliceRange
import CSLibExt.Algorithms.Sorting.CPythonListsort.Assembly.ListSortInputMode
import CSLibExt.Algorithms.Sorting.CPythonListsort.Transcription.ListSortImpl
import Mathlib

-- Preserve the imported development's original implicit type binders.
set_option autoImplicit true

/-!
# Unscanned-snapshot correctness

`PendingRunsCorrect` intentionally describes only the prefix already represented
by the pending stack.  The scan induction also needs a separate fact saying
that the still-unscanned keys are the untouched, absolutely tagged suffix of
the original snapshot.  Keeping that fact here avoids strengthening the
already-reviewed pending-run invariant.
-/

namespace CPythonListsort

universe u v

/-- The existing pending-run key view is definitionally the shared half-open
`SortSlice` key range.  This is the bridge used by local run and merge
correctness posts when they are assembled into `PendingRunsCorrect`. -/
@[simp]
theorem pendingRunOccurrenceKeys_eq_sortSliceRangeKeys
    (state : MergeState (Occurrence α) ν) (run : PendingRun) :
    pendingRunOccurrenceKeys state run =
      sortSliceRangeKeys state.data run.base run.len.toNat := by
  rfl

/-! ## Whole-entry occurrence tagging -/

/-- Attach an absolute occurrence index to every key in a complete
`SortSlice`, without changing the payload paired with that key.  Tagging the
whole slice before selecting a range prevents a nonzero-base subrange from
being accidentally retagged relative to zero. -/
def tagSortSliceOccurrences (slice : SortSlice κ ν) :
    SortSlice (Occurrence κ) ν :=
  { entries := slice.entries.zipIdx.map fun entry =>
      { key := { value := entry.1.key, origin := entry.2 }
        value := entry.1.value } }

@[simp]
theorem tagSortSliceOccurrences_size (slice : SortSlice κ ν) :
    (tagSortSliceOccurrences slice).entries.size = slice.entries.size := by
  simp [tagSortSliceOccurrences]

/-- Tagging changes only keys: the complete payload projection is identical
to that of the source slice. -/
theorem tagSortSliceOccurrences_payloads (slice : SortSlice κ ν) :
    (tagSortSliceOccurrences slice).entries.map SortSliceEntry.value =
      slice.entries.map SortSliceEntry.value := by
  apply Array.ext <;>
    simp [tagSortSliceOccurrences]

/-- Key projection of a tagged whole-entry range agrees exactly with tagging
the complete source key array before taking the same range. -/
theorem sortSliceRangeKeys_tagSortSliceOccurrences (slice : SortSlice κ ν)
    (start count : Nat) :
    sortSliceRangeKeys (tagSortSliceOccurrences slice) start count =
      (tagOccurrences (slice.entries.map SortSliceEntry.key)).extract
        start (start + count) := by
  have hkeys :
      (tagSortSliceOccurrences slice).entries.map SortSliceEntry.key =
        tagOccurrences (slice.entries.map SortSliceEntry.key) := by
    apply Array.ext <;>
      simp [tagSortSliceOccurrences, tagOccurrences]
  simpa only [sortSliceRangeKeys, sortSliceRangeEntries,
    Array.map_extract] using
      congrArg (fun keys => keys.extract start (start + count)) hkeys

/-- Occurrence tagging preserves the input's key/payload representation mode. -/
theorem tagSortSliceOccurrences_valuesMode
    {hasKeyfunc : Bool} {slice : SortSlice κ ν}
    (h : SortSlice.ValuesModeInvariant hasKeyfunc slice) :
    SortSlice.ValuesModeInvariant hasKeyfunc (tagSortSliceOccurrences slice) := by
  intro index hindex
  have hsource : index < slice.entries.size := by simpa using hindex
  have hmode := h index hsource
  unfold SortSlice.EntryMatchesValuesMode at hmode ⊢
  split <;> simpa [tagSortSliceOccurrences] using hmode

namespace ListSortInput

/-- Lift a validated keyed or unkeyed input to absolute occurrence keys while
retaining every payload and the same `hasKeyfunc` mode. -/
def withOccurrenceKeys (input : ListSortInput κ ν) :
    ListSortInput (Occurrence κ) ν where
  slice := tagSortSliceOccurrences input.slice
  hasKeyfunc := input.hasKeyfunc
  valuesMode := tagSortSliceOccurrences_valuesMode input.valuesMode

end ListSortInput

/-- Whole-entry companion to `ScanRemainderMatches`.  It says that the
unscanned suffix still contains exactly the tagged source entries, including
each optional payload, and exposes every clipping bound explicitly. -/
structure ScanRemainderEntriesMatch (source : SortSlice κ ν)
    (state : MergeState (Occurrence κ) ν) (scanned : Nat) : Prop where
  scanned_le : scanned ≤ state.listlen.toNat
  state_stop_le :
    state.basekeys + state.listlen.toNat ≤ state.data.entries.size
  source_stop_le :
    state.basekeys + state.listlen.toNat ≤ source.entries.size
  entries_eq :
    (sortSliceRangeEntries state.data (state.basekeys + scanned)
      (state.listlen.toNat - scanned)).toList =
      (sortSliceRangeEntries (tagSortSliceOccurrences source)
        (state.basekeys + scanned)
        (state.listlen.toNat - scanned)).toList

/-- The unscanned state suffix is exactly the corresponding absolute-origin
segment of the original input.

The three bounds are part of the proposition rather than implicit clipping
assumptions.  The invariant has no comparator parameter: it is a snapshot and
frame property, independent of ordering laws. -/
structure ScanRemainderMatches (input : Array α)
    (state : MergeState (Occurrence α) ν) (scanned : Nat) : Prop where
  scanned_le : scanned ≤ state.listlen.toNat
  state_stop_le :
    state.basekeys + state.listlen.toNat ≤ state.data.entries.size
  input_stop_le : state.basekeys + state.listlen.toNat ≤ input.size
  keys_eq :
    (sortSliceRangeKeys state.data (state.basekeys + scanned)
      (state.listlen.toNat - scanned)).toList =
      canonicalOccurrenceSegment input (state.basekeys + scanned)
        (state.listlen.toNat - scanned)

namespace ScanRemainderMatches

/-- The exact suffix equality, exported under a short projection name for the
top-level scan invariant. -/
theorem remainder_eq
    {input : Array α} {state : MergeState (Occurrence α) ν}
    {scanned : Nat} (h : ScanRemainderMatches input state scanned) :
    (sortSliceRangeKeys state.data (state.basekeys + scanned)
      (state.listlen.toNat - scanned)).toList =
      canonicalOccurrenceSegment input (state.basekeys + scanned)
        (state.listlen.toNat - scanned) :=
  h.keys_eq

/-- Dropping a prefix from a canonical absolute-origin segment advances both
its absolute base and its remaining length. -/
theorem canonicalOccurrenceSegment_drop (input : Array α)
    (base count skipped : Nat) :
    (canonicalOccurrenceSegment input base count).drop skipped =
      canonicalOccurrenceSegment input (base + skipped) (count - skipped) := by
  simp [canonicalOccurrenceSegment, List.extract, List.drop_take,
    List.drop_drop]

/-- A mutation confined to the already-consumed prefix preserves the exact
unscanned suffix.  Structural fields are named explicitly so callers cannot
silently change the interval described by the invariant. -/
theorem preserve_consumed_update
    {input : Array α}
    {before after : MergeState (Occurrence α) ν} {scanned : Nat}
    (h : ScanRemainderMatches input before scanned)
    (hbase : after.basekeys = before.basekeys)
    (hlistlen : after.listlen = before.listlen)
    (hframe : SortSlice.EqualOutsideRange before.data after.data
      before.basekeys scanned) :
    ScanRemainderMatches input after scanned := by
  refine
    { scanned_le := by simpa [hlistlen] using h.scanned_le
      state_stop_le := ?_
      input_stop_le := by simpa [hbase, hlistlen] using h.input_stop_le
      keys_eq := ?_ }
  · rw [hbase, hlistlen]
    rw [← hframe.size_eq]
    exact h.state_stop_le
  · have hsuffix := hframe.keys_eq_of_disjoint
        (before.basekeys + scanned) (before.listlen.toNat - scanned)
        (Or.inr le_rfl)
    rw [hbase, hlistlen]
    rw [← hsuffix]
    exact h.keys_eq

/-- Consuming `consumed` keys and changing only that newly consumed interval
advances the snapshot invariant to the shorter untouched suffix. -/
theorem advance
    {input : Array α}
    {before after : MergeState (Occurrence α) ν} {scanned consumed : Nat}
    (h : ScanRemainderMatches input before scanned)
    (hconsumed : consumed ≤ before.listlen.toNat - scanned)
    (hbase : after.basekeys = before.basekeys)
    (hlistlen : after.listlen = before.listlen)
    (hframe : SortSlice.EqualOutsideRange before.data after.data
      (before.basekeys + scanned) consumed) :
    ScanRemainderMatches input after (scanned + consumed) := by
  have hscannedConsumed :
      scanned + consumed ≤ before.listlen.toNat := by
    have hscanned := h.scanned_le
    omega
  have htail := congrArg (List.drop consumed) h.keys_eq
  rw [sortSliceRangeKeys_toList_drop,
    canonicalOccurrenceSegment_drop] at htail
  have hbeforeTail :
      (sortSliceRangeKeys before.data
        (before.basekeys + (scanned + consumed))
        (before.listlen.toNat - (scanned + consumed))).toList =
      canonicalOccurrenceSegment input
        (before.basekeys + (scanned + consumed))
        (before.listlen.toNat - (scanned + consumed)) := by
    simpa [Nat.add_assoc, Nat.sub_sub] using htail
  have hsuffix := hframe.keys_eq_of_disjoint
    (before.basekeys + (scanned + consumed))
    (before.listlen.toNat - (scanned + consumed)) (Or.inr (by omega))
  refine
    { scanned_le := by simpa [hlistlen] using hscannedConsumed
      state_stop_le := ?_
      input_stop_le := by simpa [hbase, hlistlen] using h.input_stop_le
      keys_eq := ?_ }
  · rw [hbase, hlistlen]
    rw [← hframe.size_eq]
    exact h.state_stop_le
  · rw [hbase, hlistlen]
    rw [← hsuffix]
    exact hbeforeTail

end ScanRemainderMatches

namespace ScanRemainderEntriesMatch

/-- Whole-entry suffix agreement entails the original, approved key-only
snapshot invariant. -/
theorem toScanRemainderMatches
    {source : SortSlice κ ν} {state : MergeState (Occurrence κ) ν}
    {scanned : Nat} (h : ScanRemainderEntriesMatch source state scanned) :
    ScanRemainderMatches (source.entries.map SortSliceEntry.key)
      state scanned := by
  refine
    { scanned_le := h.scanned_le
      state_stop_le := h.state_stop_le
      input_stop_le := by simpa using h.source_stop_le
      keys_eq := ?_ }
  have hkeys := congrArg (List.map SortSliceEntry.key) h.entries_eq
  calc
    (sortSliceRangeKeys state.data (state.basekeys + scanned)
        (state.listlen.toNat - scanned)).toList =
        (sortSliceRangeEntries state.data (state.basekeys + scanned)
          (state.listlen.toNat - scanned)).toList.map
            SortSliceEntry.key := by simp [sortSliceRangeKeys]
    _ =
        (sortSliceRangeEntries (tagSortSliceOccurrences source)
          (state.basekeys + scanned)
          (state.listlen.toNat - scanned)).toList.map
            SortSliceEntry.key := hkeys
    _ =
        (sortSliceRangeKeys (tagSortSliceOccurrences source)
          (state.basekeys + scanned)
          (state.listlen.toNat - scanned)).toList := by
            simp [sortSliceRangeKeys]
    _ = canonicalOccurrenceSegment
          (source.entries.map SortSliceEntry.key)
          (state.basekeys + scanned) (state.listlen.toNat - scanned) := by
      rw [sortSliceRangeKeys_tagSortSliceOccurrences]
      rfl

/-- A mutation confined to the already-consumed prefix preserves the exact
unscanned whole-entry suffix. -/
theorem preserve_consumed_update
    {source : SortSlice κ ν}
    {before after : MergeState (Occurrence κ) ν} {scanned : Nat}
    (h : ScanRemainderEntriesMatch source before scanned)
    (hbase : after.basekeys = before.basekeys)
    (hlistlen : after.listlen = before.listlen)
    (hframe : SortSlice.EqualOutsideRange before.data after.data
      before.basekeys scanned) :
    ScanRemainderEntriesMatch source after scanned := by
  refine
    { scanned_le := by simpa [hlistlen] using h.scanned_le
      state_stop_le := ?_
      source_stop_le := by simpa [hbase, hlistlen] using h.source_stop_le
      entries_eq := ?_ }
  · rw [hbase, hlistlen]
    rw [← hframe.size_eq]
    exact h.state_stop_le
  · have hsuffix := hframe.entries_eq_of_disjoint
        (before.basekeys + scanned) (before.listlen.toNat - scanned)
        (Or.inr le_rfl)
    rw [hbase, hlistlen]
    rw [← hsuffix]
    exact h.entries_eq

/-- Consuming `consumed` entries and changing only that consumed interval
advances whole-entry suffix agreement to the remaining range. -/
theorem advance
    {source : SortSlice κ ν}
    {before after : MergeState (Occurrence κ) ν}
    {scanned consumed : Nat}
    (h : ScanRemainderEntriesMatch source before scanned)
    (hconsumed : consumed ≤ before.listlen.toNat - scanned)
    (hbase : after.basekeys = before.basekeys)
    (hlistlen : after.listlen = before.listlen)
    (hframe : SortSlice.EqualOutsideRange before.data after.data
      (before.basekeys + scanned) consumed) :
    ScanRemainderEntriesMatch source after (scanned + consumed) := by
  have hscannedConsumed :
      scanned + consumed ≤ before.listlen.toNat := by
    have hscanned := h.scanned_le
    omega
  have htail := congrArg (List.drop consumed) h.entries_eq
  rw [sortSliceRangeEntries_toList_drop,
    sortSliceRangeEntries_toList_drop] at htail
  have hbeforeTail :
      (sortSliceRangeEntries before.data
        (before.basekeys + (scanned + consumed))
        (before.listlen.toNat - (scanned + consumed))).toList =
      (sortSliceRangeEntries (tagSortSliceOccurrences source)
        (before.basekeys + (scanned + consumed))
        (before.listlen.toNat - (scanned + consumed))).toList := by
    simpa [Nat.add_assoc, Nat.sub_sub] using htail
  have hsuffix := hframe.entries_eq_of_disjoint
    (before.basekeys + (scanned + consumed))
    (before.listlen.toNat - (scanned + consumed)) (Or.inr (by omega))
  refine
    { scanned_le := by simpa [hlistlen] using hscannedConsumed
      state_stop_le := ?_
      source_stop_le := by simpa [hbase, hlistlen] using h.source_stop_le
      entries_eq := ?_ }
  · rw [hbase, hlistlen]
    rw [← hframe.size_eq]
    exact h.state_stop_le
  · rw [hbase, hlistlen]
    rw [← hsuffix]
    exact hbeforeTail

end ScanRemainderEntriesMatch

/-! ## Initialization and anti-vacuity regressions -/

/-- Canonically tagged unkeyed input used by the occurrence-carrying
correctness execution. -/
def occurrenceInputSlice (input : Array α) : SortSlice (Occurrence α) PUnit :=
  { entries := (tagOccurrences input).map fun key =>
      { key := key, value := none } }

@[simp]
theorem occurrenceInputSlice_size (input : Array α) :
    (occurrenceInputSlice input).entries.size = input.size := by
  simp [occurrenceInputSlice, tagOccurrences]

/-- Projecting keys from the occurrence input slice recovers the canonical
tagged half-open range exactly. -/
theorem sortSliceRangeKeys_occurrenceInputSlice (input : Array α)
    (start count : Nat) :
    sortSliceRangeKeys (occurrenceInputSlice input) start count =
      (tagOccurrences input).extract start (start + count) := by
  apply Array.ext_getElem?
  intro i
  simp [sortSliceRangeKeys, sortSliceRangeEntries, occurrenceInputSlice,
    Function.comp_def]

/-- Initialization from a complete source slice establishes whole-entry
unscanned agreement for either values mode.  `hasKeyfunc` is deliberately
arbitrary: the tagged slice preserves every payload, so the theorem applies
to both validated keyed and unkeyed inputs. -/
theorem scanRemainderEntriesMatch_initial
    (keyCompare : BoolComparator (Occurrence κ)) (hasKeyfunc : Bool)
    (source : SortSlice κ ν) (hsize : source.entries.size ≤ PY_LIST_MAX) :
    ScanRemainderEntriesMatch source
      (initialMergeState keyCompare hasKeyfunc
        (tagSortSliceOccurrences source)).1 0 := by
  have hword :
      (BitVec.ofNat 64 source.entries.size : PySSize).toNat =
        source.entries.size := by
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt]
    norm_num [PY_LIST_MAX, PY_SSIZE_T_MAX, PY_OBJECT_PTR_BYTES] at hsize ⊢
    omega
  refine
    { scanned_le := by
        simp [initialMergeState, minrunInitTraced, hword]
      state_stop_le := by
        simp [initialMergeState, minrunInitTraced, hword]
      source_stop_le := by
        simp [initialMergeState, minrunInitTraced, hword]
      entries_eq := ?_ }
  simp [initialMergeState, minrunInitTraced, hword]

/-- Validated-input form of whole-entry initialization.  It runs
`initialMergeState` with exactly the input's proof-carrying `hasKeyfunc` mode. -/
theorem scanRemainderEntriesMatch_initial_listSortInput
    (keyCompare : BoolComparator (Occurrence κ))
    (input : ListSortInput κ ν)
    (hsize : input.slice.entries.size ≤ PY_LIST_MAX) :
    ScanRemainderEntriesMatch input.slice
      (initialMergeState keyCompare input.hasKeyfunc
        input.withOccurrenceKeys.slice).1 0 := by
  simpa [ListSortInput.withOccurrenceKeys] using
    scanRemainderEntriesMatch_initial keyCompare input.hasKeyfunc
      input.slice hsize

/-- `initialMergeState` establishes the complete unscanned snapshot invariant
at `scanned = 0` for every source-admitted occurrence-carrying input. -/
theorem scanRemainderMatches_initial
    (keyCompare : BoolComparator (Occurrence α)) (input : Array α)
    (hsize : input.size ≤ PY_LIST_MAX) :
    ScanRemainderMatches input
      (initialMergeState keyCompare false (occurrenceInputSlice input)).1 0 := by
  have hword :
      (BitVec.ofNat 64 input.size : PySSize).toNat = input.size := by
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt]
    norm_num [PY_LIST_MAX, PY_SSIZE_T_MAX, PY_OBJECT_PTR_BYTES] at hsize ⊢
    omega
  refine
    { scanned_le := by simp [initialMergeState, minrunInitTraced, hword]
      state_stop_le := by
        simp [initialMergeState, minrunInitTraced, hword]
      input_stop_le := by
        simp [initialMergeState, minrunInitTraced, hword]
      keys_eq := ?_ }
  simp only [initialMergeState, minrunInitTraced, Nat.zero_add,
    Nat.sub_zero]
  rw [sortSliceRangeKeys_occurrenceInputSlice]
  rfl

end CPythonListsort
