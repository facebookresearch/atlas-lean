/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Code.Correctness.OriginRelabelScan

/-!
# Erasure of occurrence tags

The functional-correctness development runs the implementation on keys tagged
with their original positions.  This module proves that those tags are ghost
data for execution: after structurally erasing every occurrence key, the full
tagged evaluator is exactly the ordinary untagged evaluator.  Optional payloads
and all control, allocation, pending-run, and fuel fields are preserved.
-/

namespace CPythonListsort

universe u v

variable {alpha : Type u} {nu : Type v}

/-- Forget the origin component of one occurrence-bearing synchronized entry. -/
def eraseOccurrenceEntry
    (entry : SortSliceEntry (Occurrence alpha) nu) : SortSliceEntry alpha nu :=
  { key := entry.key.value
    value := entry.value }

/-- Forget occurrence origins throughout a synchronized slice. -/
def eraseOccurrenceSlice
    (slice : SortSlice (Occurrence alpha) nu) : SortSlice alpha nu :=
  { entries := slice.entries.map eraseOccurrenceEntry }

/-- Project an occurrence comparator to values by supplying irrelevant origins. -/
def eraseOccurrenceComparator
    (compare : BoolComparator (Occurrence alpha)) : BoolComparator alpha :=
  fun left right =>
    compare { value := left, origin := 0 } { value := right, origin := 0 }

/-- Forget occurrence origins in initialized temporary cells. -/
def eraseOccurrenceTempStorage
    (storage : TempStorage (Occurrence alpha) nu) : TempStorage alpha nu :=
  { cells := storage.cells.map (Option.map eraseOccurrenceEntry)
    backing := storage.backing
    hasValues := storage.hasValues }

/-- Structurally erase occurrence origins from a merge state. -/
def eraseOccurrenceMergeState
    (state : MergeState (Occurrence alpha) nu) : MergeState alpha nu :=
  { min_gallop := state.min_gallop
    listlen := state.listlen
    basekeys := state.basekeys
    data := eraseOccurrenceSlice state.data
    a := eraseOccurrenceTempStorage state.a
    alloced := state.alloced
    pending := state.pending
    key_compare := eraseOccurrenceComparator state.key_compare
    mr_current := state.mr_current
    mr_e := state.mr_e
    mr_mask := state.mr_mask }

/-- Structurally erase occurrence origins from a top-level result. -/
def eraseOccurrenceListSortImplResult
    (result : ListSortImplResult (Occurrence alpha) nu) :
    ListSortImplResult alpha nu :=
  { state := eraseOccurrenceMergeState result.state
    returnCode := result.returnCode
    fuelExhausted := result.fuelExhausted }

@[simp]
theorem eraseOccurrenceComparator_occurrenceComparator
    (lt : BoolComparator alpha) :
    eraseOccurrenceComparator (occurrenceComparator lt) = lt := by
  rfl

@[simp]
theorem eraseOccurrenceEntry_key
    (entry : SortSliceEntry (Occurrence alpha) nu) :
    (eraseOccurrenceEntry entry).key = entry.key.value := rfl

@[simp]
theorem eraseOccurrenceEntry_value
    (entry : SortSliceEntry (Occurrence alpha) nu) :
    (eraseOccurrenceEntry entry).value = entry.value := rfl

@[simp]
theorem eraseOccurrenceSlice_entries
    (slice : SortSlice (Occurrence alpha) nu) :
    (eraseOccurrenceSlice slice).entries =
      slice.entries.map eraseOccurrenceEntry := rfl

@[simp]
theorem eraseOccurrenceSlice_entries_size
    (slice : SortSlice (Occurrence alpha) nu) :
    (eraseOccurrenceSlice slice).entries.size = slice.entries.size := by
  simp [eraseOccurrenceSlice]

@[simp]
theorem eraseOccurrenceTempStorage_cells
    (storage : TempStorage (Occurrence alpha) nu) :
    (eraseOccurrenceTempStorage storage).cells =
      storage.cells.map (Option.map eraseOccurrenceEntry) := rfl

@[simp]
theorem eraseOccurrenceTempStorage_cells_size
    (storage : TempStorage (Occurrence alpha) nu) :
    (eraseOccurrenceTempStorage storage).cells.size = storage.cells.size := by
  simp [eraseOccurrenceTempStorage]

@[simp]
theorem eraseOccurrenceMergeState_data
    (state : MergeState (Occurrence alpha) nu) :
    (eraseOccurrenceMergeState state).data = eraseOccurrenceSlice state.data := rfl

@[simp]
theorem eraseOccurrenceMergeState_tempStorage
    (state : MergeState (Occurrence alpha) nu) :
    (eraseOccurrenceMergeState state).a =
      eraseOccurrenceTempStorage state.a := rfl

@[simp]
theorem eraseOccurrenceMergeState_key_compare
    (state : MergeState (Occurrence alpha) nu) :
    (eraseOccurrenceMergeState state).key_compare =
      eraseOccurrenceComparator state.key_compare := rfl

@[simp]
theorem eraseOccurrenceMergeState_pending
    (state : MergeState (Occurrence alpha) nu) :
    (eraseOccurrenceMergeState state).pending = state.pending := rfl

@[simp]
theorem eraseOccurrenceMergeState_listlen
    (state : MergeState (Occurrence alpha) nu) :
    (eraseOccurrenceMergeState state).listlen = state.listlen := rfl

@[simp]
theorem eraseOccurrenceMergeState_basekeys
    (state : MergeState (Occurrence alpha) nu) :
    (eraseOccurrenceMergeState state).basekeys = state.basekeys := rfl

@[simp]
theorem eraseOccurrenceMergeState_alloced
    (state : MergeState (Occurrence alpha) nu) :
    (eraseOccurrenceMergeState state).alloced = state.alloced := rfl

@[simp]
theorem eraseOccurrenceMergeState_minrunState
    (state : MergeState (Occurrence alpha) nu) :
    (eraseOccurrenceMergeState state).minrunState = state.minrunState := rfl

@[simp]
theorem eraseOccurrenceMergeState_minGallop
    (state : MergeState (Occurrence alpha) nu) :
    (eraseOccurrenceMergeState state).min_gallop = state.min_gallop := rfl

@[simp]
theorem eraseOccurrenceMergeState_mrCurrent
    (state : MergeState (Occurrence alpha) nu) :
    (eraseOccurrenceMergeState state).mr_current = state.mr_current := rfl

@[simp]
theorem eraseOccurrenceMergeState_mrE
    (state : MergeState (Occurrence alpha) nu) :
    (eraseOccurrenceMergeState state).mr_e = state.mr_e := rfl

@[simp]
theorem eraseOccurrenceMergeState_mrMask
    (state : MergeState (Occurrence alpha) nu) :
    (eraseOccurrenceMergeState state).mr_mask = state.mr_mask := rfl

@[simp]
theorem eraseOccurrenceListSortImplResult_state
    (result : ListSortImplResult (Occurrence alpha) nu) :
    (eraseOccurrenceListSortImplResult result).state =
      eraseOccurrenceMergeState result.state := rfl

@[simp]
theorem eraseOccurrenceListSortImplResult_returnCode
    (result : ListSortImplResult (Occurrence alpha) nu) :
    (eraseOccurrenceListSortImplResult result).returnCode = result.returnCode := rfl

@[simp]
theorem eraseOccurrenceListSortImplResult_fuelExhausted
    (result : ListSortImplResult (Occurrence alpha) nu) :
    (eraseOccurrenceListSortImplResult result).fuelExhausted =
      result.fuelExhausted := rfl

@[simp]
theorem eraseOccurrenceSlice_tagSortSliceOccurrences
    (slice : SortSlice alpha nu) :
    eraseOccurrenceSlice (tagSortSliceOccurrences slice) = slice := by
  cases slice with
  | mk entries =>
      simp only [eraseOccurrenceSlice, tagSortSliceOccurrences]
      congr 1
      apply Array.ext <;>
        simp [eraseOccurrenceEntry]

@[simp]
theorem eraseOccurrenceInput_withOccurrenceKeys
    (input : ListSortInput alpha nu) :
    eraseOccurrenceSlice input.withOccurrenceKeys.slice = input.slice := by
  exact eraseOccurrenceSlice_tagSortSliceOccurrences input.slice

@[simp]
theorem eraseOccurrenceSlice_read
    (slice : SortSlice (Occurrence alpha) nu) (index : Int) :
    (eraseOccurrenceSlice slice).read? index =
      (slice.read? index).map eraseOccurrenceEntry := by
  by_cases hindex : 0 ≤ index <;>
    simp [eraseOccurrenceSlice, SortSlice.read?, hindex]

@[simp]
theorem eraseOccurrenceSlice_write
    (slice : SortSlice (Occurrence alpha) nu) (index : Int)
    (entry : SortSliceEntry (Occurrence alpha) nu) :
    (eraseOccurrenceSlice slice).write? index (eraseOccurrenceEntry entry) =
      (slice.write? index entry).map eraseOccurrenceSlice := by
  by_cases hindex : 0 ≤ index
  · by_cases hin : index.toNat < slice.entries.size
    · simp [eraseOccurrenceSlice, eraseOccurrenceEntry, SortSlice.write?,
        hindex, hin]
    · simp [eraseOccurrenceSlice, SortSlice.write?, hindex, hin]
  · simp [SortSlice.write?, hindex]

def eraseOccurrenceCursorResult
    (result : SortSlice.CursorResult (Occurrence alpha) nu) :
    SortSlice.CursorResult alpha nu :=
  { slice := eraseOccurrenceSlice result.slice
    dst := result.dst
    src := result.src }

def eraseOccurrenceReverseSliceResult
    (result : ReverseSliceResult (Occurrence alpha) nu) :
    ReverseSliceResult alpha nu :=
  { slice := eraseOccurrenceSlice result.slice
    fuelExhausted := result.fuelExhausted }

@[simp]
theorem eraseOccurrenceSlice_copyFrom
    (destination source : SortSlice (Occurrence alpha) nu) (dst src : Int) :
    (eraseOccurrenceSlice destination).copyFrom?
        (eraseOccurrenceSlice source) dst src =
      (destination.copyFrom? source dst src).map eraseOccurrenceSlice := by
  unfold SortSlice.copyFrom?
  rw [eraseOccurrenceSlice_read]
  cases hread : source.read? src with
  | none => simp
  | some entry =>
      simp only [Option.map_some]
      exact eraseOccurrenceSlice_write destination dst entry

@[simp]
theorem eraseOccurrenceSlice_copy
    (slice : SortSlice (Occurrence alpha) nu) (dst src : Int) :
    (eraseOccurrenceSlice slice).copy? dst src =
      (slice.copy? dst src).map eraseOccurrenceSlice := by
  simp [SortSlice.copy?, eraseOccurrenceSlice_copyFrom]

@[simp]
theorem eraseOccurrenceSlice_copyFromIncr
    (destination source : SortSlice (Occurrence alpha) nu) (dst src : Int) :
    (eraseOccurrenceSlice destination).copyFromIncr?
        (eraseOccurrenceSlice source) dst src =
      (destination.copyFromIncr? source dst src).map
        eraseOccurrenceCursorResult := by
  unfold SortSlice.copyFromIncr?
  rw [eraseOccurrenceSlice_copyFrom]
  cases hcopy : destination.copyFrom? source dst src with
  | none => simp
  | some updated => simp [eraseOccurrenceCursorResult]

@[simp]
theorem eraseOccurrenceSlice_copyFromDecr
    (destination source : SortSlice (Occurrence alpha) nu) (dst src : Int) :
    (eraseOccurrenceSlice destination).copyFromDecr?
        (eraseOccurrenceSlice source) dst src =
      (destination.copyFromDecr? source dst src).map
        eraseOccurrenceCursorResult := by
  unfold SortSlice.copyFromDecr?
  rw [eraseOccurrenceSlice_copyFrom]
  cases hcopy : destination.copyFrom? source dst src with
  | none => simp
  | some updated => simp [eraseOccurrenceCursorResult]

@[simp]
theorem eraseOccurrenceSlice_copyIncr
    (slice : SortSlice (Occurrence alpha) nu) (dst src : Int) :
    (eraseOccurrenceSlice slice).copyIncr? dst src =
      (slice.copyIncr? dst src).map eraseOccurrenceCursorResult := by
  simp [SortSlice.copyIncr?, eraseOccurrenceSlice_copyFromIncr]

@[simp]
theorem eraseOccurrenceSlice_copyDecr
    (slice : SortSlice (Occurrence alpha) nu) (dst src : Int) :
    (eraseOccurrenceSlice slice).copyDecr? dst src =
      (slice.copyDecr? dst src).map eraseOccurrenceCursorResult := by
  simp [SortSlice.copyDecr?, eraseOccurrenceSlice_copyFromDecr]

theorem eraseOccurrenceSlice_memcpyCore (count : Nat)
    (destination source : SortSlice (Occurrence alpha) nu) (dst src : Int) :
    SortSlice.memcpyCore? count (eraseOccurrenceSlice destination)
        (eraseOccurrenceSlice source) dst src =
      (SortSlice.memcpyCore? count destination source dst src).map
        eraseOccurrenceSlice := by
  induction count generalizing destination dst src with
  | zero => rfl
  | succ count ih =>
      simp only [SortSlice.memcpyCore?]
      rw [eraseOccurrenceSlice_copyFrom]
      cases hcopy : destination.copyFrom? source dst src with
      | none => simp
      | some updated => simp [ih]

theorem eraseOccurrenceSlice_memmoveForward (count : Nat)
    (slice : SortSlice (Occurrence alpha) nu) (dst src : Int) :
    SortSlice.memmoveForward? count (eraseOccurrenceSlice slice) dst src =
      (SortSlice.memmoveForward? count slice dst src).map
        eraseOccurrenceSlice := by
  induction count generalizing slice dst src with
  | zero => rfl
  | succ count ih =>
      simp only [SortSlice.memmoveForward?]
      rw [eraseOccurrenceSlice_copy]
      cases hcopy : slice.copy? dst src with
      | none => simp
      | some updated => simp [ih]

theorem eraseOccurrenceSlice_memmoveBackward (count : Nat)
    (slice : SortSlice (Occurrence alpha) nu) (dst src : Int) :
    SortSlice.memmoveBackward? count (eraseOccurrenceSlice slice) dst src =
      (SortSlice.memmoveBackward? count slice dst src).map
        eraseOccurrenceSlice := by
  induction count generalizing slice dst src with
  | zero => rfl
  | succ count ih =>
      simp only [SortSlice.memmoveBackward?]
      rw [eraseOccurrenceSlice_copy]
      cases hcopy : slice.copy? (dst + Int.ofNat count)
          (src + Int.ofNat count) with
      | none => simp
      | some updated => simp [ih]

@[simp]
theorem eraseOccurrenceSlice_memmove
    (slice : SortSlice (Occurrence alpha) nu) (dst src : Int) (count : Nat) :
    (eraseOccurrenceSlice slice).memmove? dst src count =
      (slice.memmove? dst src count).map eraseOccurrenceSlice := by
  simp only [SortSlice.memmove?]
  cases SortSlice.memmoveDirection dst src <;>
    simp [eraseOccurrenceSlice_memmoveForward,
      eraseOccurrenceSlice_memmoveBackward]

@[simp]
theorem eraseOccurrencePushPendingRun
    (state : MergeState (Occurrence alpha) nu) (run : PendingRun) :
    pushPendingRun (eraseOccurrenceMergeState state) run =
      eraseOccurrenceMergeState (pushPendingRun state run) := by
  rfl

@[simp]
theorem eraseOccurrenceInstallMinrunState
    (state : MergeState (Occurrence alpha) nu) (minrun : MinrunState) :
    installMinrunState (eraseOccurrenceMergeState state) minrun =
      eraseOccurrenceMergeState (installMinrunState state minrun) := by
  rfl

@[simp]
theorem eraseOccurrenceMergeState_setData
    (state : MergeState (Occurrence alpha) nu)
    (data : SortSlice (Occurrence alpha) nu) :
    { eraseOccurrenceMergeState state with
        data := eraseOccurrenceSlice data } =
      eraseOccurrenceMergeState { state with data := data } := by
  rfl

@[simp]
theorem eraseOccurrenceMergeState_setPending
    (state : MergeState (Occurrence alpha) nu) (pending : Array PendingRun) :
    { eraseOccurrenceMergeState state with pending := pending } =
      eraseOccurrenceMergeState { state with pending := pending } := by
  rfl

theorem expandedEraseOccurrenceMergeStateWithMinGallop
    (state : MergeState (Occurrence alpha) nu) (minGallop : PySSize) :
    ({ min_gallop := minGallop
       listlen := (eraseOccurrenceMergeState state).listlen
       basekeys := (eraseOccurrenceMergeState state).basekeys
       data := eraseOccurrenceSlice state.data
       a := eraseOccurrenceTempStorage state.a
       alloced := (eraseOccurrenceMergeState state).alloced
       pending := (eraseOccurrenceMergeState state).pending
       key_compare := (eraseOccurrenceMergeState state).key_compare
       mr_current := (eraseOccurrenceMergeState state).mr_current
       mr_e := (eraseOccurrenceMergeState state).mr_e
       mr_mask := (eraseOccurrenceMergeState state).mr_mask } :
        MergeState alpha nu) =
      eraseOccurrenceMergeState { state with min_gallop := minGallop } := by
  rfl

@[simp]
theorem iflt_eraseOccurrence
    (lt : BoolComparator alpha) (left right : Occurrence alpha) :
    iflt lt left.value right.value =
      iflt (occurrenceComparator lt) left right := by
  rfl

/-! ## Allocation and galloping -/

def eraseOccurrenceMergeGetmemResult
    (result : MergeGetmemResult (Occurrence alpha) nu) :
    MergeGetmemResult alpha nu :=
  { result with state := eraseOccurrenceMergeState result.state }

@[simp]
theorem eraseOccurrenceMergeGetmemResult_state
    (result : MergeGetmemResult (Occurrence alpha) nu) :
    (eraseOccurrenceMergeGetmemResult result).state =
      eraseOccurrenceMergeState result.state := rfl

@[simp]
theorem eraseOccurrenceMergeGetmemResult_outcome
    (result : MergeGetmemResult (Occurrence alpha) nu) :
    (eraseOccurrenceMergeGetmemResult result).outcome = result.outcome := rfl

@[simp]
theorem eraseOccurrenceMergeFreemem
    (state : MergeState (Occurrence alpha) nu) :
    mergeFreemem (eraseOccurrenceMergeState state) =
      eraseOccurrenceMergeState (mergeFreemem state) := by
  by_cases hinline : state.a.backing = .inline <;>
    simp [mergeFreemem, hinline, eraseOccurrenceMergeState,
      eraseOccurrenceTempStorage]

@[simp]
theorem eraseOccurrenceMergeGetmemAllocationLimit
    (storage : TempStorage (Occurrence alpha) nu) :
    mergeGetmemAllocationLimit (eraseOccurrenceTempStorage storage) =
      mergeGetmemAllocationLimit storage := by
  rfl

@[simp]
theorem eraseOccurrenceMergeGetmem
    (state : MergeState (Occurrence alpha) nu) (need : PySSize) :
    mergeGetmem (eraseOccurrenceMergeState state) need =
      eraseOccurrenceMergeGetmemResult (mergeGetmem state need) := by
  have hlimit :
      mergeGetmemAllocationLimit (eraseOccurrenceMergeState state).a =
        mergeGetmemAllocationLimit state.a := by rfl
  rw [mergeGetmem, mergeGetmem]
  rw [eraseOccurrenceMergeState_alloced, hlimit]
  by_cases hreuse : need.sle state.alloced = true
  · simp [hreuse, eraseOccurrenceMergeGetmemResult]
  · have hreuseFalse : need.sle state.alloced = false := by
      cases h : need.sle state.alloced <;> simp_all
    by_cases hguard : mergeGetmemAllocationLimit state.a < need.toNat
    · simp only [hreuseFalse, Bool.false_eq_true, if_false, hguard, if_true,
        eraseOccurrenceMergeGetmemResult]
      rw [eraseOccurrenceMergeFreemem]
    · simp only [hreuseFalse, Bool.false_eq_true, if_false, hguard]
      rw [eraseOccurrenceMergeFreemem]
      simp [eraseOccurrenceMergeGetmemResult, eraseOccurrenceMergeState,
        eraseOccurrenceTempStorage]

theorem eraseOccurrenceGallopLeftRightExponential
    (lt : BoolComparator alpha) (fuel : Nat)
    (slice : SortSlice (Occurrence alpha) nu) (base : Int)
    (key : Occurrence alpha) (hint maxOffset lastOffset offset : Nat) :
    gallopLeftRightExponential? fuel lt (eraseOccurrenceSlice slice) base
        key.value hint maxOffset lastOffset offset =
      gallopLeftRightExponential? fuel (occurrenceComparator lt)
        slice base key hint maxOffset lastOffset offset := by
  induction fuel generalizing lastOffset offset with
  | zero => rfl
  | succ fuel ih =>
      simp only [gallopLeftRightExponential?]
      by_cases hactive : offset < maxOffset
      · rw [if_pos hactive, if_pos hactive, eraseOccurrenceSlice_read]
        cases hread : slice.read? (base + Int.ofNat hint + Int.ofNat offset) with
        | none => rfl
        | some entry =>
            simp only [Option.map_some, gallopBindOptionAcross]
            simp only [eraseOccurrenceEntry_key, iflt_eraseOccurrence]
            split <;> simp [ih]
      · simp [hactive]

theorem eraseOccurrenceGallopLeftLeftExponential
    (lt : BoolComparator alpha) (fuel : Nat)
    (slice : SortSlice (Occurrence alpha) nu) (base : Int)
    (key : Occurrence alpha) (hint maxOffset lastOffset offset : Nat) :
    gallopLeftLeftExponential? fuel lt (eraseOccurrenceSlice slice) base
        key.value hint maxOffset lastOffset offset =
      gallopLeftLeftExponential? fuel (occurrenceComparator lt)
        slice base key hint maxOffset lastOffset offset := by
  induction fuel generalizing lastOffset offset with
  | zero => rfl
  | succ fuel ih =>
      simp only [gallopLeftLeftExponential?]
      by_cases hactive : offset < maxOffset
      · rw [if_pos hactive, if_pos hactive, eraseOccurrenceSlice_read]
        cases hread : slice.read? (base + Int.ofNat hint - Int.ofNat offset) with
        | none => rfl
        | some entry =>
            simp only [Option.map_some, gallopBindOptionAcross]
            simp only [eraseOccurrenceEntry_key, iflt_eraseOccurrence]
            split <;> simp [ih]
      · simp [hactive]

theorem eraseOccurrenceGallopLeftBinary
    (lt : BoolComparator alpha) (fuel : Nat)
    (slice : SortSlice (Occurrence alpha) nu) (base : Int)
    (key : Occurrence alpha) (lower upper : Nat) :
    gallopLeftBinary? fuel lt (eraseOccurrenceSlice slice) base key.value
        lower upper =
      gallopLeftBinary? fuel (occurrenceComparator lt) slice base key
        lower upper := by
  induction fuel generalizing lower upper with
  | zero => rfl
  | succ fuel ih =>
      simp only [gallopLeftBinary?]
      by_cases hactive : lower < upper
      · rw [if_pos hactive, if_pos hactive, eraseOccurrenceSlice_read]
        cases hread : slice.read?
            (base + Int.ofNat (lower + (upper - lower) / 2)) with
        | none => rfl
        | some entry =>
            simp only [Option.map_some, gallopBindOptionAcross]
            simp only [eraseOccurrenceEntry_key, iflt_eraseOccurrence]
            split <;> simp [ih]
      · simp [hactive]

@[simp]
theorem eraseOccurrenceFinishGallopLeft
    (lt : BoolComparator alpha) (fuel : Nat)
    (slice : SortSlice (Occurrence alpha) nu) (base : Int)
    (key : Occurrence alpha) (n : Nat) (lastOffset upperOffset : Int)
    (exponentialFuelExhausted : Bool) :
    finishGallopLeft? fuel lt (eraseOccurrenceSlice slice) base key.value n
        lastOffset upperOffset exponentialFuelExhausted =
      finishGallopLeft? fuel (occurrenceComparator lt) slice base key n
        lastOffset upperOffset exponentialFuelExhausted := by
  unfold finishGallopLeft?
  by_cases hbounds :
      -1 ≤ lastOffset ∧ lastOffset < upperOffset ∧ upperOffset ≤ Int.ofNat n
  · rw [if_pos hbounds, if_pos hbounds]
    by_cases hnonnegative : 0 ≤ lastOffset + 1 ∧ 0 ≤ upperOffset
    · rw [if_pos hnonnegative, if_pos hnonnegative]
      by_cases hexhausted : exponentialFuelExhausted = true
      · simp [hexhausted]
      · simp [hexhausted, eraseOccurrenceGallopLeftBinary]
    · rw [if_neg hnonnegative, if_neg hnonnegative]
  · rw [if_neg hbounds, if_neg hbounds]

theorem eraseOccurrenceGallopRightLeftExponential
    (lt : BoolComparator alpha) (fuel : Nat)
    (slice : SortSlice (Occurrence alpha) nu) (base : Int)
    (key : Occurrence alpha) (hint maxOffset lastOffset offset : Nat) :
    gallopRightLeftExponential? fuel lt (eraseOccurrenceSlice slice) base
        key.value hint maxOffset lastOffset offset =
      gallopRightLeftExponential? fuel (occurrenceComparator lt)
        slice base key hint maxOffset lastOffset offset := by
  induction fuel generalizing lastOffset offset with
  | zero => rfl
  | succ fuel ih =>
      simp only [gallopRightLeftExponential?]
      by_cases hactive : offset < maxOffset
      · rw [if_pos hactive, if_pos hactive, eraseOccurrenceSlice_read]
        cases hread : slice.read? (base + Int.ofNat hint - Int.ofNat offset) with
        | none => rfl
        | some entry =>
            simp only [Option.map_some, gallopBindOptionAcross]
            simp only [eraseOccurrenceEntry_key, iflt_eraseOccurrence]
            split <;> simp [ih]
      · simp [hactive]

theorem eraseOccurrenceGallopRightRightExponential
    (lt : BoolComparator alpha) (fuel : Nat)
    (slice : SortSlice (Occurrence alpha) nu) (base : Int)
    (key : Occurrence alpha) (hint maxOffset lastOffset offset : Nat) :
    gallopRightRightExponential? fuel lt (eraseOccurrenceSlice slice) base
        key.value hint maxOffset lastOffset offset =
      gallopRightRightExponential? fuel (occurrenceComparator lt)
        slice base key hint maxOffset lastOffset offset := by
  induction fuel generalizing lastOffset offset with
  | zero => rfl
  | succ fuel ih =>
      simp only [gallopRightRightExponential?]
      by_cases hactive : offset < maxOffset
      · rw [if_pos hactive, if_pos hactive, eraseOccurrenceSlice_read]
        cases hread : slice.read? (base + Int.ofNat hint + Int.ofNat offset) with
        | none => rfl
        | some entry =>
            simp only [Option.map_some, gallopBindOptionAcross]
            simp only [eraseOccurrenceEntry_key, iflt_eraseOccurrence]
            split <;> simp [ih]
      · simp [hactive]

theorem eraseOccurrenceGallopRightBinary
    (lt : BoolComparator alpha) (fuel : Nat)
    (slice : SortSlice (Occurrence alpha) nu) (base : Int)
    (key : Occurrence alpha) (lower upper : Nat) :
    gallopRightBinary? fuel lt (eraseOccurrenceSlice slice) base key.value
        lower upper =
      gallopRightBinary? fuel (occurrenceComparator lt) slice base key
        lower upper := by
  induction fuel generalizing lower upper with
  | zero => rfl
  | succ fuel ih =>
      simp only [gallopRightBinary?]
      by_cases hactive : lower < upper
      · rw [if_pos hactive, if_pos hactive, eraseOccurrenceSlice_read]
        cases hread : slice.read?
            (base + Int.ofNat (lower + (upper - lower) / 2)) with
        | none => rfl
        | some entry =>
            simp only [Option.map_some, gallopBindOptionAcross]
            simp only [eraseOccurrenceEntry_key, iflt_eraseOccurrence]
            split <;> simp [ih]
      · simp [hactive]

@[simp]
theorem eraseOccurrenceFinishGallopRight
    (lt : BoolComparator alpha) (fuel : Nat)
    (slice : SortSlice (Occurrence alpha) nu) (base : Int)
    (key : Occurrence alpha) (n : Nat) (lastOffset upperOffset : Int)
    (exponentialFuelExhausted : Bool) :
    finishGallopRight? fuel lt (eraseOccurrenceSlice slice) base key.value n
        lastOffset upperOffset exponentialFuelExhausted =
      finishGallopRight? fuel (occurrenceComparator lt) slice base key n
        lastOffset upperOffset exponentialFuelExhausted := by
  unfold finishGallopRight?
  by_cases hbounds :
      -1 ≤ lastOffset ∧ lastOffset < upperOffset ∧ upperOffset ≤ Int.ofNat n
  · rw [if_pos hbounds, if_pos hbounds]
    by_cases hnonnegative : 0 ≤ lastOffset + 1 ∧ 0 ≤ upperOffset
    · rw [if_pos hnonnegative, if_pos hnonnegative]
      by_cases hexhausted : exponentialFuelExhausted = true
      · simp [hexhausted]
      · simp [hexhausted, eraseOccurrenceGallopRightBinary]
    · rw [if_neg hnonnegative, if_neg hnonnegative]
  · rw [if_neg hbounds, if_neg hbounds]

@[simp]
theorem eraseOccurrenceGallopLeft
    (lt : BoolComparator alpha)
    (state : MergeState (Occurrence alpha) nu)
    (slice : SortSlice (Occurrence alpha) nu) (base : Int)
    (key : Occurrence alpha) (n hint : Nat)
    (hcompare : state.key_compare = occurrenceComparator lt) :
    gallopLeft? (eraseOccurrenceMergeState state)
        (eraseOccurrenceSlice slice) base key.value n hint =
      gallopLeft? state slice base key n hint := by
  unfold gallopLeft?
  simp only [eraseOccurrenceMergeState_key_compare, hcompare,
    eraseOccurrenceComparator_occurrenceComparator]
  split <;> try rfl
  rw [eraseOccurrenceSlice_read]
  cases hread : slice.read? (base + Int.ofNat hint) with
  | none => rfl
  | some entry =>
      simp only [Option.map_some, gallopBindOptionAcross]
      simp only [eraseOccurrenceEntry_key, iflt_eraseOccurrence]
      split
      · rw [eraseOccurrenceGallopLeftRightExponential]
        cases hexponential : gallopLeftRightExponential? (n + 1)
            (occurrenceComparator lt) slice base key hint (n - hint) 0 1 with
        | none => rfl
        | some exponential =>
            simp [eraseOccurrenceFinishGallopLeft]
      · rw [eraseOccurrenceGallopLeftLeftExponential]
        cases hexponential : gallopLeftLeftExponential? (n + 1)
            (occurrenceComparator lt) slice base key hint (hint + 1) 0 1 with
        | none => rfl
        | some exponential =>
            simp [eraseOccurrenceFinishGallopLeft]

@[simp]
theorem eraseOccurrenceGallopRight
    (lt : BoolComparator alpha)
    (state : MergeState (Occurrence alpha) nu)
    (slice : SortSlice (Occurrence alpha) nu) (base : Int)
    (key : Occurrence alpha) (n hint : Nat)
    (hcompare : state.key_compare = occurrenceComparator lt) :
    gallopRight? (eraseOccurrenceMergeState state)
        (eraseOccurrenceSlice slice) base key.value n hint =
      gallopRight? state slice base key n hint := by
  unfold gallopRight?
  simp only [eraseOccurrenceMergeState_key_compare, hcompare,
    eraseOccurrenceComparator_occurrenceComparator]
  split <;> try rfl
  rw [eraseOccurrenceSlice_read]
  cases hread : slice.read? (base + Int.ofNat hint) with
  | none => rfl
  | some entry =>
      simp only [Option.map_some, gallopBindOptionAcross]
      simp only [eraseOccurrenceEntry_key, iflt_eraseOccurrence]
      split
      · rw [eraseOccurrenceGallopRightLeftExponential]
        cases hexponential : gallopRightLeftExponential? (n + 1)
            (occurrenceComparator lt) slice base key hint (hint + 1) 0 1 with
        | none => rfl
        | some exponential =>
            simp [eraseOccurrenceFinishGallopRight]
      · rw [eraseOccurrenceGallopRightRightExponential]
        cases hexponential : gallopRightRightExponential? (n + 1)
            (occurrenceComparator lt) slice base key hint (n - hint) 0 1 with
        | none => rfl
        | some exponential =>
            simp [eraseOccurrenceFinishGallopRight]

/-! ## Front-end evaluator erasure -/

variable {alpha : Type u} {nu : Type v}

/-! ## Slice reversal -/

theorem eraseOccurrenceReverseSliceLoop (fuel : Nat)
    (slice : SortSlice (Occurrence alpha) nu) (lo hi : Int) :
    reverseSliceLoop? fuel (eraseOccurrenceSlice slice) lo hi =
      (reverseSliceLoop? fuel slice lo hi).map
        eraseOccurrenceReverseSliceResult := by
  induction fuel generalizing slice lo hi with
  | zero => rfl
  | succ fuel ih =>
      simp only [reverseSliceLoop?]
      by_cases hactive : lo < hi
      · rw [if_pos hactive, if_pos hactive]
        rw [eraseOccurrenceSlice_read]
        cases hleft : slice.read? lo with
        | none => simp
        | some left =>
            simp only [Option.map_some]
            rw [eraseOccurrenceSlice_read]
            cases hright : slice.read? hi with
            | none => simp
            | some right =>
                cases hwriteLeft : slice.write? lo right with
                | none => simp [hwriteLeft, eraseOccurrenceSlice_write]
                | some afterLeft =>
                    cases hwriteRight : afterLeft.write? hi left with
                    | none =>
                        simp [hwriteLeft, hwriteRight,
                          eraseOccurrenceSlice_write]
                    | some afterRight =>
                        simp [hwriteLeft, hwriteRight,
                          eraseOccurrenceSlice_write, ih]
      · simp [hactive, eraseOccurrenceReverseSliceResult]

@[simp]
theorem eraseOccurrenceReverseSlice
    (slice : SortSlice (Occurrence alpha) nu) (lo hi : Int) :
    reverseSlice? (eraseOccurrenceSlice slice) lo hi =
      (reverseSlice? slice lo hi).map eraseOccurrenceReverseSliceResult := by
  unfold reverseSlice?
  by_cases horder : lo ≤ hi
  · rw [if_pos horder, if_pos horder]
    by_cases hactive : lo < hi
    · rw [if_pos hactive, if_pos hactive]
      exact eraseOccurrenceReverseSliceLoop (hi - lo).toNat slice lo (hi - 1)
    · simp [hactive, eraseOccurrenceReverseSliceResult]
  · simp [horder]

@[simp]
theorem eraseOccurrenceSortsliceReverse
    (slice : SortSlice (Occurrence alpha) nu) (base : Int) (count : Nat) :
    sortsliceReverse? (eraseOccurrenceSlice slice) base count =
      (sortsliceReverse? slice base count).map
        eraseOccurrenceReverseSliceResult := by
  simp [sortsliceReverse?, eraseOccurrenceReverseSlice]

/-! ## Natural-run detection -/

def eraseOccurrenceCountRunResult
    (result : CountRunResult (Occurrence alpha) nu) :
    CountRunResult alpha nu :=
  { result with slice := eraseOccurrenceSlice result.slice }

@[simp]
theorem eraseOccurrenceCountRunResult_slice
    (result : CountRunResult (Occurrence alpha) nu) :
    (eraseOccurrenceCountRunResult result).slice =
      eraseOccurrenceSlice result.slice := rfl

@[simp]
theorem eraseOccurrenceCountRunResult_length
    (result : CountRunResult (Occurrence alpha) nu) :
    (eraseOccurrenceCountRunResult result).length = result.length := rfl

@[simp]
theorem eraseOccurrenceCountRunResult_fuel
    (result : CountRunResult (Occurrence alpha) nu) :
    (eraseOccurrenceCountRunResult result).fuelExhausted =
      result.fuelExhausted := rfl

def eraseOccurrenceReverseEqualResult
    (result : ReverseEqualResult (Occurrence alpha) nu) :
    ReverseEqualResult alpha nu :=
  { result with slice := eraseOccurrenceSlice result.slice }

@[simp]
theorem eraseOccurrenceReverseEqualResult_slice
    (result : ReverseEqualResult (Occurrence alpha) nu) :
    (eraseOccurrenceReverseEqualResult result).slice =
      eraseOccurrenceSlice result.slice := rfl

@[simp]
theorem eraseOccurrenceReverseEqualResult_fuel
    (result : ReverseEqualResult (Occurrence alpha) nu) :
    (eraseOccurrenceReverseEqualResult result).fuelExhausted =
      result.fuelExhausted := rfl

def eraseOccurrenceDescendingScanResult
    (result : DescendingScanResult (Occurrence alpha) nu) :
    DescendingScanResult alpha nu :=
  { result with slice := eraseOccurrenceSlice result.slice }

@[simp]
theorem eraseOccurrenceDescendingScanResult_slice
    (result : DescendingScanResult (Occurrence alpha) nu) :
    (eraseOccurrenceDescendingScanResult result).slice =
      eraseOccurrenceSlice result.slice := rfl

@[simp]
theorem eraseOccurrenceDescendingScanResult_length
    (result : DescendingScanResult (Occurrence alpha) nu) :
    (eraseOccurrenceDescendingScanResult result).length = result.length := rfl

@[simp]
theorem eraseOccurrenceDescendingScanResult_equalTail
    (result : DescendingScanResult (Occurrence alpha) nu) :
    (eraseOccurrenceDescendingScanResult result).equalTail =
      result.equalTail := rfl

@[simp]
theorem eraseOccurrenceDescendingScanResult_fuel
    (result : DescendingScanResult (Occurrence alpha) nu) :
    (eraseOccurrenceDescendingScanResult result).fuelExhausted =
      result.fuelExhausted := rfl

@[simp]
theorem iflt_eraseOccurrenceEntry_occurrenceComparator
    (lt : BoolComparator alpha)
    (left right : SortSliceEntry (Occurrence alpha) nu) :
    iflt lt (eraseOccurrenceEntry left).key
        (eraseOccurrenceEntry right).key =
      iflt (occurrenceComparator lt) left.key right.key := by
  rfl

theorem eraseOccurrenceAscendingScan (lt : BoolComparator alpha)
    (fuel : Nat) (slice : SortSlice (Occurrence alpha) nu) (base : Int)
    (nremaining n : Nat) :
    ascendingScan? fuel lt (eraseOccurrenceSlice slice)
        base nremaining n =
      ascendingScan? fuel (occurrenceComparator lt) slice
        base nremaining n := by
  induction fuel generalizing n with
  | zero => rfl
  | succ fuel ih =>
      simp only [ascendingScan?]
      by_cases hscan : n < nremaining
      · rw [if_pos hscan, if_pos hscan]
        rw [eraseOccurrenceSlice_read]
        cases hprevious : slice.read? (base + Int.ofNat (n - 1)) with
        | none => rfl
        | some previous =>
            simp only [Option.map_some, countRunBindOptionAcross]
            rw [eraseOccurrenceSlice_read]
            cases hnext : slice.read? (base + Int.ofNat n) with
            | none => rfl
            | some next =>
                simp only [Option.map_some]
                rw [iflt_eraseOccurrenceEntry_occurrenceComparator]
                split <;> simp [ih]
      · simp [hscan]

@[simp]
theorem eraseOccurrenceReverseLastEqual
    (slice : SortSlice (Occurrence alpha) nu) (base : Int) (n neq : Nat) :
    reverseLastEqual? (eraseOccurrenceSlice slice) base n neq =
      (reverseLastEqual? slice base n neq).map
        eraseOccurrenceReverseEqualResult := by
  unfold reverseLastEqual?
  by_cases heq : neq = 0
  · simp [heq, eraseOccurrenceReverseEqualResult]
  · rw [if_neg heq, if_neg heq]
    dsimp only
    rw [eraseOccurrenceSortsliceReverse]
    cases hreversed : sortsliceReverse? slice
        (base + Int.ofNat n - Int.ofNat (neq + 1)) (neq + 1) with
    | none => simp
    | some reversed =>
        simp [eraseOccurrenceReverseEqualResult,
          eraseOccurrenceReverseSliceResult]

theorem eraseOccurrenceDescendingScan (lt : BoolComparator alpha)
    (fuel : Nat) (slice : SortSlice (Occurrence alpha) nu) (base : Int)
    (nremaining n neq : Nat) :
    descendingScan? fuel lt (eraseOccurrenceSlice slice)
        base nremaining n neq =
      (descendingScan? fuel (occurrenceComparator lt) slice
        base nremaining n neq).map eraseOccurrenceDescendingScanResult := by
  induction fuel generalizing slice n neq with
  | zero => rfl
  | succ fuel ih =>
      simp only [descendingScan?]
      by_cases hscan : n < nremaining
      · rw [if_pos hscan, if_pos hscan]
        rw [eraseOccurrenceSlice_read]
        cases hprevious : slice.read? (base + Int.ofNat (n - 1)) with
        | none => simp
        | some previous =>
            simp only [Option.map_some]
            rw [eraseOccurrenceSlice_read]
            cases hnext : slice.read? (base + Int.ofNat n) with
            | none => simp
            | some next =>
                simp only [Option.map_some, Option.bind_eq_bind,
                  Option.bind_some]
                rw [iflt_eraseOccurrenceEntry_occurrenceComparator]
                by_cases hless :
                    iflt (occurrenceComparator lt) next.key previous.key = true
                · simp only [iflt_eq] at hless
                  simp only [iflt_eq]
                  rw [eraseOccurrenceReverseLastEqual]
                  cases hreversed : reverseLastEqual? slice base n neq with
                  | none => simp [hless]
                  | some reversed =>
                      cases hfuel : reversed.fuelExhausted <;>
                        simp [hless, hfuel,
                          eraseOccurrenceReverseEqualResult,
                          eraseOccurrenceDescendingScanResult, ih]
                · rw [iflt_eraseOccurrenceEntry_occurrenceComparator]
                  by_cases hgreater :
                      iflt (occurrenceComparator lt) previous.key next.key = true
                  · simp only [iflt_eq] at hless hgreater
                    simp [iflt_eq, hless, hgreater,
                      eraseOccurrenceDescendingScanResult]
                  · simp only [iflt_eq] at hless hgreater
                    simp [iflt_eq, hless, hgreater, ih]
      · simp [hscan, eraseOccurrenceDescendingScanResult]

theorem eraseOccurrenceFinishDescending (lt : BoolComparator alpha)
    (state : MergeState (Occurrence alpha) nu)
    (slice : SortSlice (Occurrence alpha) nu) (base : Int)
    (nremaining n : Nat)
    (hcompare : state.key_compare = occurrenceComparator lt) :
    finishDescending? (eraseOccurrenceMergeState state)
        (eraseOccurrenceSlice slice) base nremaining n =
      (finishDescending? state slice base nremaining n).map
        eraseOccurrenceCountRunResult := by
  unfold finishDescending?
  simp only [eraseOccurrenceMergeState_key_compare, hcompare,
    eraseOccurrenceComparator_occurrenceComparator]
  rw [eraseOccurrenceDescendingScan]
  cases hdescending : descendingScan? nremaining
      (occurrenceComparator lt) slice base nremaining n 0 with
  | none => simp
  | some descending =>
      by_cases hfuel : descending.fuelExhausted = true
      · simp [hfuel, eraseOccurrenceDescendingScanResult,
          eraseOccurrenceCountRunResult]
      · cases hequal : reverseLastEqual? descending.slice base
            descending.length descending.equalTail with
        | none =>
            simp [hfuel, hequal, eraseOccurrenceDescendingScanResult]
        | some equalReversed =>
            by_cases hequalFuel : equalReversed.fuelExhausted = true
            · simp [hfuel, hequal, hequalFuel,
                eraseOccurrenceDescendingScanResult,
                eraseOccurrenceReverseEqualResult,
                eraseOccurrenceCountRunResult]
            · cases hwhole : sortsliceReverse? equalReversed.slice base
                  descending.length with
              | none =>
                  simp [hfuel, hequal, hequalFuel, hwhole,
                    eraseOccurrenceDescendingScanResult,
                    eraseOccurrenceReverseEqualResult]
              | some wholeReversed =>
                  by_cases hwholeFuel : wholeReversed.fuelExhausted = true
                  · simp [hfuel, hequal, hequalFuel, hwhole, hwholeFuel,
                      eraseOccurrenceDescendingScanResult,
                      eraseOccurrenceReverseEqualResult,
                      eraseOccurrenceReverseSliceResult,
                      eraseOccurrenceCountRunResult]
                  · simp only [hfuel, Bool.false_eq_true, if_false,
                      Option.map_some, Option.bind_eq_bind, Option.bind_some,
                      eraseOccurrenceDescendingScanResult_fuel,
                      eraseOccurrenceDescendingScanResult_slice,
                      eraseOccurrenceDescendingScanResult_length,
                      eraseOccurrenceDescendingScanResult_equalTail]
                    rw [eraseOccurrenceReverseLastEqual]
                    simp only [hequal, Option.map_some, Option.bind_some,
                      eraseOccurrenceReverseEqualResult_fuel,
                      eraseOccurrenceReverseEqualResult_slice, hequalFuel,
                      Bool.false_eq_true, if_false]
                    rw [eraseOccurrenceSortsliceReverse]
                    simp only [hwhole, Option.map_some, Option.bind_some,
                      eraseOccurrenceReverseSliceResult, hwholeFuel,
                      Bool.false_eq_true, if_false]
                    rw [eraseOccurrenceAscendingScan]
                    cases hascending : ascendingScan? nremaining
                        (occurrenceComparator lt) wholeReversed.slice base
                        nremaining descending.length <;> rfl

theorem eraseOccurrenceCountRun (lt : BoolComparator alpha)
    (state : MergeState (Occurrence alpha) nu)
    (slice : SortSlice (Occurrence alpha) nu) (base : Int)
    (nremaining : Nat)
    (hcompare : state.key_compare = occurrenceComparator lt) :
    countRun? (eraseOccurrenceMergeState state)
        (eraseOccurrenceSlice slice) base nremaining =
      (countRun? state slice base nremaining).map
        eraseOccurrenceCountRunResult := by
  unfold countRun?
  simp only [eraseOccurrenceMergeState_key_compare, hcompare,
    eraseOccurrenceComparator_occurrenceComparator]
  by_cases hvalid : 0 < nremaining ∧ nremaining ≤ PY_SSIZE_T_MAX
  · rw [if_pos hvalid, if_pos hvalid, eraseOccurrenceAscendingScan]
    cases hascending : ascendingScan? nremaining
        (occurrenceComparator lt) slice base nremaining 1 with
    | none => simp [countRunBindOptionAcross]
    | some ascending =>
        cases hfuel : ascending.fuelExhausted with
        | true =>
            simp [countRunBindOptionAcross, hfuel,
              eraseOccurrenceCountRunResult]
        | false =>
            by_cases hcomplete : ascending.length = nremaining
            · simp [countRunBindOptionAcross, hfuel, hcomplete,
                eraseOccurrenceCountRunResult]
            · by_cases hlong : 1 < ascending.length
              · simp only [countRunBindOptionAcross, hfuel,
                    Bool.false_eq_true, if_false, hcomplete, hlong, if_true]
                rw [eraseOccurrenceSlice_read]
                cases hfirst : slice.read? base with
                | none => simp
                | some first =>
                    simp only [Option.map_some]
                    rw [eraseOccurrenceSlice_read]
                    cases hlast : slice.read?
                        (base + Int.ofNat (ascending.length - 1)) with
                    | none => simp
                    | some last =>
                        simp only [Option.map_some, Option.bind_eq_bind,
                          Option.bind_some]
                        rw [iflt_eraseOccurrenceEntry_occurrenceComparator]
                        by_cases hordered :
                            occurrenceComparator lt first.key last.key = true
                        · simp [hordered, iflt,
                            eraseOccurrenceCountRunResult]
                        · cases hreversed : sortsliceReverse? slice base
                              ascending.length with
                          | none => simp [hordered, iflt, hreversed]
                          | some reversed =>
                              cases hreverseFuel : reversed.fuelExhausted with
                              | true =>
                                  simp [hordered, iflt, hreversed,
                                    hreverseFuel,
                                    eraseOccurrenceReverseSliceResult,
                                    eraseOccurrenceCountRunResult]
                              | false =>
                                  simp [hordered, iflt, hreversed,
                                    hreverseFuel,
                                    eraseOccurrenceReverseSliceResult,
                                    eraseOccurrenceFinishDescending lt state
                                      reversed.slice base nremaining
                                      (ascending.length + 1) hcompare]
              · simp only [countRunBindOptionAcross, hfuel,
                    Bool.false_eq_true, if_false, hcomplete, hlong]
                exact eraseOccurrenceFinishDescending lt state slice base
                  nremaining (ascending.length + 1) hcompare
  · simp [hvalid]

/-! ## Stable binary insertion -/

def eraseOccurrenceBinarysortResult
    (result : BinarysortResult (Occurrence alpha) nu) :
    BinarysortResult alpha nu :=
  { result with slice := eraseOccurrenceSlice result.slice }

@[simp]
theorem eraseOccurrenceBinarysortResult_slice
    (result : BinarysortResult (Occurrence alpha) nu) :
    (eraseOccurrenceBinarysortResult result).slice =
      eraseOccurrenceSlice result.slice := rfl

@[simp]
theorem eraseOccurrenceBinarysortResult_fuel
    (result : BinarysortResult (Occurrence alpha) nu) :
    (eraseOccurrenceBinarysortResult result).fuelExhausted =
      result.fuelExhausted := rfl

theorem eraseOccurrenceBinarysortSearch (lt : BoolComparator alpha)
    (fuel : Nat) (slice : SortSlice (Occurrence alpha) nu) (base : Int)
    (pivot : SortSliceEntry (Occurrence alpha) nu) (left right : Nat) :
    binarysortSearch? fuel lt (eraseOccurrenceSlice slice) base
        (eraseOccurrenceEntry pivot) left right =
      binarysortSearch? fuel (occurrenceComparator lt) slice base pivot
        left right := by
  induction fuel generalizing left right with
  | zero => rfl
  | succ fuel ih =>
      simp only [binarysortSearch?]
      by_cases hsearch : left < right
      · rw [if_pos hsearch, if_pos hsearch, eraseOccurrenceSlice_read]
        cases hread : slice.read?
            (base + Int.ofNat ((left + right) / 2)) with
        | none => rfl
        | some entry =>
            simp only [Option.map_some, binarysortBindOptionAcross]
            rw [iflt_eraseOccurrenceEntry_occurrenceComparator]
            split <;> simp [ih]
      · simp [hsearch]

theorem eraseOccurrenceBinarysortLoop (lt : BoolComparator alpha)
    (fuel : Nat) (state : MergeState (Occurrence alpha) nu)
    (slice : SortSlice (Occurrence alpha) nu) (base : Int) (n ok : Nat)
    (hcompare : state.key_compare = occurrenceComparator lt) :
    binarysortLoop? fuel (eraseOccurrenceMergeState state)
        (eraseOccurrenceSlice slice) base n ok =
      (binarysortLoop? fuel state slice base n ok).map
        eraseOccurrenceBinarysortResult := by
  induction fuel generalizing slice ok with
  | zero => rfl
  | succ fuel ih =>
      simp only [binarysortLoop?]
      by_cases hloop : ok < n
      · rw [if_pos hloop, if_pos hloop, eraseOccurrenceSlice_read]
        cases hpivot : slice.read? (base + Int.ofNat ok) with
        | none => simp [binarysortBindOptionAcross]
        | some pivot =>
            simp only [Option.map_some, binarysortBindOptionAcross]
            simp only [eraseOccurrenceMergeState_key_compare, hcompare,
              eraseOccurrenceComparator_occurrenceComparator]
            rw [eraseOccurrenceBinarysortSearch]
            cases hsearch : binarysortSearch? (ok + 1)
                (occurrenceComparator lt) slice base pivot 0 ok with
            | none => simp
            | some search =>
                cases hfuel : search.fuelExhausted with
                | true =>
                    simp [hfuel, eraseOccurrenceBinarysortResult]
                | false =>
                    simp only [hfuel, Bool.false_eq_true, if_false]
                    rw [eraseOccurrenceSlice_memmove]
                    cases hmove : slice.memmove?
                        (base + Int.ofNat (search.position + 1))
                        (base + Int.ofNat search.position)
                        (ok - search.position) with
                    | none => simp
                    | some moved =>
                        simp only [Option.map_some, Int.ofNat_eq_natCast,
                          Option.bind_eq_bind, Option.bind_some,
                          eraseOccurrenceSlice_write, Option.map_bind,
                          Function.comp_apply]
                        rw [Option.bind_map]
                        apply Option.bind_congr
                        intro inserted _
                        exact ih inserted (ok + 1)
      · rw [if_neg hloop, if_neg hloop]
        rfl

@[simp]
theorem eraseOccurrenceBinarysort (lt : BoolComparator alpha)
    (state : MergeState (Occurrence alpha) nu)
    (slice : SortSlice (Occurrence alpha) nu) (base : Int) (n ok : Nat)
    (hcompare : state.key_compare = occurrenceComparator lt) :
    binarysort? (eraseOccurrenceMergeState state)
        (eraseOccurrenceSlice slice) base n ok =
      (binarysort? state slice base n ok).map
        eraseOccurrenceBinarysortResult := by
  unfold binarysort?
  by_cases hvalid : 1 ≤ n ∧ ok ≤ n ∧ n ≤ MAX_MINRUN.toNat
  · rw [if_pos hvalid, if_pos hvalid]
    split <;>
      apply eraseOccurrenceBinarysortLoop lt n state slice base n <;>
      exact hcompare
  · simp [hvalid]


end CPythonListsort
