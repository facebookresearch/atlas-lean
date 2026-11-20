/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Code.Correctness.ScanStepCorrectness
import Code.Correctness.MergeForceCollapseCorrectness

/-!
# Equivariance under mirrored occurrence origins

Reverse-mode correctness compares the actual initially reversed execution,
whose carried origins run backwards, with a canonical execution over the
reversed source.  This file supplies the explicit relabeling and proves that
the implementation observes only occurrence values: changing every origin by
the same mirror map commutes with the data-moving evaluator.
-/

namespace CPythonListsort

universe u v

variable {alpha : Type u} {nu : Type v}

/-- Mirror an absolute origin inside a slice of length `size`, leaving origins
outside that slice unchanged.  The outside branch makes this a total
involution even on stale or deliberately fabricated temporary cells. -/
def mirrorOrigin (size origin : Nat) : Nat :=
  if origin < size then size - 1 - origin else origin

theorem mirrorOrigin_of_lt (size origin : Nat) (h : origin < size) :
    mirrorOrigin size origin = size - 1 - origin := by
  simp [mirrorOrigin, h]

@[simp]
theorem mirrorOrigin_involutive (size origin : Nat) :
    mirrorOrigin size (mirrorOrigin size origin) = origin := by
  by_cases h : origin < size
  · have hmirror : size - 1 - origin < size := by omega
    simp [mirrorOrigin, h, hmirror]
    omega
  · simp [mirrorOrigin, h]

/-- Relabel one carried occurrence without changing its observable value. -/
def mirrorOccurrence (size : Nat) (entry : Occurrence alpha) : Occurrence alpha :=
  { value := entry.value, origin := mirrorOrigin size entry.origin }

/-- Relabel the key of one synchronized entry, preserving its payload. -/
def mirrorSortSliceEntry (size : Nat)
    (entry : SortSliceEntry (Occurrence alpha) nu) :
    SortSliceEntry (Occurrence alpha) nu :=
  { key := mirrorOccurrence size entry.key, value := entry.value }

/-- Relabel every occurrence key in a synchronized slice. -/
def mirrorSortSlice (size : Nat) (slice : SortSlice (Occurrence alpha) nu) :
    SortSlice (Occurrence alpha) nu :=
  { entries := slice.entries.map (mirrorSortSliceEntry size) }

/-- Relabel initialized temporary cells while retaining allocation metadata. -/
def mirrorTempStorage (size : Nat)
    (storage : TempStorage (Occurrence alpha) nu) :
    TempStorage (Occurrence alpha) nu :=
  { cells := storage.cells.map (Option.map (mirrorSortSliceEntry size))
    backing := storage.backing
    hasValues := storage.hasValues }

/-- Relabel every occurrence-bearing store in a merge state.  All control,
layout, allocation, and comparator fields are retained literally. -/
def mirrorMergeState (size : Nat)
    (state : MergeState (Occurrence alpha) nu) :
    MergeState (Occurrence alpha) nu :=
  { state with
    data := mirrorSortSlice size state.data
    a := mirrorTempStorage size state.a }

@[simp]
theorem mirrorOccurrence_value (size : Nat) (entry : Occurrence alpha) :
    (mirrorOccurrence size entry).value = entry.value := rfl

@[simp]
theorem mirrorOccurrence_origin (size : Nat) (entry : Occurrence alpha) :
    (mirrorOccurrence size entry).origin = mirrorOrigin size entry.origin := rfl

@[simp]
theorem mirrorOccurrence_involutive (size : Nat) (entry : Occurrence alpha) :
    mirrorOccurrence size (mirrorOccurrence size entry) = entry := by
  cases entry
  simp [mirrorOccurrence]

@[simp]
theorem mirrorSortSliceEntry_key (size : Nat)
    (entry : SortSliceEntry (Occurrence alpha) nu) :
    (mirrorSortSliceEntry size entry).key = mirrorOccurrence size entry.key := rfl

@[simp]
theorem mirrorSortSliceEntry_value (size : Nat)
    (entry : SortSliceEntry (Occurrence alpha) nu) :
    (mirrorSortSliceEntry size entry).value = entry.value := rfl

@[simp]
theorem mirrorSortSliceEntry_involutive (size : Nat)
    (entry : SortSliceEntry (Occurrence alpha) nu) :
    mirrorSortSliceEntry size (mirrorSortSliceEntry size entry) = entry := by
  cases entry
  simp [mirrorSortSliceEntry]

@[simp]
theorem mirrorSortSlice_involutive (size : Nat)
    (slice : SortSlice (Occurrence alpha) nu) :
    mirrorSortSlice size (mirrorSortSlice size slice) = slice := by
  cases slice with
  | mk entries =>
      simp only [mirrorSortSlice, Array.map_map]
      simp [Function.comp_def]

@[simp]
theorem mirrorTempStorage_involutive (size : Nat)
    (storage : TempStorage (Occurrence alpha) nu) :
    mirrorTempStorage size (mirrorTempStorage size storage) = storage := by
  cases storage with
  | mk cells backing hasValues =>
      simp [mirrorTempStorage, Array.map_map, Function.comp_def]

@[simp]
theorem mirrorMergeState_involutive (size : Nat)
    (state : MergeState (Occurrence alpha) nu) :
    mirrorMergeState size (mirrorMergeState size state) = state := by
  cases state
  simp [mirrorMergeState]

@[simp]
theorem mirrorSortSlice_entries_size (size : Nat)
    (slice : SortSlice (Occurrence alpha) nu) :
    (mirrorSortSlice size slice).entries.size = slice.entries.size := by
  simp [mirrorSortSlice]

@[simp]
theorem mirrorTempStorage_cells_size (size : Nat)
    (storage : TempStorage (Occurrence alpha) nu) :
    (mirrorTempStorage size storage).cells.size = storage.cells.size := by
  simp [mirrorTempStorage]

@[simp]
theorem mirrorMergeState_data_size (size : Nat)
    (state : MergeState (Occurrence alpha) nu) :
    (mirrorMergeState size state).data.entries.size = state.data.entries.size := by
  simp [mirrorMergeState]

@[simp]
theorem mirrorMergeState_data (size : Nat)
    (state : MergeState (Occurrence alpha) nu) :
    (mirrorMergeState size state).data = mirrorSortSlice size state.data := rfl

/-- Every comparator observation is unchanged by mirrored-origin relabeling. -/
@[simp]
theorem occurrenceComparator_mirror (lt : BoolComparator alpha) (size : Nat)
    (left right : Occurrence alpha) :
    occurrenceComparator lt (mirrorOccurrence size left)
        (mirrorOccurrence size right) = occurrenceComparator lt left right := by
  rfl

@[simp]
theorem iflt_occurrenceComparator_mirror (lt : BoolComparator alpha)
    (size : Nat) (left right : SortSliceEntry (Occurrence alpha) nu) :
    iflt (occurrenceComparator lt) (mirrorSortSliceEntry size left).key
        (mirrorSortSliceEntry size right).key =
      iflt (occurrenceComparator lt) left.key right.key := by
  rfl

@[simp]
theorem mirrorSortSlice_read (size : Nat)
    (slice : SortSlice (Occurrence alpha) nu) (index : Int) :
    (mirrorSortSlice size slice).read? index =
      (slice.read? index).map (mirrorSortSliceEntry size) := by
  by_cases hindex : 0 ≤ index <;>
    simp [mirrorSortSlice, SortSlice.read?, hindex]

@[simp]
theorem mirrorSortSlice_write (size : Nat)
    (slice : SortSlice (Occurrence alpha) nu) (index : Int)
    (entry : SortSliceEntry (Occurrence alpha) nu) :
    (mirrorSortSlice size slice).write? index (mirrorSortSliceEntry size entry) =
      (slice.write? index entry).map (mirrorSortSlice size) := by
  by_cases hindex : 0 ≤ index
  · by_cases hin : index.toNat < slice.entries.size
    · simp [mirrorSortSlice, mirrorSortSliceEntry, SortSlice.write?, hindex, hin]
    · simp [mirrorSortSlice, SortSlice.write?, hindex, hin]
  · simp [SortSlice.write?, hindex]

@[simp]
theorem mirrorMergeState_key_compare (size : Nat)
    (state : MergeState (Occurrence alpha) nu) :
    (mirrorMergeState size state).key_compare = state.key_compare := rfl

@[simp]
theorem mirrorMergeState_pending (size : Nat)
    (state : MergeState (Occurrence alpha) nu) :
    (mirrorMergeState size state).pending = state.pending := rfl

@[simp]
theorem mirrorMergeState_listlen (size : Nat)
    (state : MergeState (Occurrence alpha) nu) :
    (mirrorMergeState size state).listlen = state.listlen := rfl

@[simp]
theorem mirrorMergeState_basekeys (size : Nat)
    (state : MergeState (Occurrence alpha) nu) :
    (mirrorMergeState size state).basekeys = state.basekeys := rfl

@[simp]
theorem mirrorMergeState_alloced (size : Nat)
    (state : MergeState (Occurrence alpha) nu) :
    (mirrorMergeState size state).alloced = state.alloced := rfl

@[simp]
theorem mirrorMergeState_minrunState (size : Nat)
    (state : MergeState (Occurrence alpha) nu) :
    (mirrorMergeState size state).minrunState = state.minrunState := rfl

def mirrorCursorResult (size : Nat)
    (result : SortSlice.CursorResult (Occurrence alpha) nu) :
    SortSlice.CursorResult (Occurrence alpha) nu :=
  { result with slice := mirrorSortSlice size result.slice }

def mirrorReverseSliceResult (size : Nat)
    (result : ReverseSliceResult (Occurrence alpha) nu) :
    ReverseSliceResult (Occurrence alpha) nu :=
  { result with slice := mirrorSortSlice size result.slice }

@[simp]
theorem mirrorSortSlice_copyFrom (size : Nat)
    (destination source : SortSlice (Occurrence alpha) nu) (dst src : Int) :
    (mirrorSortSlice size destination).copyFrom?
        (mirrorSortSlice size source) dst src =
      (destination.copyFrom? source dst src).map (mirrorSortSlice size) := by
  unfold SortSlice.copyFrom?
  rw [mirrorSortSlice_read]
  cases hread : source.read? src with
  | none => simp
  | some entry =>
      simp only [Option.map_some]
      exact mirrorSortSlice_write size destination dst entry

@[simp]
theorem mirrorSortSlice_copy (size : Nat)
    (slice : SortSlice (Occurrence alpha) nu) (dst src : Int) :
    (mirrorSortSlice size slice).copy? dst src =
      (slice.copy? dst src).map (mirrorSortSlice size) := by
  simp [SortSlice.copy?, mirrorSortSlice_copyFrom]

@[simp]
theorem mirrorSortSlice_copyFromIncr (size : Nat)
    (destination source : SortSlice (Occurrence alpha) nu) (dst src : Int) :
    (mirrorSortSlice size destination).copyFromIncr?
        (mirrorSortSlice size source) dst src =
      (destination.copyFromIncr? source dst src).map (mirrorCursorResult size) := by
  unfold SortSlice.copyFromIncr?
  rw [mirrorSortSlice_copyFrom]
  cases hcopy : destination.copyFrom? source dst src with
  | none => simp
  | some updated => simp [mirrorCursorResult]

@[simp]
theorem mirrorSortSlice_copyFromDecr (size : Nat)
    (destination source : SortSlice (Occurrence alpha) nu) (dst src : Int) :
    (mirrorSortSlice size destination).copyFromDecr?
        (mirrorSortSlice size source) dst src =
      (destination.copyFromDecr? source dst src).map (mirrorCursorResult size) := by
  unfold SortSlice.copyFromDecr?
  rw [mirrorSortSlice_copyFrom]
  cases hcopy : destination.copyFrom? source dst src with
  | none => simp
  | some updated => simp [mirrorCursorResult]

@[simp]
theorem mirrorSortSlice_copyIncr (size : Nat)
    (slice : SortSlice (Occurrence alpha) nu) (dst src : Int) :
    (mirrorSortSlice size slice).copyIncr? dst src =
      (slice.copyIncr? dst src).map (mirrorCursorResult size) := by
  simp [SortSlice.copyIncr?, mirrorSortSlice_copyFromIncr]

@[simp]
theorem mirrorSortSlice_copyDecr (size : Nat)
    (slice : SortSlice (Occurrence alpha) nu) (dst src : Int) :
    (mirrorSortSlice size slice).copyDecr? dst src =
      (slice.copyDecr? dst src).map (mirrorCursorResult size) := by
  simp [SortSlice.copyDecr?, mirrorSortSlice_copyFromDecr]

theorem mirrorSortSlice_memcpyCore (size count : Nat)
    (destination source : SortSlice (Occurrence alpha) nu) (dst src : Int) :
    SortSlice.memcpyCore? count (mirrorSortSlice size destination)
        (mirrorSortSlice size source) dst src =
      (SortSlice.memcpyCore? count destination source dst src).map
        (mirrorSortSlice size) := by
  induction count generalizing destination dst src with
  | zero => rfl
  | succ count ih =>
      simp only [SortSlice.memcpyCore?]
      rw [mirrorSortSlice_copyFrom]
      cases hcopy : destination.copyFrom? source dst src with
      | none => simp
      | some updated => simp [ih]

theorem mirrorSortSlice_memmoveForward (size count : Nat)
    (slice : SortSlice (Occurrence alpha) nu) (dst src : Int) :
    SortSlice.memmoveForward? count (mirrorSortSlice size slice) dst src =
      (SortSlice.memmoveForward? count slice dst src).map
        (mirrorSortSlice size) := by
  induction count generalizing slice dst src with
  | zero => rfl
  | succ count ih =>
      simp only [SortSlice.memmoveForward?]
      rw [mirrorSortSlice_copy]
      cases hcopy : slice.copy? dst src with
      | none => simp
      | some updated => simp [ih]

theorem mirrorSortSlice_memmoveBackward (size count : Nat)
    (slice : SortSlice (Occurrence alpha) nu) (dst src : Int) :
    SortSlice.memmoveBackward? count (mirrorSortSlice size slice) dst src =
      (SortSlice.memmoveBackward? count slice dst src).map
        (mirrorSortSlice size) := by
  induction count generalizing slice dst src with
  | zero => rfl
  | succ count ih =>
      simp only [SortSlice.memmoveBackward?]
      rw [mirrorSortSlice_copy]
      cases hcopy : slice.copy? (dst + Int.ofNat count) (src + Int.ofNat count) with
      | none => simp
      | some updated => simp [ih]

@[simp]
theorem mirrorSortSlice_memmove (size : Nat)
    (slice : SortSlice (Occurrence alpha) nu) (dst src : Int) (count : Nat) :
    (mirrorSortSlice size slice).memmove? dst src count =
      (slice.memmove? dst src count).map (mirrorSortSlice size) := by
  simp only [SortSlice.memmove?]
  cases SortSlice.memmoveDirection dst src <;>
    simp [mirrorSortSlice_memmoveForward,
      mirrorSortSlice_memmoveBackward]

theorem mirrorReverseSliceLoop (size fuel : Nat)
    (slice : SortSlice (Occurrence alpha) nu) (lo hi : Int) :
    reverseSliceLoop? fuel (mirrorSortSlice size slice) lo hi =
      (reverseSliceLoop? fuel slice lo hi).map
        (mirrorReverseSliceResult size) := by
  induction fuel generalizing slice lo hi with
  | zero => rfl
  | succ fuel ih =>
      simp only [reverseSliceLoop?]
      by_cases hactive : lo < hi
      · rw [if_pos hactive, if_pos hactive]
        rw [mirrorSortSlice_read]
        cases hleft : slice.read? lo with
        | none => simp
        | some left =>
            simp only [Option.map_some]
            rw [mirrorSortSlice_read]
            cases hright : slice.read? hi with
            | none => simp
            | some right =>
                cases hwriteLeft : slice.write? lo right with
                | none => simp [hwriteLeft, mirrorSortSlice_write]
                | some afterLeft =>
                    cases hwriteRight : afterLeft.write? hi left with
                    | none =>
                        simp [hwriteLeft, hwriteRight, mirrorSortSlice_write]
                    | some afterRight =>
                        simp [hwriteLeft, hwriteRight, mirrorSortSlice_write, ih]
      · simp [hactive, mirrorReverseSliceResult]

@[simp]
theorem mirrorReverseSlice (size : Nat)
    (slice : SortSlice (Occurrence alpha) nu) (lo hi : Int) :
    reverseSlice? (mirrorSortSlice size slice) lo hi =
      (reverseSlice? slice lo hi).map (mirrorReverseSliceResult size) := by
  unfold reverseSlice?
  by_cases horder : lo ≤ hi
  · rw [if_pos horder, if_pos horder]
    by_cases hactive : lo < hi
    · rw [if_pos hactive, if_pos hactive]
      exact mirrorReverseSliceLoop size (hi - lo).toNat slice lo (hi - 1)
    · simp [hactive, mirrorReverseSliceResult]
  · simp [horder]

@[simp]
theorem mirrorSortsliceReverse (size : Nat)
    (slice : SortSlice (Occurrence alpha) nu) (base : Int) (count : Nat) :
    sortsliceReverse? (mirrorSortSlice size slice) base count =
      (sortsliceReverse? slice base count).map (mirrorReverseSliceResult size) := by
  simp [sortsliceReverse?, mirrorReverseSlice]

/-! ## Natural-run detection -/

def mirrorCountRunResult (size : Nat)
    (result : CountRunResult (Occurrence alpha) nu) :
    CountRunResult (Occurrence alpha) nu :=
  { result with slice := mirrorSortSlice size result.slice }

@[simp] theorem mirrorCountRunResult_slice (size : Nat)
    (result : CountRunResult (Occurrence alpha) nu) :
    (mirrorCountRunResult size result).slice = mirrorSortSlice size result.slice := rfl

@[simp] theorem mirrorCountRunResult_length (size : Nat)
    (result : CountRunResult (Occurrence alpha) nu) :
    (mirrorCountRunResult size result).length = result.length := rfl

@[simp] theorem mirrorCountRunResult_fuel (size : Nat)
    (result : CountRunResult (Occurrence alpha) nu) :
    (mirrorCountRunResult size result).fuelExhausted = result.fuelExhausted := rfl

def mirrorReverseEqualResult (size : Nat)
    (result : ReverseEqualResult (Occurrence alpha) nu) :
    ReverseEqualResult (Occurrence alpha) nu :=
  { result with slice := mirrorSortSlice size result.slice }

@[simp] theorem mirrorReverseEqualResult_slice (size : Nat)
    (result : ReverseEqualResult (Occurrence alpha) nu) :
    (mirrorReverseEqualResult size result).slice = mirrorSortSlice size result.slice := rfl

@[simp] theorem mirrorReverseEqualResult_fuel (size : Nat)
    (result : ReverseEqualResult (Occurrence alpha) nu) :
    (mirrorReverseEqualResult size result).fuelExhausted = result.fuelExhausted := rfl

def mirrorDescendingScanResult (size : Nat)
    (result : DescendingScanResult (Occurrence alpha) nu) :
    DescendingScanResult (Occurrence alpha) nu :=
  { result with slice := mirrorSortSlice size result.slice }

@[simp] theorem mirrorDescendingScanResult_slice (size : Nat)
    (result : DescendingScanResult (Occurrence alpha) nu) :
    (mirrorDescendingScanResult size result).slice =
      mirrorSortSlice size result.slice := rfl

@[simp] theorem mirrorDescendingScanResult_length (size : Nat)
    (result : DescendingScanResult (Occurrence alpha) nu) :
    (mirrorDescendingScanResult size result).length = result.length := rfl

@[simp] theorem mirrorDescendingScanResult_equalTail (size : Nat)
    (result : DescendingScanResult (Occurrence alpha) nu) :
    (mirrorDescendingScanResult size result).equalTail = result.equalTail := rfl

@[simp] theorem mirrorDescendingScanResult_fuel (size : Nat)
    (result : DescendingScanResult (Occurrence alpha) nu) :
    (mirrorDescendingScanResult size result).fuelExhausted =
      result.fuelExhausted := rfl

theorem mirrorAscendingScan (lt : BoolComparator alpha) (size fuel : Nat)
    (slice : SortSlice (Occurrence alpha) nu) (base : Int)
    (nremaining n : Nat) :
    ascendingScan? fuel (occurrenceComparator lt) (mirrorSortSlice size slice)
        base nremaining n =
      ascendingScan? fuel (occurrenceComparator lt) slice base nremaining n := by
  induction fuel generalizing n with
  | zero => rfl
  | succ fuel ih =>
      simp only [ascendingScan?]
      by_cases hscan : n < nremaining
      · rw [if_pos hscan, if_pos hscan]
        rw [mirrorSortSlice_read]
        cases hprevious : slice.read? (base + Int.ofNat (n - 1)) with
        | none => rfl
        | some previous =>
            simp only [Option.map_some, countRunBindOptionAcross]
            rw [mirrorSortSlice_read]
            cases hnext : slice.read? (base + Int.ofNat n) with
            | none => rfl
            | some next =>
                simp only [Option.map_some]
                rw [iflt_occurrenceComparator_mirror]
                split <;> simp [ih]
      · simp [hscan]

@[simp]
theorem mirrorReverseLastEqual (size : Nat)
    (slice : SortSlice (Occurrence alpha) nu) (base : Int) (n neq : Nat) :
    reverseLastEqual? (mirrorSortSlice size slice) base n neq =
      (reverseLastEqual? slice base n neq).map (mirrorReverseEqualResult size) := by
  unfold reverseLastEqual?
  by_cases heq : neq = 0
  · simp [heq, mirrorReverseEqualResult]
  · rw [if_neg heq, if_neg heq]
    dsimp only
    rw [mirrorSortsliceReverse]
    cases hreversed : sortsliceReverse? slice
        (base + Int.ofNat n - Int.ofNat (neq + 1)) (neq + 1) with
    | none => simp
    | some reversed =>
        simp [mirrorReverseEqualResult, mirrorReverseSliceResult]

theorem mirrorDescendingScan (lt : BoolComparator alpha) (size fuel : Nat)
    (slice : SortSlice (Occurrence alpha) nu) (base : Int)
    (nremaining n neq : Nat) :
    descendingScan? fuel (occurrenceComparator lt) (mirrorSortSlice size slice)
        base nremaining n neq =
      (descendingScan? fuel (occurrenceComparator lt) slice base nremaining n neq).map
        (mirrorDescendingScanResult size) := by
  induction fuel generalizing slice n neq with
  | zero => rfl
  | succ fuel ih =>
      simp only [descendingScan?]
      by_cases hscan : n < nremaining
      · rw [if_pos hscan, if_pos hscan]
        rw [mirrorSortSlice_read]
        cases hprevious : slice.read? (base + Int.ofNat (n - 1)) with
        | none => simp
        | some previous =>
            simp only [Option.map_some]
            rw [mirrorSortSlice_read]
            cases hnext : slice.read? (base + Int.ofNat n) with
            | none => simp
            | some next =>
                by_cases hless :
                    iflt (occurrenceComparator lt) next.key previous.key = true
                · simp only [iflt_eq] at hless
                  simp only [iflt_eq]
                  rw [mirrorReverseLastEqual]
                  cases hreversed : reverseLastEqual? slice base n neq with
                  | none => simp [hless]
                  | some reversed =>
                      cases hfuel : reversed.fuelExhausted <;>
                        simp [hless, hfuel, mirrorReverseEqualResult,
                          mirrorDescendingScanResult, ih]
                · by_cases hgreater :
                    iflt (occurrenceComparator lt) previous.key next.key = true
                  · simp only [iflt_eq] at hless hgreater
                    simp [iflt_eq, hless, hgreater, mirrorDescendingScanResult]
                  · simp only [iflt_eq] at hless hgreater
                    simp [iflt_eq, hless, hgreater, ih]
      · simp [hscan, mirrorDescendingScanResult]

theorem mirrorFinishDescending (lt : BoolComparator alpha) (size : Nat)
    (state : MergeState (Occurrence alpha) nu)
    (slice : SortSlice (Occurrence alpha) nu) (base : Int)
    (nremaining n : Nat)
    (hcompare : state.key_compare = occurrenceComparator lt) :
    finishDescending? (mirrorMergeState size state) (mirrorSortSlice size slice)
        base nremaining n =
      (finishDescending? state slice base nremaining n).map
        (mirrorCountRunResult size) := by
  unfold finishDescending?
  simp only [mirrorMergeState_key_compare, hcompare]
  rw [mirrorDescendingScan]
  cases hdescending : descendingScan? nremaining (occurrenceComparator lt) slice
      base nremaining n 0 with
  | none => simp
  | some descending =>
      by_cases hfuel : descending.fuelExhausted = true
      · simp [hfuel, mirrorDescendingScanResult, mirrorCountRunResult]
      · cases hequal : reverseLastEqual? descending.slice base descending.length
            descending.equalTail with
        | none =>
            simp [hfuel, hequal, mirrorDescendingScanResult]
        | some equalReversed =>
            by_cases hequalFuel : equalReversed.fuelExhausted = true
            · simp [hfuel, hequal, hequalFuel, mirrorDescendingScanResult,
                mirrorReverseEqualResult, mirrorCountRunResult]
            · cases hwhole : sortsliceReverse? equalReversed.slice base
                  descending.length with
              | none =>
                  simp [hfuel, hequal, hequalFuel, hwhole,
                    mirrorDescendingScanResult, mirrorReverseEqualResult]
              | some wholeReversed =>
                  by_cases hwholeFuel : wholeReversed.fuelExhausted = true
                  · simp [hfuel, hequal, hequalFuel, hwhole, hwholeFuel,
                      mirrorDescendingScanResult, mirrorReverseEqualResult,
                      mirrorReverseSliceResult, mirrorCountRunResult]
                  · simp only [hfuel, Bool.false_eq_true, if_false,
                      Option.map_some, Option.bind_eq_bind, Option.bind_some,
                      mirrorDescendingScanResult_fuel,
                      mirrorDescendingScanResult_slice,
                      mirrorDescendingScanResult_length,
                      mirrorDescendingScanResult_equalTail]
                    rw [mirrorReverseLastEqual]
                    simp only [hequal, Option.map_some, Option.bind_some,
                      mirrorReverseEqualResult_fuel,
                      mirrorReverseEqualResult_slice, hequalFuel,
                      Bool.false_eq_true, if_false]
                    rw [mirrorSortsliceReverse]
                    simp only [hwhole, Option.map_some, Option.bind_some,
                      mirrorReverseSliceResult, hwholeFuel,
                      Bool.false_eq_true, if_false]
                    rw [mirrorAscendingScan]
                    cases hascending : ascendingScan? nremaining
                        (occurrenceComparator lt) wholeReversed.slice base
                        nremaining descending.length <;> rfl

theorem mirrorCountRun (lt : BoolComparator alpha) (size : Nat)
    (state : MergeState (Occurrence alpha) nu)
    (slice : SortSlice (Occurrence alpha) nu) (base : Int) (nremaining : Nat)
    (hcompare : state.key_compare = occurrenceComparator lt) :
    countRun? (mirrorMergeState size state) (mirrorSortSlice size slice)
        base nremaining =
      (countRun? state slice base nremaining).map (mirrorCountRunResult size) := by
  unfold countRun?
  simp only [mirrorMergeState_key_compare, hcompare]
  by_cases hvalid : 0 < nremaining ∧ nremaining ≤ PY_SSIZE_T_MAX
  · rw [if_pos hvalid, if_pos hvalid, mirrorAscendingScan]
    cases hascending : ascendingScan? nremaining (occurrenceComparator lt) slice
        base nremaining 1 with
    | none => simp [countRunBindOptionAcross]
    | some ascending =>
        cases hfuel : ascending.fuelExhausted with
        | true => simp [countRunBindOptionAcross, hfuel, mirrorCountRunResult]
        | false =>
            by_cases hcomplete : ascending.length = nremaining
            · simp [countRunBindOptionAcross, hfuel, hcomplete,
                mirrorCountRunResult]
            · by_cases hlong : 1 < ascending.length
              · simp only [countRunBindOptionAcross, hfuel,
                    Bool.false_eq_true, if_false, hcomplete, hlong, if_true]
                rw [mirrorSortSlice_read]
                cases hfirst : slice.read? base with
                | none => simp
                | some first =>
                    simp only [Option.map_some]
                    rw [mirrorSortSlice_read]
                    cases hlast : slice.read? (base + Int.ofNat (ascending.length - 1)) with
                    | none => simp
                    | some last =>
                        simp only [Option.map_some]
                        by_cases hordered :
                            occurrenceComparator lt first.key last.key = true
                        · simp [hordered, iflt, mirrorCountRunResult]
                        · cases hreversed : sortsliceReverse? slice base
                              ascending.length with
                          | none => simp [hordered, iflt, hreversed]
                          | some reversed =>
                              cases hreverseFuel : reversed.fuelExhausted with
                              | true => simp [hordered, iflt, hreversed,
                                  hreverseFuel, mirrorReverseSliceResult,
                                  mirrorCountRunResult]
                              | false =>
                                  simp [hordered, iflt, hreversed, hreverseFuel,
                                    mirrorReverseSliceResult,
                                    mirrorFinishDescending lt size state
                                      reversed.slice base nremaining
                                      (ascending.length + 1) hcompare]
              · simp only [countRunBindOptionAcross, hfuel,
                    Bool.false_eq_true, if_false, hcomplete, hlong]
                exact mirrorFinishDescending lt size state slice base nremaining
                  (ascending.length + 1) hcompare
  · simp [hvalid]

/-! ## Stable binary insertion -/

def mirrorBinarysortResult (size : Nat)
    (result : BinarysortResult (Occurrence alpha) nu) :
    BinarysortResult (Occurrence alpha) nu :=
  { result with slice := mirrorSortSlice size result.slice }

@[simp] theorem mirrorBinarysortResult_slice (size : Nat)
    (result : BinarysortResult (Occurrence alpha) nu) :
    (mirrorBinarysortResult size result).slice = mirrorSortSlice size result.slice := rfl

@[simp] theorem mirrorBinarysortResult_fuel (size : Nat)
    (result : BinarysortResult (Occurrence alpha) nu) :
    (mirrorBinarysortResult size result).fuelExhausted = result.fuelExhausted := rfl

theorem mirrorBinarysortSearch (lt : BoolComparator alpha) (size fuel : Nat)
    (slice : SortSlice (Occurrence alpha) nu) (base : Int)
    (pivot : SortSliceEntry (Occurrence alpha) nu) (left right : Nat) :
    binarysortSearch? fuel (occurrenceComparator lt) (mirrorSortSlice size slice)
        base (mirrorSortSliceEntry size pivot) left right =
      binarysortSearch? fuel (occurrenceComparator lt) slice base pivot left right := by
  induction fuel generalizing left right with
  | zero => rfl
  | succ fuel ih =>
      simp only [binarysortSearch?]
      by_cases hsearch : left < right
      · rw [if_pos hsearch, if_pos hsearch, mirrorSortSlice_read]
        cases hread : slice.read? (base + Int.ofNat ((left + right) / 2)) with
        | none => rfl
        | some entry =>
            simp only [Option.map_some, binarysortBindOptionAcross]
            rw [iflt_occurrenceComparator_mirror]
            split <;> simp [ih]
      · simp [hsearch]

theorem mirrorBinarysortLoop (lt : BoolComparator alpha) (size fuel : Nat)
    (state : MergeState (Occurrence alpha) nu)
    (slice : SortSlice (Occurrence alpha) nu) (base : Int) (n ok : Nat)
    (hcompare : state.key_compare = occurrenceComparator lt) :
    binarysortLoop? fuel (mirrorMergeState size state) (mirrorSortSlice size slice)
        base n ok =
      (binarysortLoop? fuel state slice base n ok).map
        (mirrorBinarysortResult size) := by
  induction fuel generalizing slice ok with
  | zero => rfl
  | succ fuel ih =>
      simp only [binarysortLoop?]
      by_cases hloop : ok < n
      · rw [if_pos hloop, if_pos hloop, mirrorSortSlice_read]
        cases hpivot : slice.read? (base + Int.ofNat ok) with
        | none => simp [binarysortBindOptionAcross]
        | some pivot =>
            simp only [Option.map_some, binarysortBindOptionAcross]
            simp only [mirrorMergeState_key_compare, hcompare]
            rw [mirrorBinarysortSearch]
            cases hsearch : binarysortSearch? (ok + 1) (occurrenceComparator lt)
                slice base pivot 0 ok with
            | none => simp
            | some search =>
                cases hfuel : search.fuelExhausted with
                | true => simp [hfuel, mirrorBinarysortResult]
                | false =>
                    simp only [hfuel,
                      Bool.false_eq_true, if_false]
                    rw [mirrorSortSlice_memmove]
                    cases hmove : slice.memmove?
                        (base + Int.ofNat (search.position + 1))
                        (base + Int.ofNat search.position) (ok - search.position) with
                    | none => simp
                    | some moved =>
                        simp only [Option.map_some, Int.ofNat_eq_natCast,
                          Option.bind_eq_bind, Option.bind_some,
                          mirrorSortSlice_write, Option.map_bind,
                          Function.comp_apply]
                        rw [Option.bind_map]
                        apply Option.bind_congr
                        intro inserted _
                        exact ih inserted (ok + 1)
      · rw [if_neg hloop, if_neg hloop]
        rfl

@[simp]
theorem mirrorBinarysort (lt : BoolComparator alpha) (size : Nat)
    (state : MergeState (Occurrence alpha) nu)
    (slice : SortSlice (Occurrence alpha) nu) (base : Int) (n ok : Nat)
    (hcompare : state.key_compare = occurrenceComparator lt) :
    binarysort? (mirrorMergeState size state) (mirrorSortSlice size slice)
        base n ok =
      (binarysort? state slice base n ok).map (mirrorBinarysortResult size) := by
  unfold binarysort?
  by_cases hvalid : 1 ≤ n ∧ ok ≤ n ∧ n ≤ MAX_MINRUN.toNat
  · rw [if_pos hvalid, if_pos hvalid]
    split <;> apply mirrorBinarysortLoop lt size n state slice base n <;>
      exact hcompare
  · simp [hvalid]

/-! ## Canonical–mirrored semantic relations

The ordinary `PendingRunsCorrect` stability clause orders equal-valued
occurrences by increasing origin.  Mirroring origins reverses that order, so
the ordinary predicate is intentionally *not* claimed for a mirrored state.
The predicates below instead say that applying the involution back to the
mirrored data recovers the signed forward certificate. -/

@[simp]
theorem mirrorSortSlice_entries (size : Nat)
    (slice : SortSlice (Occurrence alpha) nu) :
    (mirrorSortSlice size slice).entries =
      slice.entries.map (mirrorSortSliceEntry size) := rfl

@[simp]
theorem sortSliceRangeEntries_mirror (size start count : Nat)
    (slice : SortSlice (Occurrence alpha) nu) :
    sortSliceRangeEntries (mirrorSortSlice size slice) start count =
      (sortSliceRangeEntries slice start count).map
        (mirrorSortSliceEntry size) := by
  simp [sortSliceRangeEntries, mirrorSortSlice, Array.map_extract]

@[simp]
theorem sortSliceRangeKeys_mirror (size start count : Nat)
    (slice : SortSlice (Occurrence alpha) nu) :
    sortSliceRangeKeys (mirrorSortSlice size slice) start count =
      (sortSliceRangeKeys slice start count).map (mirrorOccurrence size) := by
  simp [sortSliceRangeKeys, Array.map_map, Function.comp_def]

@[simp]
theorem pendingRunOccurrenceKeys_mirror (size : Nat)
    (state : MergeState (Occurrence alpha) nu) (run : PendingRun) :
    pendingRunOccurrenceKeys (mirrorMergeState size state) run =
      (pendingRunOccurrenceKeys state run).map (mirrorOccurrence size) := by
  change sortSliceRangeKeys (mirrorSortSlice size state.data) run.base
      run.len.toNat =
    (sortSliceRangeKeys state.data run.base run.len.toNat).map
      (mirrorOccurrence size)
  exact sortSliceRangeKeys_mirror size run.base run.len.toNat state.data

@[simp]
theorem pendingOccurrenceKeys_mirror (size : Nat)
    (state : MergeState (Occurrence alpha) nu) :
    pendingOccurrenceKeys (mirrorMergeState size state) =
      (pendingOccurrenceKeys state).map (mirrorOccurrence size) := by
  unfold pendingOccurrenceKeys
  rw [mirrorMergeState_pending, List.map_flatMap]
  apply List.flatMap_congr
  intro run _
  simp only [pendingRunOccurrenceKeys_mirror, Array.toList_map]

theorem sorted_mirror_iff (lt : BoolComparator alpha) (size : Nat)
    (entries : Array (Occurrence alpha)) :
    Sorted (occurrenceComparator lt) (entries.map (mirrorOccurrence size)) ↔
      Sorted (occurrenceComparator lt) entries := by
  simp only [Sorted, Array.toList_map]
  constructor
  · intro h
    have hmapped := List.pairwise_map.mp h
    simpa [Function.comp_def, occurrenceComparator] using hmapped
  · intro h
    apply List.pairwise_map.mpr
    simpa [Function.comp_def, occurrenceComparator] using h

/-- Reverse-oriented pending correctness: the structural and sortedness facts
hold on the mirrored state itself, while stability is checked after applying
the origin involution back to the canonical orientation. -/
structure CanonicalMirroredPendingRunsCorrect (lt : BoolComparator alpha)
    (input : Array alpha) (size : Nat)
    (state : MergeState (Occurrence alpha) nu) (scanned : Nat) : Prop where
  layout : PendingLayout state scanned
  runSorted : ∀ run ∈ state.pending.toList,
    Sorted (occurrenceComparator lt) (pendingRunOccurrenceKeys state run)
  stableAfterUnmirror : StableOccurrencePermutation lt
    (canonicalOccurrenceSegment input state.basekeys scanned)
    ((pendingOccurrenceKeys state).map (mirrorOccurrence size))

/-- Whole-entry snapshot relation for a mirrored execution.  Unmirroring each
current entry must recover a permutation of the absolutely tagged source. -/
def CanonicalMirroredEntrySnapshotPermutation (source : SortSlice alpha nu)
    (size : Nat) (current : SortSlice (Occurrence alpha) nu) : Prop :=
  (current.entries.map (mirrorSortSliceEntry size)).toList.Perm
    (tagSortSliceOccurrences source).entries.toList

/-- Unscanned-suffix relation for a mirrored execution.  Bounds are stated on
the real mirrored state; its suffix agrees with the canonical source after
applying the origin involution back to every entry. -/
structure CanonicalMirroredScanRemainderEntriesMatch
    (source : SortSlice alpha nu) (size : Nat)
    (state : MergeState (Occurrence alpha) nu) (scanned : Nat) : Prop where
  scanned_le : scanned ≤ state.listlen.toNat
  state_stop_le :
    state.basekeys + state.listlen.toNat ≤ state.data.entries.size
  source_stop_le :
    state.basekeys + state.listlen.toNat ≤ source.entries.size
  entries_eq :
    ((sortSliceRangeEntries state.data (state.basekeys + scanned)
      (state.listlen.toNat - scanned)).map
        (mirrorSortSliceEntry size)).toList =
      (sortSliceRangeEntries (tagSortSliceOccurrences source)
        (state.basekeys + scanned)
        (state.listlen.toNat - scanned)).toList

/-- A signed forward pending certificate transports to the mirrored state in
the reverse-oriented sense.  This theorem deliberately does not conclude the
ordinary `PendingRunsCorrect` predicate for the mirrored state. -/
theorem PendingRunsCorrect.toCanonicalMirrored
    (lt : BoolComparator alpha) (input : Array alpha) (size scanned : Nat)
    (state : MergeState (Occurrence alpha) nu)
    (h : PendingRunsCorrect lt input state scanned) :
    CanonicalMirroredPendingRunsCorrect lt input size
      (mirrorMergeState size state) scanned := by
  refine ⟨?_, ?_, ?_⟩
  · simpa [PendingLayout, mirrorMergeState] using h.layout
  · intro run hrun
    rw [pendingRunOccurrenceKeys_mirror]
    exact (sorted_mirror_iff lt size _).2
      (h.runSorted run (by simpa using hrun))
  · rw [pendingOccurrenceKeys_mirror, List.map_map]
    simpa [Function.comp_def] using h.stableOccurrencePermutation

/-- Applying the involution to a reverse-oriented pending certificate recovers
the exact ordinary forward predicate. -/
theorem CanonicalMirroredPendingRunsCorrect.unmirror
    (lt : BoolComparator alpha) (input : Array alpha) (size scanned : Nat)
    (state : MergeState (Occurrence alpha) nu)
    (h : CanonicalMirroredPendingRunsCorrect lt input size state scanned) :
    PendingRunsCorrect lt input (mirrorMergeState size state) scanned := by
  refine ⟨?_, ?_, ?_⟩
  · simpa [PendingLayout, mirrorMergeState] using h.layout
  · intro run hrun
    rw [pendingRunOccurrenceKeys_mirror]
    exact (sorted_mirror_iff lt size _).2
      (h.runSorted run (by simpa using hrun))
  · rw [pendingOccurrenceKeys_mirror]
    simpa using h.stableAfterUnmirror

/-- A signed whole-entry snapshot transports to the mirrored store. -/
theorem EntrySnapshotPermutation.toCanonicalMirrored
    (source : SortSlice alpha nu) (size : Nat)
    (current : SortSlice (Occurrence alpha) nu)
    (h : EntrySnapshotPermutation source current) :
    CanonicalMirroredEntrySnapshotPermutation source size
      (mirrorSortSlice size current) := by
  simpa [CanonicalMirroredEntrySnapshotPermutation, EntrySnapshotPermutation,
    mirrorSortSlice, Array.map_map, Function.comp_def] using h

/-- Unmirroring a reverse-oriented whole-entry snapshot recovers the ordinary
snapshot predicate. -/
theorem CanonicalMirroredEntrySnapshotPermutation.unmirror
    (source : SortSlice alpha nu) (size : Nat)
    (current : SortSlice (Occurrence alpha) nu)
    (h : CanonicalMirroredEntrySnapshotPermutation source size current) :
    EntrySnapshotPermutation source (mirrorSortSlice size current) := by
  simpa [CanonicalMirroredEntrySnapshotPermutation, EntrySnapshotPermutation,
    mirrorSortSlice, Array.map_map, Function.comp_def] using h

/-- A signed forward suffix snapshot transports to the mirrored state in the
reverse-oriented sense. -/
theorem ScanRemainderEntriesMatch.toCanonicalMirrored
    (source : SortSlice alpha nu) (size scanned : Nat)
    (state : MergeState (Occurrence alpha) nu)
    (h : ScanRemainderEntriesMatch source state scanned) :
    CanonicalMirroredScanRemainderEntriesMatch source size
      (mirrorMergeState size state) scanned := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · simpa using h.scanned_le
  · simpa using h.state_stop_le
  · simpa using h.source_stop_le
  · simp only [mirrorMergeState_data, mirrorMergeState_basekeys,
      mirrorMergeState_listlen]
    rw [sortSliceRangeEntries_mirror, Array.map_map]
    simpa [Function.comp_def] using h.entries_eq

/-- Unmirroring a reverse-oriented suffix snapshot recovers the ordinary
forward suffix predicate. -/
theorem CanonicalMirroredScanRemainderEntriesMatch.unmirror
    (source : SortSlice alpha nu) (size scanned : Nat)
    (state : MergeState (Occurrence alpha) nu)
    (h : CanonicalMirroredScanRemainderEntriesMatch source size state scanned) :
    ScanRemainderEntriesMatch source (mirrorMergeState size state) scanned := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · simpa using h.scanned_le
  · simpa using h.state_stop_le
  · simpa using h.source_stop_le
  · simp only [mirrorMergeState_data, mirrorMergeState_basekeys,
      mirrorMergeState_listlen]
    rw [sortSliceRangeEntries_mirror]
    simpa using h.entries_eq

/-! ## Kernel-checkable nonidentity regression -/

private def originRelabelRegressionOccurrence : Occurrence Nat :=
  { value := 17, origin := 0 }

/-- The relabeling is observably nonidentity inside the mirrored extent, and
applying it twice restores the original occurrence.  This is a kernel-reduced
regression proved by `decide`. -/
theorem mirrorOccurrence_nonidentity_regression :
    mirrorOccurrence 4 originRelabelRegressionOccurrence =
        ({ value := 17, origin := 3 } : Occurrence Nat) ∧
      mirrorOccurrence 4
          (mirrorOccurrence 4 originRelabelRegressionOccurrence) =
        originRelabelRegressionOccurrence := by
  decide

end CPythonListsort
