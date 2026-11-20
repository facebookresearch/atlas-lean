/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Code.Correctness.OriginRelabelEquivariance

/-!
# Origin-relabel equivariance for merge evaluators

The reverse-mode transport changes only the recorded origins carried by
occurrence keys.  This module proves that temporary-storage allocation,
galloping, and both concrete merge engines commute with that relabeling.
These are evaluator equations only: no ordering or stability law is assumed.
-/

namespace CPythonListsort

universe u v

variable {alpha : Type u} {nu : Type v}

@[simp] theorem mirrorTempStorage_cells (size : Nat)
    (storage : TempStorage (Occurrence alpha) nu) :
    (mirrorTempStorage size storage).cells =
      storage.cells.map (Option.map (mirrorSortSliceEntry size)) := rfl

@[simp] theorem mirrorTempStorage_backing (size : Nat)
    (storage : TempStorage (Occurrence alpha) nu) :
    (mirrorTempStorage size storage).backing = storage.backing := rfl

@[simp] theorem mirrorTempStorage_hasValues (size : Nat)
    (storage : TempStorage (Occurrence alpha) nu) :
    (mirrorTempStorage size storage).hasValues = storage.hasValues := rfl

@[simp] theorem mirrorMergeState_minGallop (size : Nat)
    (state : MergeState (Occurrence alpha) nu) :
    (mirrorMergeState size state).min_gallop = state.min_gallop := rfl

@[simp] theorem mirrorMergeState_tempStorage (size : Nat)
    (state : MergeState (Occurrence alpha) nu) :
    (mirrorMergeState size state).a = mirrorTempStorage size state.a := rfl

@[simp] theorem mirrorMergeState_mrCurrent (size : Nat)
    (state : MergeState (Occurrence alpha) nu) :
    (mirrorMergeState size state).mr_current = state.mr_current := rfl

@[simp] theorem mirrorMergeState_mrE (size : Nat)
    (state : MergeState (Occurrence alpha) nu) :
    (mirrorMergeState size state).mr_e = state.mr_e := rfl

@[simp] theorem mirrorMergeState_mrMask (size : Nat)
    (state : MergeState (Occurrence alpha) nu) :
    (mirrorMergeState size state).mr_mask = state.mr_mask := rfl

/-- Repackage the expanded state update created by unfolding a merge round. -/
theorem expandedMirrorMergeStateWithMinGallop (size : Nat)
    (state : MergeState (Occurrence alpha) nu) (minGallop : PySSize) :
    ({ min_gallop := minGallop
       listlen := (mirrorMergeState size state).listlen
       basekeys := (mirrorMergeState size state).basekeys
       data := mirrorSortSlice size state.data
       a := mirrorTempStorage size state.a
       alloced := (mirrorMergeState size state).alloced
       pending := (mirrorMergeState size state).pending
       key_compare := (mirrorMergeState size state).key_compare
       mr_current := (mirrorMergeState size state).mr_current
       mr_e := (mirrorMergeState size state).mr_e
       mr_mask := (mirrorMergeState size state).mr_mask } :
        MergeState (Occurrence alpha) nu) =
      mirrorMergeState size { state with min_gallop := minGallop } := by
  rfl

@[simp]
theorem iflt_mirrorOccurrence (lt : BoolComparator alpha) (size : Nat)
    (left right : Occurrence alpha) :
    iflt (occurrenceComparator lt) (mirrorOccurrence size left)
        (mirrorOccurrence size right) =
      iflt (occurrenceComparator lt) left right := by
  rfl

/-! ## Temporary storage and allocation -/

/-- Relabel the state component returned by `mergeGetmem`. -/
def mirrorMergeGetmemResult (size : Nat)
    (result : MergeGetmemResult (Occurrence alpha) nu) :
    MergeGetmemResult (Occurrence alpha) nu :=
  { result with state := mirrorMergeState size result.state }

@[simp] theorem mirrorMergeGetmemResult_state (size : Nat)
    (result : MergeGetmemResult (Occurrence alpha) nu) :
    (mirrorMergeGetmemResult size result).state =
      mirrorMergeState size result.state := rfl

@[simp] theorem mirrorMergeGetmemResult_outcome (size : Nat)
    (result : MergeGetmemResult (Occurrence alpha) nu) :
    (mirrorMergeGetmemResult size result).outcome = result.outcome := rfl

@[simp]
theorem mirrorMergeFreemem (size : Nat)
    (state : MergeState (Occurrence alpha) nu) :
    mergeFreemem (mirrorMergeState size state) =
      mirrorMergeState size (mergeFreemem state) := by
  by_cases hinline : state.a.backing = .inline <;>
    simp [mergeFreemem, hinline, mirrorMergeState, mirrorTempStorage]

@[simp]
theorem mirrorMergeGetmemAllocationLimit (size : Nat)
    (storage : TempStorage (Occurrence alpha) nu) :
    mergeGetmemAllocationLimit (mirrorTempStorage size storage) =
      mergeGetmemAllocationLimit storage := by
  rfl

@[simp]
theorem mirrorMergeGetmem (size : Nat)
    (state : MergeState (Occurrence alpha) nu) (need : PySSize) :
    mergeGetmem (mirrorMergeState size state) need =
      mirrorMergeGetmemResult size (mergeGetmem state need) := by
  have hlimit :
      mergeGetmemAllocationLimit (mirrorMergeState size state).a =
        mergeGetmemAllocationLimit state.a := by rfl
  rw [mergeGetmem, mergeGetmem]
  rw [mirrorMergeState_alloced, hlimit]
  by_cases hreuse : need.sle state.alloced = true
  · simp [hreuse, mirrorMergeGetmemResult]
  · have hreuseFalse : need.sle state.alloced = false := by
      cases h : need.sle state.alloced <;> simp_all
    by_cases hguard : mergeGetmemAllocationLimit state.a < need.toNat
    · simp only [hreuseFalse, Bool.false_eq_true, if_false, hguard, if_true,
        mirrorMergeGetmemResult]
      rw [mirrorMergeFreemem]
    · simp only [hreuseFalse, Bool.false_eq_true, if_false, hguard]
      rw [mirrorMergeFreemem]
      simp [mirrorMergeGetmemResult, mirrorMergeState, mirrorTempStorage]

theorem mergeFreemem_key_compare (state : MergeState κ ν) :
    (mergeFreemem state).key_compare = state.key_compare := by
  by_cases hinline : state.a.backing = .inline <;>
    simp [mergeFreemem, hinline]

theorem mergeGetmem_key_compare (state : MergeState κ ν) (need : PySSize) :
    (mergeGetmem state need).state.key_compare = state.key_compare := by
  unfold mergeGetmem
  split
  · rfl
  · dsimp only
    split <;> simp [mergeFreemem_key_compare]

/-! ## Hinted galloping -/

theorem mirrorGallopLeftRightExponential (lt : BoolComparator alpha)
    (size fuel : Nat) (slice : SortSlice (Occurrence alpha) nu) (base : Int)
    (key : Occurrence alpha) (hint maxOffset lastOffset offset : Nat) :
    gallopLeftRightExponential? fuel (occurrenceComparator lt)
        (mirrorSortSlice size slice) base (mirrorOccurrence size key)
        hint maxOffset lastOffset offset =
      gallopLeftRightExponential? fuel (occurrenceComparator lt)
        slice base key hint maxOffset lastOffset offset := by
  induction fuel generalizing lastOffset offset with
  | zero => rfl
  | succ fuel ih =>
      simp only [gallopLeftRightExponential?]
      by_cases hactive : offset < maxOffset
      · rw [if_pos hactive, if_pos hactive, mirrorSortSlice_read]
        cases hread : slice.read? (base + Int.ofNat hint + Int.ofNat offset) with
        | none => rfl
        | some entry =>
            simp only [Option.map_some, gallopBindOptionAcross]
            simp only [mirrorSortSliceEntry_key, iflt_mirrorOccurrence]
            split <;> simp [ih]
      · simp [hactive]

theorem mirrorGallopLeftLeftExponential (lt : BoolComparator alpha)
    (size fuel : Nat) (slice : SortSlice (Occurrence alpha) nu) (base : Int)
    (key : Occurrence alpha) (hint maxOffset lastOffset offset : Nat) :
    gallopLeftLeftExponential? fuel (occurrenceComparator lt)
        (mirrorSortSlice size slice) base (mirrorOccurrence size key)
        hint maxOffset lastOffset offset =
      gallopLeftLeftExponential? fuel (occurrenceComparator lt)
        slice base key hint maxOffset lastOffset offset := by
  induction fuel generalizing lastOffset offset with
  | zero => rfl
  | succ fuel ih =>
      simp only [gallopLeftLeftExponential?]
      by_cases hactive : offset < maxOffset
      · rw [if_pos hactive, if_pos hactive, mirrorSortSlice_read]
        cases hread : slice.read? (base + Int.ofNat hint - Int.ofNat offset) with
        | none => rfl
        | some entry =>
            simp only [Option.map_some, gallopBindOptionAcross]
            simp only [mirrorSortSliceEntry_key, iflt_mirrorOccurrence]
            split <;> simp [ih]
      · simp [hactive]

theorem mirrorGallopLeftBinary (lt : BoolComparator alpha)
    (size fuel : Nat) (slice : SortSlice (Occurrence alpha) nu) (base : Int)
    (key : Occurrence alpha) (lower upper : Nat) :
    gallopLeftBinary? fuel (occurrenceComparator lt)
        (mirrorSortSlice size slice) base (mirrorOccurrence size key) lower upper =
      gallopLeftBinary? fuel (occurrenceComparator lt)
        slice base key lower upper := by
  induction fuel generalizing lower upper with
  | zero => rfl
  | succ fuel ih =>
      simp only [gallopLeftBinary?]
      by_cases hactive : lower < upper
      · rw [if_pos hactive, if_pos hactive, mirrorSortSlice_read]
        cases hread : slice.read?
            (base + Int.ofNat (lower + (upper - lower) / 2)) with
        | none => rfl
        | some entry =>
            simp only [Option.map_some, gallopBindOptionAcross]
            simp only [mirrorSortSliceEntry_key, iflt_mirrorOccurrence]
            split <;> simp [ih]
      · simp [hactive]

@[simp]
theorem mirrorFinishGallopLeft (lt : BoolComparator alpha)
    (size fuel : Nat) (slice : SortSlice (Occurrence alpha) nu) (base : Int)
    (key : Occurrence alpha) (n : Nat) (lastOffset upperOffset : Int)
    (exponentialFuelExhausted : Bool) :
    finishGallopLeft? fuel (occurrenceComparator lt)
        (mirrorSortSlice size slice) base (mirrorOccurrence size key) n
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
      · simp [hexhausted, mirrorGallopLeftBinary]
    · rw [if_neg hnonnegative, if_neg hnonnegative]
  · rw [if_neg hbounds, if_neg hbounds]

theorem mirrorGallopRightLeftExponential (lt : BoolComparator alpha)
    (size fuel : Nat) (slice : SortSlice (Occurrence alpha) nu) (base : Int)
    (key : Occurrence alpha) (hint maxOffset lastOffset offset : Nat) :
    gallopRightLeftExponential? fuel (occurrenceComparator lt)
        (mirrorSortSlice size slice) base (mirrorOccurrence size key)
        hint maxOffset lastOffset offset =
      gallopRightLeftExponential? fuel (occurrenceComparator lt)
        slice base key hint maxOffset lastOffset offset := by
  induction fuel generalizing lastOffset offset with
  | zero => rfl
  | succ fuel ih =>
      simp only [gallopRightLeftExponential?]
      by_cases hactive : offset < maxOffset
      · rw [if_pos hactive, if_pos hactive, mirrorSortSlice_read]
        cases hread : slice.read? (base + Int.ofNat hint - Int.ofNat offset) with
        | none => rfl
        | some entry =>
            simp only [Option.map_some, gallopBindOptionAcross]
            simp only [mirrorSortSliceEntry_key, iflt_mirrorOccurrence]
            split <;> simp [ih]
      · simp [hactive]

theorem mirrorGallopRightRightExponential (lt : BoolComparator alpha)
    (size fuel : Nat) (slice : SortSlice (Occurrence alpha) nu) (base : Int)
    (key : Occurrence alpha) (hint maxOffset lastOffset offset : Nat) :
    gallopRightRightExponential? fuel (occurrenceComparator lt)
        (mirrorSortSlice size slice) base (mirrorOccurrence size key)
        hint maxOffset lastOffset offset =
      gallopRightRightExponential? fuel (occurrenceComparator lt)
        slice base key hint maxOffset lastOffset offset := by
  induction fuel generalizing lastOffset offset with
  | zero => rfl
  | succ fuel ih =>
      simp only [gallopRightRightExponential?]
      by_cases hactive : offset < maxOffset
      · rw [if_pos hactive, if_pos hactive, mirrorSortSlice_read]
        cases hread : slice.read? (base + Int.ofNat hint + Int.ofNat offset) with
        | none => rfl
        | some entry =>
            simp only [Option.map_some, gallopBindOptionAcross]
            simp only [mirrorSortSliceEntry_key, iflt_mirrorOccurrence]
            split <;> simp [ih]
      · simp [hactive]

theorem mirrorGallopRightBinary (lt : BoolComparator alpha)
    (size fuel : Nat) (slice : SortSlice (Occurrence alpha) nu) (base : Int)
    (key : Occurrence alpha) (lower upper : Nat) :
    gallopRightBinary? fuel (occurrenceComparator lt)
        (mirrorSortSlice size slice) base (mirrorOccurrence size key) lower upper =
      gallopRightBinary? fuel (occurrenceComparator lt)
        slice base key lower upper := by
  induction fuel generalizing lower upper with
  | zero => rfl
  | succ fuel ih =>
      simp only [gallopRightBinary?]
      by_cases hactive : lower < upper
      · rw [if_pos hactive, if_pos hactive, mirrorSortSlice_read]
        cases hread : slice.read?
            (base + Int.ofNat (lower + (upper - lower) / 2)) with
        | none => rfl
        | some entry =>
            simp only [Option.map_some, gallopBindOptionAcross]
            simp only [mirrorSortSliceEntry_key, iflt_mirrorOccurrence]
            split <;> simp [ih]
      · simp [hactive]

@[simp]
theorem mirrorFinishGallopRight (lt : BoolComparator alpha)
    (size fuel : Nat) (slice : SortSlice (Occurrence alpha) nu) (base : Int)
    (key : Occurrence alpha) (n : Nat) (lastOffset upperOffset : Int)
    (exponentialFuelExhausted : Bool) :
    finishGallopRight? fuel (occurrenceComparator lt)
        (mirrorSortSlice size slice) base (mirrorOccurrence size key) n
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
      · simp [hexhausted, mirrorGallopRightBinary]
    · rw [if_neg hnonnegative, if_neg hnonnegative]
  · rw [if_neg hbounds, if_neg hbounds]

@[simp]
theorem mirrorGallopLeft (lt : BoolComparator alpha) (size : Nat)
    (state : MergeState (Occurrence alpha) nu)
    (slice : SortSlice (Occurrence alpha) nu) (base : Int)
    (key : Occurrence alpha) (n hint : Nat)
    (hcompare : state.key_compare = occurrenceComparator lt) :
    gallopLeft? (mirrorMergeState size state) (mirrorSortSlice size slice)
        base (mirrorOccurrence size key) n hint =
      gallopLeft? state slice base key n hint := by
  unfold gallopLeft?
  simp only [mirrorMergeState_key_compare, hcompare]
  split <;> try rfl
  rw [mirrorSortSlice_read]
  cases hread : slice.read? (base + Int.ofNat hint) with
  | none => rfl
  | some entry =>
      simp only [Option.map_some, gallopBindOptionAcross]
      simp only [mirrorSortSliceEntry_key, iflt_mirrorOccurrence]
      split
      · rw [mirrorGallopLeftRightExponential]
        cases hexponential : gallopLeftRightExponential? (n + 1)
            (occurrenceComparator lt) slice base key hint (n - hint) 0 1 with
        | none => rfl
        | some exponential =>
            simp [mirrorFinishGallopLeft]
      · rw [mirrorGallopLeftLeftExponential]
        cases hexponential : gallopLeftLeftExponential? (n + 1)
            (occurrenceComparator lt) slice base key hint (hint + 1) 0 1 with
        | none => rfl
        | some exponential =>
            simp [mirrorFinishGallopLeft]

@[simp]
theorem mirrorGallopRight (lt : BoolComparator alpha) (size : Nat)
    (state : MergeState (Occurrence alpha) nu)
    (slice : SortSlice (Occurrence alpha) nu) (base : Int)
    (key : Occurrence alpha) (n hint : Nat)
    (hcompare : state.key_compare = occurrenceComparator lt) :
    gallopRight? (mirrorMergeState size state) (mirrorSortSlice size slice)
        base (mirrorOccurrence size key) n hint =
      gallopRight? state slice base key n hint := by
  unfold gallopRight?
  simp only [mirrorMergeState_key_compare, hcompare]
  split <;> try rfl
  rw [mirrorSortSlice_read]
  cases hread : slice.read? (base + Int.ofNat hint) with
  | none => rfl
  | some entry =>
      simp only [Option.map_some, gallopBindOptionAcross]
      simp only [mirrorSortSliceEntry_key, iflt_mirrorOccurrence]
      split
      · rw [mirrorGallopRightLeftExponential]
        cases hexponential : gallopRightLeftExponential? (n + 1)
            (occurrenceComparator lt) slice base key hint (hint + 1) 0 1 with
        | none => rfl
        | some exponential =>
            simp [mirrorFinishGallopRight]
      · rw [mirrorGallopRightRightExponential]
        cases hexponential : gallopRightRightExponential? (n + 1)
            (occurrenceComparator lt) slice base key hint (n - hint) 0 1 with
        | none => rfl
        | some exponential =>
            simp [mirrorFinishGallopRight]

/-! ## `merge_lo` primitives -/

@[simp]
theorem mirrorMergeDataMemmove (size : Nat) (site : MergeMemmoveCallsite)
    (data : SortSlice (Occurrence alpha) nu) (dst src : Int) (count : Nat) :
    mergeDataMemmove? site (mirrorSortSlice size data) dst src count =
      (mergeDataMemmove? site data dst src count).map (mirrorSortSlice size) := by
  simp [mergeDataMemmove?]

@[simp]
theorem mirrorMergeLoTempRead (size : Nat)
    (storage : TempStorage (Occurrence alpha) nu) (index : Nat) :
    mergeLoTempRead? (mirrorTempStorage size storage) index =
      (mergeLoTempRead? storage index).map (mirrorSortSliceEntry size) := by
  cases hcell : storage.cells[index]? with
  | none => simp [mergeLoTempRead?, mirrorTempStorage, hcell]
  | some cell =>
      cases cell <;> simp [mergeLoTempRead?, mirrorTempStorage, hcell]

@[simp]
theorem mirrorMergeLoTempWrite (size : Nat)
    (storage : TempStorage (Occurrence alpha) nu) (index : Nat)
    (entry : SortSliceEntry (Occurrence alpha) nu) :
    mergeLoTempWrite? (mirrorTempStorage size storage) index
        (mirrorSortSliceEntry size entry) =
      (mergeLoTempWrite? storage index entry).map (mirrorTempStorage size) := by
  unfold mergeLoTempWrite?
  simp only [mirrorTempStorage_cells_size]
  split
  · simp [mirrorTempStorage, Array.map_set]
  · rfl

theorem mirrorMergeLoMemcpyDataToTemp
    (size : Nat) (site : MergeLoMemcpyCallsite)
    (hDirection : site.backings =
      { destination := .temporary, source := .main })
    (count : Nat) (state : MergeState (Occurrence alpha) nu)
    (destination : Nat) (source : Int) :
    mergeLoMemcpyDataToTemp? site hDirection count
        (mirrorMergeState size state) destination source =
      (mergeLoMemcpyDataToTemp? site hDirection count state destination source).map
        (mirrorMergeState size) := by
  induction count generalizing state destination source with
  | zero => rfl
  | succ count ih =>
      simp only [mergeLoMemcpyDataToTemp?]
      simp only [mirrorMergeState_data, mirrorMergeState_tempStorage,
        mirrorMergeState_minGallop, mirrorMergeState_listlen,
        mirrorMergeState_basekeys, mirrorMergeState_alloced,
        mirrorMergeState_pending, mirrorMergeState_key_compare,
        mirrorMergeState_mrCurrent, mirrorMergeState_mrE,
        mirrorMergeState_mrMask]
      rw [mirrorSortSlice_read]
      cases hread : state.data.read? source with
      | none => rfl
      | some entry =>
          simp only [Option.map_some, bind, Option.bind]
          rw [mirrorMergeLoTempWrite]
          cases hwrite : mergeLoTempWrite? state.a destination entry with
          | none => rfl
          | some storage =>
              simp only [Option.map_some]
              simpa [mirrorMergeState] using
                ih (state := { state with a := storage })
                  (destination := destination + 1) (source := source + 1)

theorem mirrorMergeLoMemcpyTempToData
    (size : Nat) (site : MergeLoMemcpyCallsite)
    (hDirection : site.backings =
      { destination := .main, source := .temporary })
    (count : Nat) (state : MergeState (Occurrence alpha) nu)
    (destination : Int) (source : Nat) :
    mergeLoMemcpyTempToData? site hDirection count
        (mirrorMergeState size state) destination source =
      (mergeLoMemcpyTempToData? site hDirection count state destination source).map
        (mirrorMergeState size) := by
  induction count generalizing state destination source with
  | zero => rfl
  | succ count ih =>
      simp only [mergeLoMemcpyTempToData?]
      simp only [mirrorMergeState_data, mirrorMergeState_tempStorage,
        mirrorMergeState_minGallop, mirrorMergeState_listlen,
        mirrorMergeState_basekeys, mirrorMergeState_alloced,
        mirrorMergeState_pending, mirrorMergeState_key_compare,
        mirrorMergeState_mrCurrent, mirrorMergeState_mrE,
        mirrorMergeState_mrMask]
      rw [mirrorMergeLoTempRead]
      cases hread : mergeLoTempRead? state.a source with
      | none => rfl
      | some entry =>
          simp only [Option.map_some, bind, Option.bind]
          rw [mirrorSortSlice_write]
          cases hwrite : state.data.write? destination entry with
          | none => rfl
          | some data =>
              simp only [Option.map_some]
              simpa [mirrorMergeState] using
                ih (state := { state with data := data })
                  (destination := destination + 1) (source := source + 1)

@[simp]
theorem mirrorMergeLoInitialDataToTemp (size count : Nat)
    (state : MergeState (Occurrence alpha) nu) (destination : Nat)
    (source : Int) :
    mergeLoMemcpyDataToTemp? .initialDataToTemp rfl count
        (mirrorMergeState size state) destination source =
      (mergeLoMemcpyDataToTemp? .initialDataToTemp rfl count state
        destination source).map (mirrorMergeState size) := by
  exact mirrorMergeLoMemcpyDataToTemp size .initialDataToTemp rfl count state
    destination source

@[simp]
theorem mirrorMergeLoGallopTempToData (size count : Nat)
    (state : MergeState (Occurrence alpha) nu) (destination : Int)
    (source : Nat) :
    mergeLoMemcpyTempToData? .gallopTempToData rfl count
        (mirrorMergeState size state) destination source =
      (mergeLoMemcpyTempToData? .gallopTempToData rfl count state
        destination source).map (mirrorMergeState size) := by
  exact mirrorMergeLoMemcpyTempToData size .gallopTempToData rfl count state
    destination source

@[simp]
theorem mirrorMergeLoFinalTempToData (size count : Nat)
    (state : MergeState (Occurrence alpha) nu) (destination : Int)
    (source : Nat) :
    mergeLoMemcpyTempToData? .finalTempToData rfl count
        (mirrorMergeState size state) destination source =
      (mergeLoMemcpyTempToData? .finalTempToData rfl count state
        destination source).map (mirrorMergeState size) := by
  exact mirrorMergeLoMemcpyTempToData size .finalTempToData rfl count state
    destination source

theorem mergeLoMemcpyDataToTemp_key_compare_of_eq_some
    (site : MergeLoMemcpyCallsite)
    (hDirection : site.backings =
      { destination := .temporary, source := .main })
    (count : Nat) (state result : MergeState κ ν) (destination : Nat)
    (source : Int)
    (h : mergeLoMemcpyDataToTemp? site hDirection count state destination
      source = some result) :
    result.key_compare = state.key_compare := by
  induction count generalizing state destination source with
  | zero =>
      simp only [mergeLoMemcpyDataToTemp?] at h
      injection h with h
      subst result
      rfl
  | succ count ih =>
      simp only [mergeLoMemcpyDataToTemp?, bind, Option.bind] at h
      split at h <;> simp_all
      split at h <;> simp_all
      simpa using ih _ _ _ h

theorem mergeLoMemcpyTempToData_key_compare_of_eq_some
    (site : MergeLoMemcpyCallsite)
    (hDirection : site.backings =
      { destination := .main, source := .temporary })
    (count : Nat) (state result : MergeState κ ν) (destination : Int)
    (source : Nat)
    (h : mergeLoMemcpyTempToData? site hDirection count state destination
      source = some result) :
    result.key_compare = state.key_compare := by
  induction count generalizing state destination source with
  | zero =>
      simp only [mergeLoMemcpyTempToData?] at h
      injection h with h
      subst result
      rfl
  | succ count ih =>
      simp only [mergeLoMemcpyTempToData?, bind, Option.bind] at h
      split at h <;> simp_all
      split at h <;> simp_all
      simpa using ih _ _ _ h

theorem mirrorMergeLoGatherTempEntries (size count : Nat)
    (storage : TempStorage (Occurrence alpha) nu) (source : Nat)
    (entries : Array (SortSliceEntry (Occurrence alpha) nu)) :
    mergeLoGatherTempEntries? count (mirrorTempStorage size storage) source
        (entries.map (mirrorSortSliceEntry size)) =
      (mergeLoGatherTempEntries? count storage source entries).map
        (Array.map (mirrorSortSliceEntry size)) := by
  induction count generalizing source entries with
  | zero => rfl
  | succ count ih =>
      simp only [mergeLoGatherTempEntries?]
      rw [mirrorMergeLoTempRead]
      cases hread : mergeLoTempRead? storage source with
      | none => rfl
      | some entry =>
          simp only [Option.map_some]
          simpa [Array.map_push] using
            ih (source := source + 1) (entries := entries.push entry)

@[simp]
theorem mirrorMergeLoTempRun (size : Nat)
    (storage : TempStorage (Occurrence alpha) nu) (source count : Nat) :
    mergeLoTempRun? (mirrorTempStorage size storage) source count =
      (mergeLoTempRun? storage source count).map (mirrorSortSlice size) := by
  unfold mergeLoTempRun?
  have hgather :
      mergeLoGatherTempEntries? count (mirrorTempStorage size storage) source #[] =
        (mergeLoGatherTempEntries? count storage source #[]).map
          (Array.map (mirrorSortSliceEntry size)) := by
    simpa using mirrorMergeLoGatherTempEntries size count storage source #[]
  rw [hgather]
  cases hentries : mergeLoGatherTempEntries? count storage source #[] with
  | none => rfl
  | some entries => simp [mirrorSortSlice]

/-- Relabel the occurrence-bearing state of a forward merge machine. -/
def mirrorMergeLoMachine (size : Nat)
    (machine : MergeLoMachine (Occurrence alpha) nu) :
    MergeLoMachine (Occurrence alpha) nu :=
  { machine with state := mirrorMergeState size machine.state }

/-- Relabel the occurrence-bearing state of a forward merge result. -/
def mirrorMergeLoResult (size : Nat)
    (result : MergeLoResult (Occurrence alpha) nu) :
    MergeLoResult (Occurrence alpha) nu :=
  { result with state := mirrorMergeState size result.state }

@[simp] theorem mirrorMergeLoResult_state (size : Nat)
    (result : MergeLoResult (Occurrence alpha) nu) :
    (mirrorMergeLoResult size result).state =
      mirrorMergeState size result.state := rfl

@[simp] theorem mirrorMergeLoResult_returnCode (size : Nat)
    (result : MergeLoResult (Occurrence alpha) nu) :
    (mirrorMergeLoResult size result).returnCode = result.returnCode := rfl

@[simp] theorem mirrorMergeLoResult_fuelExhausted (size : Nat)
    (result : MergeLoResult (Occurrence alpha) nu) :
    (mirrorMergeLoResult size result).fuelExhausted = result.fuelExhausted := rfl

@[simp] theorem mirrorMergeLoMachine_state (size : Nat)
    (machine : MergeLoMachine (Occurrence alpha) nu) :
    (mirrorMergeLoMachine size machine).state =
      mirrorMergeState size machine.state := rfl

@[simp] theorem mirrorMergeLoMachine_dest (size : Nat)
    (machine : MergeLoMachine (Occurrence alpha) nu) :
    (mirrorMergeLoMachine size machine).dest = machine.dest := rfl

@[simp] theorem mirrorMergeLoMachine_aPos (size : Nat)
    (machine : MergeLoMachine (Occurrence alpha) nu) :
    (mirrorMergeLoMachine size machine).aPos = machine.aPos := rfl

@[simp] theorem mirrorMergeLoMachine_bPos (size : Nat)
    (machine : MergeLoMachine (Occurrence alpha) nu) :
    (mirrorMergeLoMachine size machine).bPos = machine.bPos := rfl

@[simp] theorem mirrorMergeLoMachine_na (size : Nat)
    (machine : MergeLoMachine (Occurrence alpha) nu) :
    (mirrorMergeLoMachine size machine).na = machine.na := rfl

@[simp] theorem mirrorMergeLoMachine_nb (size : Nat)
    (machine : MergeLoMachine (Occurrence alpha) nu) :
    (mirrorMergeLoMachine size machine).nb = machine.nb := rfl

@[simp] theorem mirrorMergeLoMachine_minGallop (size : Nat)
    (machine : MergeLoMachine (Occurrence alpha) nu) :
    (mirrorMergeLoMachine size machine).minGallop = machine.minGallop := rfl

@[simp]
theorem mirrorMergeLoFailure (size : Nat)
    (state : MergeState (Occurrence alpha) nu) :
    mergeLoFailure (mirrorMergeState size state) =
      mirrorMergeLoResult size (mergeLoFailure state) := rfl

@[simp]
theorem mirrorMergeLoOutOfFuel (size : Nat)
    (state : MergeState (Occurrence alpha) nu) :
    mergeLoOutOfFuel (mirrorMergeState size state) =
      mirrorMergeLoResult size (mergeLoOutOfFuel state) := rfl

@[simp]
theorem mirrorMergeLoSuccess (size : Nat)
    (state : MergeState (Occurrence alpha) nu) :
    mergeLoSuccess (mirrorMergeState size state) =
      mirrorMergeLoResult size (mergeLoSuccess state) := rfl

@[simp]
theorem mirrorMergeLoCopyAIncr (size : Nat)
    (machine : MergeLoMachine (Occurrence alpha) nu) :
    mergeLoCopyAIncr? (mirrorMergeLoMachine size machine) =
      (mergeLoCopyAIncr? machine).map (mirrorMergeLoMachine size) := by
  unfold mergeLoCopyAIncr?
  simp only [mirrorMergeLoMachine_state, mirrorMergeLoMachine_aPos,
    mirrorMergeLoMachine_dest, mirrorMergeLoMachine_bPos,
    mirrorMergeLoMachine_na, mirrorMergeLoMachine_nb,
    mirrorMergeLoMachine_minGallop, mirrorMergeState_tempStorage,
    mirrorMergeState_data]
  rw [mirrorMergeLoTempRead]
  cases hread : mergeLoTempRead? machine.state.a machine.aPos with
  | none => rfl
  | some entry =>
      simp only [Option.map_some, bind, Option.bind]
      rw [mirrorSortSlice_write]
      cases hwrite : machine.state.data.write? machine.dest entry with
      | none => rfl
      | some data => simp [mirrorMergeLoMachine, mirrorMergeState]

@[simp]
theorem mirrorMergeLoCopyBIncr (size : Nat)
    (machine : MergeLoMachine (Occurrence alpha) nu) :
    mergeLoCopyBIncr? (mirrorMergeLoMachine size machine) =
      (mergeLoCopyBIncr? machine).map (mirrorMergeLoMachine size) := by
  unfold mergeLoCopyBIncr?
  simp only [mirrorMergeLoMachine_state, mirrorMergeLoMachine_aPos,
    mirrorMergeLoMachine_dest, mirrorMergeLoMachine_bPos,
    mirrorMergeLoMachine_na, mirrorMergeLoMachine_nb,
    mirrorMergeLoMachine_minGallop, mirrorMergeState_tempStorage,
    mirrorMergeState_data]
  rw [mirrorSortSlice_read]
  cases hread : machine.state.data.read? machine.bPos with
  | none => rfl
  | some entry =>
      simp only [Option.map_some, bind, Option.bind]
      rw [mirrorSortSlice_write]
      cases hwrite : machine.state.data.write? machine.dest entry with
      | none => rfl
      | some data => simp [mirrorMergeLoMachine, mirrorMergeState]

theorem mergeLoCopyAIncr_key_compare_of_eq_some
    (machine result : MergeLoMachine κ ν)
    (h : mergeLoCopyAIncr? machine = some result) :
    result.state.key_compare = machine.state.key_compare := by
  simp only [mergeLoCopyAIncr?, bind, Option.bind] at h
  split at h <;> simp_all
  split at h <;> simp_all
  subst result
  rfl

theorem mergeLoCopyBIncr_key_compare_of_eq_some
    (machine result : MergeLoMachine κ ν)
    (h : mergeLoCopyBIncr? machine = some result) :
    result.state.key_compare = machine.state.key_compare := by
  simp only [mergeLoCopyBIncr?, bind, Option.bind] at h
  split at h <;> simp_all
  split at h <;> simp_all
  subst result
  rfl

@[simp]
theorem mirrorMergeLoSucceed (size : Nat)
    (machine : MergeLoMachine (Occurrence alpha) nu) :
    mergeLoSucceed? (mirrorMergeLoMachine size machine) =
      (mergeLoSucceed? machine).map (mirrorMergeLoResult size) := by
  unfold mergeLoSucceed?
  simp only [mirrorMergeLoMachine_state, mirrorMergeLoMachine_na,
    mirrorMergeLoMachine_dest, mirrorMergeLoMachine_aPos]
  rw [mirrorMergeLoFinalTempToData]
  cases hcopy : mergeLoMemcpyTempToData? .finalTempToData rfl machine.na
      machine.state machine.dest machine.aPos with
  | none => rfl
  | some state => simp

@[simp]
theorem mirrorMergeLoCopyB (size : Nat)
    (machine : MergeLoMachine (Occurrence alpha) nu) :
    mergeLoCopyB? (mirrorMergeLoMachine size machine) =
      (mergeLoCopyB? machine).map (mirrorMergeLoResult size) := by
  unfold mergeLoCopyB?
  by_cases hactive : machine.na = 1 ∧ 0 < machine.nb <;>
    simp only [mirrorMergeLoMachine_state, mirrorMergeLoMachine_na,
    mirrorMergeLoMachine_nb, mirrorMergeLoMachine_dest,
    mirrorMergeLoMachine_bPos, mirrorMergeLoMachine_aPos,
    mirrorMergeState_data, mirrorMergeState_tempStorage, hactive]
  · rw [mirrorMergeDataMemmove]
    cases hmove : mergeDataMemmove? .loCopyBTail machine.state.data
        machine.dest machine.bPos machine.nb with
    | none => simp
    | some data =>
        simp only [Option.map_some, bind, Option.bind]
        rw [mirrorMergeLoTempRead]
        cases hread : mergeLoTempRead? machine.state.a machine.aPos with
        | none => simp
        | some entry =>
            simp only [Option.map_some]
            rw [mirrorSortSlice_write]
            cases hwrite : data.write?
                (machine.dest + Int.ofNat machine.nb) entry with
            | none => simp
            | some finalData =>
                simp [mirrorMergeLoResult, mirrorMergeState, mergeLoSuccess]
  · rfl

@[simp]
theorem mirrorMergeLoGallopFuelFailure (size : Nat)
    (machine : MergeLoMachine (Occurrence alpha) nu) :
    mergeLoGallopFuelFailure (mirrorMergeLoMachine size machine) =
      (mergeLoGallopFuelFailure machine).map (mirrorMergeLoResult size) := by
  rfl

set_option maxHeartbeats 2000000 in
-- The gallop-round commutation proof normalizes deeply nested optional branches.
theorem mirrorMergeLoGallopRound (lt : BoolComparator alpha) (size : Nat)
    (machine : MergeLoMachine (Occurrence alpha) nu)
    (next next' : MergeLoMachine (Occurrence alpha) nu → Nat → Nat →
      Option (MergeLoResult (Occurrence alpha) nu))
    (hcompare : machine.state.key_compare = occurrenceComparator lt)
    (hnext : ∀ machine aCount bCount,
      machine.state.key_compare = occurrenceComparator lt →
      next' (mirrorMergeLoMachine size machine) aCount bCount =
        (next machine aCount bCount).map (mirrorMergeLoResult size)) :
    mergeLoGallopRound? (mirrorMergeLoMachine size machine) next' =
      (mergeLoGallopRound? machine next).map (mirrorMergeLoResult size) := by
  unfold mergeLoGallopRound?
  simp only [mirrorMergeLoMachine_na, mirrorMergeLoMachine_nb,
    mirrorMergeLoMachine_state, mirrorMergeLoMachine_dest,
    mirrorMergeLoMachine_aPos, mirrorMergeLoMachine_bPos,
    mirrorMergeLoMachine_minGallop]
  by_cases hactive : machine.na ≤ 1 ∨ machine.nb = 0 <;>
    simp only [hactive, if_pos, if_false, Option.map_none]
  rw [mirrorMergeState_data, mirrorSortSlice_read]
  cases hfirstB : machine.state.data.read? machine.bPos with
  | none => rfl
  | some firstB =>
      simp only [Option.map_some, bind, Option.bind]
      rw [mirrorMergeState_tempStorage, mirrorMergeLoTempRun]
      cases hactiveA : mergeLoTempRun? machine.state.a machine.aPos machine.na with
      | none => rfl
      | some activeA =>
          simp only [Option.map_some, mergeLoBindOptionAcross]
          let adjustedState : MergeState (Occurrence alpha) nu :=
            { machine.state with
              min_gallop :=
                if (1 : PySSize).slt machine.minGallop then
                  machine.minGallop - 1
                else machine.minGallop }
          let adjustedMachine : MergeLoMachine (Occurrence alpha) nu :=
            { machine with
              state := adjustedState
              minGallop :=
                if (1 : PySSize).slt machine.minGallop then
                  machine.minGallop - 1
                else machine.minGallop }
          have hcompare' : adjustedState.key_compare =
              occurrenceComparator lt := by
            simpa [adjustedState] using hcompare
          change
            mergeLoBindOptionAcross
                (gallopRight? (mirrorMergeState size adjustedState)
                  (mirrorSortSlice size activeA) 0
                  (mirrorOccurrence size firstB.key) machine.na 0) _ =
              Option.map (mirrorMergeLoResult size)
                (mergeLoBindOptionAcross
                  (gallopRight? adjustedState activeA 0 firstB.key
                    machine.na 0) _)
          rw [mirrorGallopRight lt size adjustedState activeA 0 firstB.key
            machine.na 0 hcompare']
          cases hgallopA : gallopRight?
              { machine.state with
                min_gallop :=
                  if (1 : PySSize).slt machine.minGallop then
                    machine.minGallop - 1
                  else machine.minGallop }
              activeA 0 firstB.key machine.na 0 with
          | none => rfl
          | some gallopA =>
              change
                (if gallopA.fuelExhausted then
                    mergeLoGallopFuelFailure
                      (mirrorMergeLoMachine size adjustedMachine)
                  else _) =
                  Option.map (mirrorMergeLoResult size)
                    (if gallopA.fuelExhausted then
                        mergeLoGallopFuelFailure adjustedMachine
                      else _)
              by_cases hfuel : gallopA.fuelExhausted = true
              · simp only [hfuel, if_true]
                exact mirrorMergeLoGallopFuelFailure size adjustedMachine
              · simp only [hfuel, Bool.false_eq_true, if_false]
                by_cases hindex : gallopA.index > machine.na
                · simp only [hindex, if_true, Option.map_none]
                · simp only [hindex, if_false]
                  change
                    Option.bind
                        (mergeLoMemcpyTempToData? .gallopTempToData rfl
                          gallopA.index (mirrorMergeState size adjustedState)
                          machine.dest machine.aPos) _ =
                      Option.map (mirrorMergeLoResult size)
                        (Option.bind
                          (mergeLoMemcpyTempToData? .gallopTempToData rfl
                            gallopA.index adjustedState machine.dest machine.aPos)
                          _)
                  rw [mirrorMergeLoGallopTempToData]
                  cases hcopyA : mergeLoMemcpyTempToData? .gallopTempToData rfl
                      gallopA.index
                      { machine.state with
                        min_gallop :=
                          if (1 : PySSize).slt machine.minGallop then
                            machine.minGallop - 1
                          else machine.minGallop }
                      machine.dest machine.aPos with
                  | none => rfl
                  | some state =>
                      simp only [Option.map_some, Option.bind_some]
                      let afterA : MergeLoMachine (Occurrence alpha) nu :=
                        { state := state
                          dest := machine.dest + Int.ofNat gallopA.index
                          aPos := machine.aPos + gallopA.index
                          bPos := machine.bPos
                          na := machine.na - gallopA.index
                          nb := machine.nb
                          minGallop :=
                            if (1 : PySSize).slt machine.minGallop then
                              machine.minGallop - 1
                            else machine.minGallop }
                      change
                        (if afterA.na = 0 then
                            mergeLoSucceed?
                              (mirrorMergeLoMachine size afterA)
                          else if afterA.na = 1 then
                            mergeLoCopyB? (mirrorMergeLoMachine size afterA)
                          else
                            Option.bind
                              (mergeLoCopyBIncr?
                                (mirrorMergeLoMachine size afterA)) _) =
                          Option.map (mirrorMergeLoResult size)
                            (if afterA.na = 0 then mergeLoSucceed? afterA
                              else if afterA.na = 1 then mergeLoCopyB? afterA
                              else Option.bind (mergeLoCopyBIncr? afterA) _)
                      split
                      · exact mirrorMergeLoSucceed size afterA
                      · split
                        · exact mirrorMergeLoCopyB size afterA
                        · rw [mirrorMergeLoCopyBIncr]
                          cases hcopyB : mergeLoCopyBIncr? afterA with
                          | none => rfl
                          | some afterB =>
                              simp only [Option.map_some, Option.bind_some]
                              change
                                (if afterB.nb = 0 then
                                    mergeLoSucceed?
                                      (mirrorMergeLoMachine size afterB)
                                  else _) =
                                  Option.map (mirrorMergeLoResult size)
                                    (if afterB.nb = 0 then
                                        mergeLoSucceed? afterB
                                      else _)
                              by_cases hnb : afterB.nb = 0
                              · simp only [hnb, if_true]
                                exact mirrorMergeLoSucceed size afterB
                              · simp only [hnb, if_false]
                                change
                                  Option.bind
                                      (mergeLoTempRead?
                                        (mirrorTempStorage size afterB.state.a)
                                        afterB.aPos) _ =
                                    Option.map (mirrorMergeLoResult size)
                                      (Option.bind
                                        (mergeLoTempRead? afterB.state.a
                                          afterB.aPos) _)
                                rw [mirrorMergeLoTempRead]
                                cases hfirstA : mergeLoTempRead? afterB.state.a
                                    afterB.aPos with
                                | none => rfl
                                | some firstA =>
                                    simp only [Option.map_some, Option.bind_some]
                                    have hafterCompare : afterB.state.key_compare =
                                        occurrenceComparator lt := by
                                      calc
                                        afterB.state.key_compare =
                                            afterA.state.key_compare :=
                                          mergeLoCopyBIncr_key_compare_of_eq_some
                                            afterA afterB hcopyB
                                        _ = state.key_compare := rfl
                                        _ = adjustedState.key_compare :=
                                          mergeLoMemcpyTempToData_key_compare_of_eq_some
                                            .gallopTempToData rfl gallopA.index
                                            adjustedState state machine.dest
                                            machine.aPos hcopyA
                                        _ = occurrenceComparator lt := hcompare'
                                    change
                                      mergeLoBindOptionAcross
                                          (gallopLeft?
                                            (mirrorMergeState size afterB.state)
                                            (mirrorSortSlice size
                                              afterB.state.data)
                                            afterB.bPos
                                            (mirrorOccurrence size firstA.key)
                                            afterB.nb 0) _ =
                                        Option.map (mirrorMergeLoResult size)
                                          (mergeLoBindOptionAcross
                                            (gallopLeft? afterB.state
                                              afterB.state.data afterB.bPos
                                              firstA.key afterB.nb 0) _)
                                    rw [mirrorGallopLeft lt size afterB.state
                                      afterB.state.data afterB.bPos firstA.key
                                      afterB.nb 0 hafterCompare]
                                    cases hgallopB : gallopLeft? afterB.state
                                        afterB.state.data afterB.bPos firstA.key
                                        afterB.nb 0 with
                                    | none => rfl
                                    | some gallopB =>
                                        change
                                          (if gallopB.fuelExhausted then
                                              mergeLoGallopFuelFailure
                                                (mirrorMergeLoMachine size afterB)
                                            else if gallopB.index > afterB.nb then
                                              none
                                            else _) =
                                            Option.map (mirrorMergeLoResult size)
                                              (if gallopB.fuelExhausted then
                                                  mergeLoGallopFuelFailure afterB
                                                else if gallopB.index > afterB.nb then
                                                  none
                                                else _)
                                        by_cases hfuelB :
                                            gallopB.fuelExhausted = true
                                        all_goals simp only [hfuelB, if_true,
                                          Bool.false_eq_true, if_false]
                                        all_goals first
                                          | exact
                                              mirrorMergeLoGallopFuelFailure
                                                size afterB
                                          | skip
                                        by_cases hindexB : gallopB.index > afterB.nb <;>
                                          simp only [hindexB, if_true, if_false,
                                            Option.map_none]
                                        change
                                          Option.bind
                                              (mergeDataMemmove? .loGallopB
                                                (mirrorSortSlice size
                                                  afterB.state.data)
                                                afterB.dest afterB.bPos
                                                gallopB.index) _ =
                                            Option.map (mirrorMergeLoResult size)
                                              (Option.bind
                                                (mergeDataMemmove? .loGallopB
                                                  afterB.state.data afterB.dest
                                                  afterB.bPos gallopB.index) _)
                                        rw [mirrorMergeDataMemmove]
                                        cases hmoveB : mergeDataMemmove?
                                            .loGallopB afterB.state.data afterB.dest
                                            afterB.bPos gallopB.index with
                                        | none => rfl
                                        | some data =>
                                            simp only [Option.map_some,
                                              Option.bind_some]
                                            let movedB :
                                                MergeLoMachine
                                                  (Occurrence alpha) nu :=
                                              { afterB with
                                                state :=
                                                  { afterB.state with data := data }
                                                dest := afterB.dest +
                                                  Int.ofNat gallopB.index
                                                bPos := afterB.bPos +
                                                  Int.ofNat gallopB.index
                                                nb := afterB.nb - gallopB.index }
                                            change
                                              (if movedB.nb = 0 then
                                                  mergeLoSucceed?
                                                    (mirrorMergeLoMachine size
                                                      movedB)
                                                else
                                                  Option.bind
                                                    (mergeLoCopyAIncr?
                                                      (mirrorMergeLoMachine size
                                                        movedB)) _) =
                                                Option.map
                                                  (mirrorMergeLoResult size)
                                                  (if movedB.nb = 0 then
                                                      mergeLoSucceed? movedB
                                                    else
                                                      Option.bind
                                                        (mergeLoCopyAIncr? movedB)
                                                        _)
                                            split
                                            · exact
                                                mirrorMergeLoSucceed size movedB
                                            · rw [mirrorMergeLoCopyAIncr]
                                              cases hcopyAOne :
                                                  mergeLoCopyAIncr? movedB with
                                              | none => rfl
                                              | some afterA =>
                                                  simp only [Option.map_some,
                                                    Option.bind_some]
                                                  change
                                                    (if afterA.na = 1 then
                                                        mergeLoCopyB?
                                                          (mirrorMergeLoMachine
                                                            size afterA)
                                                      else next'
                                                        (mirrorMergeLoMachine
                                                          size afterA)
                                                        gallopA.index
                                                        gallopB.index) =
                                                      Option.map
                                                        (mirrorMergeLoResult size)
                                                        (if afterA.na = 1 then
                                                            mergeLoCopyB? afterA
                                                          else next afterA
                                                            gallopA.index
                                                            gallopB.index)
                                                  split
                                                  · exact
                                                      mirrorMergeLoCopyB size
                                                        afterA
                                                  · apply hnext afterA
                                                      gallopA.index gallopB.index
                                                    calc
                                                      afterA.state.key_compare =
                                                          movedB.state.key_compare :=
                                                        mergeLoCopyAIncr_key_compare_of_eq_some
                                                          movedB afterA hcopyAOne
                                                      _ = afterB.state.key_compare :=
                                                        rfl
                                                      _ = occurrenceComparator lt :=
                                                        hafterCompare

set_option maxHeartbeats 2000000 in
-- Induction through the merge loop expands both ordinary and galloping phases.
theorem mirrorMergeLoLoop (lt : BoolComparator alpha) (size fuel : Nat)
    (machine : MergeLoMachine (Occurrence alpha) nu) (phase : MergeLoPhase)
    (hcompare : machine.state.key_compare = occurrenceComparator lt) :
    mergeLoLoop? fuel (mirrorMergeLoMachine size machine) phase =
      (mergeLoLoop? fuel machine phase).map (mirrorMergeLoResult size) := by
  induction fuel generalizing machine phase with
  | zero => simp [mergeLoLoop?, mirrorMergeLoResult]
  | succ fuel ih =>
      cases phase with
      | ordinary aCount bCount =>
          simp only [mergeLoLoop?]
          simp only [mirrorMergeLoMachine_na, mirrorMergeLoMachine_nb,
            mirrorMergeLoMachine_state, mirrorMergeLoMachine_aPos,
            mirrorMergeLoMachine_bPos]
          by_cases hactive : machine.na ≤ 1 ∨ machine.nb = 0 <;>
            simp only [hactive, if_pos, if_false, Option.map_none]
          rw [mirrorMergeState_tempStorage, mirrorMergeLoTempRead]
          cases hfirstA : mergeLoTempRead? machine.state.a machine.aPos with
          | none => rfl
          | some firstA =>
              simp only [Option.map_some, bind, Option.bind]
              rw [mirrorMergeState_data, mirrorSortSlice_read]
              cases hfirstB : machine.state.data.read? machine.bPos with
              | none => rfl
              | some firstB =>
                  simp only [Option.map_some]
                  simp only [mirrorMergeState_key_compare, hcompare,
                    mirrorSortSliceEntry_key,
                    iflt_mirrorOccurrence]
                  split
                  · rw [mirrorMergeLoCopyBIncr]
                    cases hcopy : mergeLoCopyBIncr? machine with
                    | none => rfl
                    | some next =>
                        simp only [Option.map_some]
                        have hnextCompare : next.state.key_compare =
                            occurrenceComparator lt :=
                          (mergeLoCopyBIncr_key_compare_of_eq_some
                            machine next hcopy).trans hcompare
                        let raised : MergeLoMachine (Occurrence alpha) nu :=
                          { next with minGallop := next.minGallop + 1 }
                        change
                          (if next.nb = 0 then
                              mergeLoSucceed?
                                (mirrorMergeLoMachine size next)
                            else if mergeLoCountAtLeastWord (bCount + 1)
                                next.minGallop then
                              mergeLoLoop? fuel
                                (mirrorMergeLoMachine size raised) .galloping
                            else
                              mergeLoLoop? fuel
                                (mirrorMergeLoMachine size next)
                                (.ordinary 0 (bCount + 1))) =
                            Option.map (mirrorMergeLoResult size)
                              (if next.nb = 0 then mergeLoSucceed? next
                                else if mergeLoCountAtLeastWord (bCount + 1)
                                    next.minGallop then
                                  mergeLoLoop? fuel raised .galloping
                                else
                                  mergeLoLoop? fuel next
                                    (.ordinary 0 (bCount + 1)))
                        split
                        · exact mirrorMergeLoSucceed size next
                        · split
                          · apply ih raised .galloping
                            simpa [raised] using hnextCompare
                          · exact ih next (.ordinary 0 (bCount + 1))
                              hnextCompare
                  · rw [mirrorMergeLoCopyAIncr]
                    cases hcopy : mergeLoCopyAIncr? machine with
                    | none => rfl
                    | some next =>
                        simp only [Option.map_some]
                        have hnextCompare : next.state.key_compare =
                            occurrenceComparator lt :=
                          (mergeLoCopyAIncr_key_compare_of_eq_some
                            machine next hcopy).trans hcompare
                        let raised : MergeLoMachine (Occurrence alpha) nu :=
                          { next with minGallop := next.minGallop + 1 }
                        change
                          (if next.na = 1 then
                              mergeLoCopyB?
                                (mirrorMergeLoMachine size next)
                            else if mergeLoCountAtLeastWord (aCount + 1)
                                next.minGallop then
                              mergeLoLoop? fuel
                                (mirrorMergeLoMachine size raised) .galloping
                            else
                              mergeLoLoop? fuel
                                (mirrorMergeLoMachine size next)
                                (.ordinary (aCount + 1) 0)) =
                            Option.map (mirrorMergeLoResult size)
                              (if next.na = 1 then mergeLoCopyB? next
                                else if mergeLoCountAtLeastWord (aCount + 1)
                                    next.minGallop then
                                  mergeLoLoop? fuel raised .galloping
                                else
                                  mergeLoLoop? fuel next
                                    (.ordinary (aCount + 1) 0))
                        split
                        · exact mirrorMergeLoCopyB size next
                        · split
                          · apply ih raised .galloping
                            simpa [raised] using hnextCompare
                          · exact ih next (.ordinary (aCount + 1) 0)
                              hnextCompare
      | galloping =>
          apply mirrorMergeLoGallopRound lt size machine _ _ hcompare
          intro next aCount bCount hnextCompare
          split
          · exact ih next .galloping hnextCompare
          · let minGallop := next.minGallop + 1
            let adjustedState := { next.state with min_gallop := minGallop }
            let adjusted : MergeLoMachine (Occurrence alpha) nu :=
              { next with state := adjustedState, minGallop := minGallop }
            change
              mergeLoLoop? fuel (mirrorMergeLoMachine size adjusted)
                  (.ordinary 0 0) =
                Option.map (mirrorMergeLoResult size)
                  (mergeLoLoop? fuel adjusted (.ordinary 0 0))
            apply ih adjusted (.ordinary 0 0)
            simpa [adjusted, adjustedState] using hnextCompare

@[simp]
theorem mirrorMergeLo (lt : BoolComparator alpha) (size : Nat)
    (state : MergeState (Occurrence alpha) nu) (ssa ssb : Int) (na nb : Nat)
    (hcompare : state.key_compare = occurrenceComparator lt) :
    mergeLo? (mirrorMergeState size state) ssa ssb na nb =
      (mergeLo? state ssa ssb na nb).map (mirrorMergeLoResult size) := by
  unfold mergeLo?
  split <;> try rfl
  rw [mirrorMergeGetmem]
  cases hallocated : mergeGetmem state (BitVec.ofNat 64 na) with
  | mk allocatedState outcome =>
      cases outcome with
      | guardRejected => simp
      | reused =>
          simp only [mirrorMergeGetmemResult]
          simp only [reduceCtorEq, if_false]
          rw [mirrorMergeLoInitialDataToTemp]
          cases hcopy : mergeLoMemcpyDataToTemp? .initialDataToTemp rfl na
              allocatedState 0 ssa with
          | none => rfl
          | some copiedState =>
              simp only [Option.map_some, bind, Option.bind]
              let initial : MergeLoMachine (Occurrence alpha) nu :=
                { state := copiedState, dest := ssa, aPos := 0, bPos := ssb,
                  na := na, nb := nb, minGallop := copiedState.min_gallop }
              change
                Option.bind (mergeLoCopyBIncr?
                    (mirrorMergeLoMachine size initial)) _ =
                  Option.map (mirrorMergeLoResult size)
                    (Option.bind (mergeLoCopyBIncr? initial) _)
              rw [mirrorMergeLoCopyBIncr]
              cases hfirst : mergeLoCopyBIncr? initial with
              | none => rfl
              | some machine =>
                  simp only [Option.map_some, Option.bind_some]
                  have hallocatedCompare : allocatedState.key_compare =
                      state.key_compare := by
                    have hframe := mergeGetmem_key_compare state
                      (BitVec.ofNat 64 na)
                    simpa [hallocated] using hframe
                  have hmachineCompare : machine.state.key_compare =
                      occurrenceComparator lt := by
                    calc
                      machine.state.key_compare = initial.state.key_compare :=
                        mergeLoCopyBIncr_key_compare_of_eq_some initial machine
                          hfirst
                      _ = copiedState.key_compare := rfl
                      _ = allocatedState.key_compare :=
                        mergeLoMemcpyDataToTemp_key_compare_of_eq_some
                          .initialDataToTemp rfl na allocatedState copiedState 0
                          ssa hcopy
                      _ = state.key_compare := hallocatedCompare
                      _ = occurrenceComparator lt := hcompare
                  change
                    (if machine.nb = 0 then
                        mergeLoSucceed? (mirrorMergeLoMachine size machine)
                      else if machine.na = 1 then
                        mergeLoCopyB? (mirrorMergeLoMachine size machine)
                      else
                        mergeLoLoop? (na + nb + 1)
                          (mirrorMergeLoMachine size machine)
                          (.ordinary 0 0)) =
                      Option.map (mirrorMergeLoResult size)
                        (if machine.nb = 0 then mergeLoSucceed? machine
                          else if machine.na = 1 then mergeLoCopyB? machine
                          else mergeLoLoop? (na + nb + 1) machine
                            (.ordinary 0 0))
                  split
                  · exact mirrorMergeLoSucceed size machine
                  · split
                    · exact mirrorMergeLoCopyB size machine
                    · exact mirrorMergeLoLoop lt size (na + nb + 1) machine
                        (.ordinary 0 0) hmachineCompare
      | grown =>
          simp only [mirrorMergeGetmemResult]
          simp only [reduceCtorEq, if_false]
          rw [mirrorMergeLoInitialDataToTemp]
          cases hcopy : mergeLoMemcpyDataToTemp? .initialDataToTemp rfl na
              allocatedState 0 ssa with
          | none => rfl
          | some copiedState =>
              simp only [Option.map_some, bind, Option.bind]
              let initial : MergeLoMachine (Occurrence alpha) nu :=
                { state := copiedState, dest := ssa, aPos := 0, bPos := ssb,
                  na := na, nb := nb, minGallop := copiedState.min_gallop }
              change
                Option.bind (mergeLoCopyBIncr?
                    (mirrorMergeLoMachine size initial)) _ =
                  Option.map (mirrorMergeLoResult size)
                    (Option.bind (mergeLoCopyBIncr? initial) _)
              rw [mirrorMergeLoCopyBIncr]
              cases hfirst : mergeLoCopyBIncr? initial with
              | none => rfl
              | some machine =>
                  simp only [Option.map_some, Option.bind_some]
                  have hallocatedCompare : allocatedState.key_compare =
                      state.key_compare := by
                    have hframe := mergeGetmem_key_compare state
                      (BitVec.ofNat 64 na)
                    simpa [hallocated] using hframe
                  have hmachineCompare : machine.state.key_compare =
                      occurrenceComparator lt := by
                    calc
                      machine.state.key_compare = initial.state.key_compare :=
                        mergeLoCopyBIncr_key_compare_of_eq_some initial machine
                          hfirst
                      _ = copiedState.key_compare := rfl
                      _ = allocatedState.key_compare :=
                        mergeLoMemcpyDataToTemp_key_compare_of_eq_some
                          .initialDataToTemp rfl na allocatedState copiedState 0
                          ssa hcopy
                      _ = state.key_compare := hallocatedCompare
                      _ = occurrenceComparator lt := hcompare
                  change
                    (if machine.nb = 0 then
                        mergeLoSucceed? (mirrorMergeLoMachine size machine)
                      else if machine.na = 1 then
                        mergeLoCopyB? (mirrorMergeLoMachine size machine)
                      else
                        mergeLoLoop? (na + nb + 1)
                          (mirrorMergeLoMachine size machine)
                          (.ordinary 0 0)) =
                      Option.map (mirrorMergeLoResult size)
                        (if machine.nb = 0 then mergeLoSucceed? machine
                          else if machine.na = 1 then mergeLoCopyB? machine
                          else mergeLoLoop? (na + nb + 1) machine
                            (.ordinary 0 0))
                  split
                  · exact mirrorMergeLoSucceed size machine
                  · split
                    · exact mirrorMergeLoCopyB size machine
                    · exact mirrorMergeLoLoop lt size (na + nb + 1) machine
                        (.ordinary 0 0) hmachineCompare

/-! ## `merge_hi` primitives -/

@[simp]
theorem mirrorMergeHiTempRead (size : Nat)
    (storage : TempStorage (Occurrence alpha) nu) (index : Int) :
    mergeHiTempRead? (mirrorTempStorage size storage) index =
      (mergeHiTempRead? storage index).map (mirrorSortSliceEntry size) := by
  unfold mergeHiTempRead?
  by_cases hnonnegative : 0 ≤ index
  · simp only [hnonnegative, if_true]
    cases hcell : storage.cells[index.toNat]? with
    | none => simp [mirrorTempStorage, hcell]
    | some cell => cases cell <;> simp [mirrorTempStorage, hcell]
  · simp [hnonnegative]

@[simp]
theorem mirrorMergeHiTempWrite (size : Nat)
    (storage : TempStorage (Occurrence alpha) nu) (index : Int)
    (entry : SortSliceEntry (Occurrence alpha) nu) :
    mergeHiTempWrite? (mirrorTempStorage size storage) index
        (mirrorSortSliceEntry size entry) =
      (mergeHiTempWrite? storage index entry).map (mirrorTempStorage size) := by
  unfold mergeHiTempWrite?
  split <;> try rfl
  simp only [mirrorTempStorage_cells_size]
  split
  · simp [mirrorTempStorage, Array.map_set]
  · rfl

@[simp]
theorem mirrorMergeHiCopyDataToTemp (size : Nat)
    (state : MergeState (Occurrence alpha) nu) (dst src : Int) :
    mergeHiCopyDataToTemp? (mirrorMergeState size state) dst src =
      (mergeHiCopyDataToTemp? state dst src).map (mirrorMergeState size) := by
  unfold mergeHiCopyDataToTemp?
  simp only [mirrorMergeState_data, mirrorMergeState_tempStorage,
    mirrorMergeState_minGallop, mirrorMergeState_listlen,
    mirrorMergeState_basekeys, mirrorMergeState_alloced,
    mirrorMergeState_pending, mirrorMergeState_key_compare,
    mirrorMergeState_mrCurrent, mirrorMergeState_mrE,
    mirrorMergeState_mrMask]
  rw [mirrorSortSlice_read]
  cases hread : state.data.read? src with
  | none => rfl
  | some entry =>
      simp only [Option.map_some, bind, Option.bind]
      rw [mirrorMergeHiTempWrite]
      cases hwrite : mergeHiTempWrite? state.a dst entry with
      | none => rfl
      | some storage => simp [mirrorMergeState]

@[simp]
theorem mirrorMergeHiCopyTempToData (size : Nat)
    (state : MergeState (Occurrence alpha) nu) (dst src : Int) :
    mergeHiCopyTempToData? (mirrorMergeState size state) dst src =
      (mergeHiCopyTempToData? state dst src).map (mirrorMergeState size) := by
  unfold mergeHiCopyTempToData?
  simp only [mirrorMergeState_data, mirrorMergeState_tempStorage,
    mirrorMergeState_minGallop, mirrorMergeState_listlen,
    mirrorMergeState_basekeys, mirrorMergeState_alloced,
    mirrorMergeState_pending, mirrorMergeState_key_compare,
    mirrorMergeState_mrCurrent, mirrorMergeState_mrE,
    mirrorMergeState_mrMask]
  rw [mirrorMergeHiTempRead]
  cases hread : mergeHiTempRead? state.a src with
  | none => rfl
  | some entry =>
      simp only [Option.map_some, bind, Option.bind]
      rw [mirrorSortSlice_write]
      cases hwrite : state.data.write? dst entry with
      | none => rfl
      | some data => simp [mirrorMergeState]

theorem mirrorMergeHiMemcpyDataToTemp
    (size : Nat) (site : MergeHiMemcpyCallsite)
    (hDirection : site.backings =
      { destination := .temporary, source := .main })
    (count : Nat) (state : MergeState (Occurrence alpha) nu)
    (dst src : Int) :
    mergeHiMemcpyDataToTemp? site hDirection count
        (mirrorMergeState size state) dst src =
      (mergeHiMemcpyDataToTemp? site hDirection count state dst src).map
        (mirrorMergeState size) := by
  induction count generalizing state dst src with
  | zero => rfl
  | succ count ih =>
      simp only [mergeHiMemcpyDataToTemp?]
      rw [mirrorMergeHiCopyDataToTemp]
      cases hcopy : mergeHiCopyDataToTemp? state dst src with
      | none => rfl
      | some state =>
          simp only [Option.map_some]
          exact ih (state := state) (dst := dst + 1) (src := src + 1)

theorem mirrorMergeHiMemcpyTempToData
    (size : Nat) (site : MergeHiMemcpyCallsite)
    (hDirection : site.backings =
      { destination := .main, source := .temporary })
    (count : Nat) (state : MergeState (Occurrence alpha) nu)
    (dst src : Int) :
    mergeHiMemcpyTempToData? site hDirection count
        (mirrorMergeState size state) dst src =
      (mergeHiMemcpyTempToData? site hDirection count state dst src).map
        (mirrorMergeState size) := by
  induction count generalizing state dst src with
  | zero => rfl
  | succ count ih =>
      simp only [mergeHiMemcpyTempToData?]
      rw [mirrorMergeHiCopyTempToData]
      cases hcopy : mergeHiCopyTempToData? state dst src with
      | none => rfl
      | some state =>
          simp only [Option.map_some]
          exact ih (state := state) (dst := dst + 1) (src := src + 1)

@[simp]
theorem mirrorMergeHiInitialDataToTemp (size count : Nat)
    (state : MergeState (Occurrence alpha) nu) (dst src : Int) :
    mergeHiMemcpyDataToTemp? .initialDataToTemp rfl count
        (mirrorMergeState size state) dst src =
      (mergeHiMemcpyDataToTemp? .initialDataToTemp rfl count state dst src).map
        (mirrorMergeState size) := by
  exact mirrorMergeHiMemcpyDataToTemp size .initialDataToTemp rfl count state
    dst src

@[simp]
theorem mirrorMergeHiGallopTempToData (size count : Nat)
    (state : MergeState (Occurrence alpha) nu) (dst src : Int) :
    mergeHiMemcpyTempToData? .gallopTempToData rfl count
        (mirrorMergeState size state) dst src =
      (mergeHiMemcpyTempToData? .gallopTempToData rfl count state dst src).map
        (mirrorMergeState size) := by
  exact mirrorMergeHiMemcpyTempToData size .gallopTempToData rfl count state
    dst src

@[simp]
theorem mirrorMergeHiFinalTempToData (size count : Nat)
    (state : MergeState (Occurrence alpha) nu) (dst src : Int) :
    mergeHiMemcpyTempToData? .finalTempToData rfl count
        (mirrorMergeState size state) dst src =
      (mergeHiMemcpyTempToData? .finalTempToData rfl count state dst src).map
        (mirrorMergeState size) := by
  exact mirrorMergeHiMemcpyTempToData size .finalTempToData rfl count state
    dst src

theorem mirrorMergeHiInitializedTempPrefixLoop (size count : Nat)
    (storage : TempStorage (Occurrence alpha) nu) (source : Nat)
    (entries : Array (SortSliceEntry (Occurrence alpha) nu)) :
    mergeHiInitializedTempPrefixLoop? count (mirrorTempStorage size storage)
        source (entries.map (mirrorSortSliceEntry size)) =
      (mergeHiInitializedTempPrefixLoop? count storage source entries).map
        (Array.map (mirrorSortSliceEntry size)) := by
  induction count generalizing source entries with
  | zero => rfl
  | succ count ih =>
      simp only [mergeHiInitializedTempPrefixLoop?]
      rw [mirrorMergeHiTempRead]
      cases hread : mergeHiTempRead? storage (Int.ofNat source) with
      | none => rfl
      | some entry =>
          simp only [Option.map_some]
          simpa [Array.map_push] using
            ih (source := source + 1) (entries := entries.push entry)

@[simp]
theorem mirrorInitializedTempPrefix (size : Nat)
    (storage : TempStorage (Occurrence alpha) nu) (count : Nat) :
    initializedTempPrefix? (mirrorTempStorage size storage) count =
      (initializedTempPrefix? storage count).map (mirrorSortSlice size) := by
  unfold initializedTempPrefix?
  have hloop :
      mergeHiInitializedTempPrefixLoop? count
          (mirrorTempStorage size storage) 0 #[] =
        (mergeHiInitializedTempPrefixLoop? count storage 0 #[]).map
          (Array.map (mirrorSortSliceEntry size)) := by
    simpa using
      mirrorMergeHiInitializedTempPrefixLoop size count storage 0 #[]
  rw [hloop]
  cases hentries : mergeHiInitializedTempPrefixLoop? count storage 0 #[] with
  | none => rfl
  | some entries => simp [mirrorSortSlice]

/-- Relabel the state carried by one backward-copy cursor result. -/
def mirrorMergeHiDataCursorResult (size : Nat)
    (result : MergeHiDataCursorResult (Occurrence alpha) nu) :
    MergeHiDataCursorResult (Occurrence alpha) nu :=
  { result with state := mirrorMergeState size result.state }

/-- Relabel the state carried by a backward merge result. -/
def mirrorMergeHiResult (size : Nat)
    (result : MergeHiResult (Occurrence alpha) nu) :
    MergeHiResult (Occurrence alpha) nu :=
  { result with state := mirrorMergeState size result.state }

/-- Relabel the state carried by a backward merge cursor. -/
def mirrorMergeHiCursor (size : Nat)
    (cursor : MergeHiCursor (Occurrence alpha) nu) :
    MergeHiCursor (Occurrence alpha) nu :=
  { cursor with state := mirrorMergeState size cursor.state }

@[simp] theorem mirrorMergeHiCursor_state (size : Nat)
    (cursor : MergeHiCursor (Occurrence alpha) nu) :
    (mirrorMergeHiCursor size cursor).state =
      mirrorMergeState size cursor.state := rfl

@[simp] theorem mirrorMergeHiCursor_dest (size : Nat)
    (cursor : MergeHiCursor (Occurrence alpha) nu) :
    (mirrorMergeHiCursor size cursor).dest = cursor.dest := rfl

@[simp] theorem mirrorMergeHiCursor_ssa (size : Nat)
    (cursor : MergeHiCursor (Occurrence alpha) nu) :
    (mirrorMergeHiCursor size cursor).ssa = cursor.ssa := rfl

@[simp] theorem mirrorMergeHiCursor_ssb (size : Nat)
    (cursor : MergeHiCursor (Occurrence alpha) nu) :
    (mirrorMergeHiCursor size cursor).ssb = cursor.ssb := rfl

@[simp] theorem mirrorMergeHiCursor_basea (size : Nat)
    (cursor : MergeHiCursor (Occurrence alpha) nu) :
    (mirrorMergeHiCursor size cursor).basea = cursor.basea := rfl

@[simp] theorem mirrorMergeHiCursor_na (size : Nat)
    (cursor : MergeHiCursor (Occurrence alpha) nu) :
    (mirrorMergeHiCursor size cursor).na = cursor.na := rfl

@[simp] theorem mirrorMergeHiCursor_nb (size : Nat)
    (cursor : MergeHiCursor (Occurrence alpha) nu) :
    (mirrorMergeHiCursor size cursor).nb = cursor.nb := rfl

@[simp] theorem mirrorMergeHiCursor_minGallop (size : Nat)
    (cursor : MergeHiCursor (Occurrence alpha) nu) :
    (mirrorMergeHiCursor size cursor).minGallop = cursor.minGallop := rfl

@[simp] theorem mirrorMergeHiCursor_phase (size : Nat)
    (cursor : MergeHiCursor (Occurrence alpha) nu) :
    (mirrorMergeHiCursor size cursor).phase = cursor.phase := rfl

@[simp]
theorem mirrorMergeHiCopyDataDecr (size : Nat)
    (state : MergeState (Occurrence alpha) nu) (dst src : Int) :
    mergeHiCopyDataDecr? (mirrorMergeState size state) dst src =
      (mergeHiCopyDataDecr? state dst src).map
        (mirrorMergeHiDataCursorResult size) := by
  unfold mergeHiCopyDataDecr?
  simp only [mirrorMergeState_data, mirrorMergeState_tempStorage,
    mirrorMergeState_minGallop, mirrorMergeState_listlen,
    mirrorMergeState_basekeys, mirrorMergeState_alloced,
    mirrorMergeState_pending, mirrorMergeState_key_compare,
    mirrorMergeState_mrCurrent, mirrorMergeState_mrE,
    mirrorMergeState_mrMask]
  rw [mirrorSortSlice_copyDecr]
  cases hcopy : state.data.copyDecr? dst src with
  | none => rfl
  | some copied => simp [mirrorMergeHiDataCursorResult, mirrorMergeState,
      mirrorCursorResult]

@[simp]
theorem mirrorMergeHiCopyTempDecr (size : Nat)
    (state : MergeState (Occurrence alpha) nu) (dst src : Int) :
    mergeHiCopyTempDecr? (mirrorMergeState size state) dst src =
      (mergeHiCopyTempDecr? state dst src).map
        (mirrorMergeHiDataCursorResult size) := by
  unfold mergeHiCopyTempDecr?
  rw [mirrorMergeHiCopyTempToData]
  cases hcopy : mergeHiCopyTempToData? state dst src with
  | none => rfl
  | some state => simp [mirrorMergeHiDataCursorResult]

theorem mergeHiMemcpyDataToTemp_key_compare_of_eq_some
    (site : MergeHiMemcpyCallsite)
    (hDirection : site.backings =
      { destination := .temporary, source := .main })
    (count : Nat) (state result : MergeState κ ν) (dst src : Int)
    (hcopy : mergeHiMemcpyDataToTemp? site hDirection count state dst src =
      some result) :
    result.key_compare = state.key_compare := by
  induction count generalizing state dst src with
  | zero =>
      simp only [mergeHiMemcpyDataToTemp?] at hcopy
      injection hcopy with hcopy
      subst result
      rfl
  | succ count ih =>
      simp only [mergeHiMemcpyDataToTemp?] at hcopy
      cases hhead : mergeHiCopyDataToTemp? state dst src with
      | none => simp [hhead] at hcopy
      | some afterHead =>
          have htail : mergeHiMemcpyDataToTemp? site hDirection count
              afterHead (dst + 1) (src + 1) = some result := by
            simpa [hhead] using hcopy
          calc
            result.key_compare = afterHead.key_compare :=
              ih afterHead (dst + 1) (src + 1) htail
            _ = state.key_compare := by
              unfold mergeHiCopyDataToTemp? at hhead
              rcases Option.bind_eq_some_iff.mp hhead with
                ⟨entry, _hread, hhead⟩
              rcases Option.bind_eq_some_iff.mp hhead with
                ⟨storage, _hwrite, hstate⟩
              injection hstate with hstate
              subst afterHead
              rfl

theorem mergeHiMemcpyTempToData_key_compare_of_eq_some
    (site : MergeHiMemcpyCallsite)
    (hDirection : site.backings =
      { destination := .main, source := .temporary })
    (count : Nat) (state result : MergeState κ ν) (dst src : Int)
    (hcopy : mergeHiMemcpyTempToData? site hDirection count state dst src =
      some result) :
    result.key_compare = state.key_compare := by
  induction count generalizing state dst src with
  | zero =>
      simp only [mergeHiMemcpyTempToData?] at hcopy
      injection hcopy with hcopy
      subst result
      rfl
  | succ count ih =>
      simp only [mergeHiMemcpyTempToData?] at hcopy
      cases hhead : mergeHiCopyTempToData? state dst src with
      | none => simp [hhead] at hcopy
      | some afterHead =>
          have htail : mergeHiMemcpyTempToData? site hDirection count
              afterHead (dst + 1) (src + 1) = some result := by
            simpa [hhead] using hcopy
          calc
            result.key_compare = afterHead.key_compare :=
              ih afterHead (dst + 1) (src + 1) htail
            _ = state.key_compare := by
              unfold mergeHiCopyTempToData? at hhead
              rcases Option.bind_eq_some_iff.mp hhead with
                ⟨entry, _hread, hhead⟩
              rcases Option.bind_eq_some_iff.mp hhead with
                ⟨data, _hwrite, hstate⟩
              injection hstate with hstate
              subst afterHead
              rfl

theorem mergeHiCopyDataDecr_key_compare_of_eq_some
    (state : MergeState κ ν) (dst src : Int)
    (result : MergeHiDataCursorResult κ ν)
    (hcopy : mergeHiCopyDataDecr? state dst src = some result) :
    result.state.key_compare = state.key_compare := by
  unfold mergeHiCopyDataDecr? at hcopy
  rcases Option.bind_eq_some_iff.mp hcopy with ⟨copied, _hcopied, hresult⟩
  injection hresult with hresult
  subst result
  rfl

theorem mergeHiCopyTempDecr_key_compare_of_eq_some
    (state : MergeState κ ν) (dst src : Int)
    (result : MergeHiDataCursorResult κ ν)
    (hcopy : mergeHiCopyTempDecr? state dst src = some result) :
    result.state.key_compare = state.key_compare := by
  unfold mergeHiCopyTempDecr? at hcopy
  rcases Option.bind_eq_some_iff.mp hcopy with ⟨afterCopy, hafter, hresult⟩
  injection hresult with hresult
  subst result
  unfold mergeHiCopyTempToData? at hafter
  rcases Option.bind_eq_some_iff.mp hafter with ⟨entry, _hread, hafter⟩
  rcases Option.bind_eq_some_iff.mp hafter with ⟨data, _hwrite, hstate⟩
  injection hstate with hstate
  subst afterCopy
  rfl

@[simp]
theorem mirrorMergeHiFuelExhausted (size : Nat)
    (cursor : MergeHiCursor (Occurrence alpha) nu) :
    mergeHiFuelExhausted (mirrorMergeHiCursor size cursor) =
      mirrorMergeHiResult size (mergeHiFuelExhausted cursor) := rfl

@[simp]
theorem mirrorMergeHiSucceed (size : Nat)
    (cursor : MergeHiCursor (Occurrence alpha) nu) :
    mergeHiSucceed? (mirrorMergeHiCursor size cursor) =
      (mergeHiSucceed? cursor).map (mirrorMergeHiResult size) := by
  unfold mergeHiSucceed?
  simp only [mirrorMergeHiCursor_nb, mirrorMergeHiCursor_state,
    mirrorMergeHiCursor_dest]
  by_cases hnb : cursor.nb = 0
  · simp [hnb, mirrorMergeHiResult]
  · simp only [hnb, if_false]
    change
      Option.bind
          (mergeHiMemcpyTempToData? .finalTempToData rfl cursor.nb
            (mirrorMergeState size cursor.state)
            (cursor.dest - Int.ofNat (cursor.nb - 1)) 0) _ =
        Option.map (mirrorMergeHiResult size)
          (Option.bind
            (mergeHiMemcpyTempToData? .finalTempToData rfl cursor.nb
              cursor.state (cursor.dest - Int.ofNat (cursor.nb - 1)) 0) _)
    rw [mirrorMergeHiFinalTempToData]
    cases hcopy : mergeHiMemcpyTempToData? .finalTempToData rfl cursor.nb
        cursor.state (cursor.dest - Int.ofNat (cursor.nb - 1)) 0 with
    | none => rfl
    | some state => simp [mirrorMergeHiResult]

@[simp]
theorem mirrorMergeHiCopyA (size : Nat)
    (cursor : MergeHiCursor (Occurrence alpha) nu) :
    mergeHiCopyA? (mirrorMergeHiCursor size cursor) =
      (mergeHiCopyA? cursor).map (mirrorMergeHiResult size) := by
  unfold mergeHiCopyA?
  simp only [mirrorMergeHiCursor_state, mirrorMergeHiCursor_dest,
    mirrorMergeHiCursor_ssa, mirrorMergeHiCursor_ssb,
    mirrorMergeHiCursor_na, mirrorMergeState_data,
    mirrorMergeState_tempStorage, mirrorMergeState_minGallop,
    mirrorMergeState_listlen, mirrorMergeState_basekeys,
    mirrorMergeState_alloced, mirrorMergeState_pending,
    mirrorMergeState_key_compare, mirrorMergeState_mrCurrent,
    mirrorMergeState_mrE, mirrorMergeState_mrMask]
  change
    (if cursor.nb = 1 ∧ 0 < cursor.na then _ else none) =
      Option.map (mirrorMergeHiResult size)
        (if cursor.nb = 1 ∧ 0 < cursor.na then _ else none)
  by_cases hactive : cursor.nb = 1 ∧ 0 < cursor.na <;>
    simp only [hactive, if_false, Option.map_none]
  rw [mirrorMergeDataMemmove]
  cases hmove : mergeDataMemmove? .hiCopyATail cursor.state.data
      (cursor.dest + (1 - Int.ofNat cursor.na))
      (cursor.ssa + (1 - Int.ofNat cursor.na)) cursor.na with
  | none => rfl
  | some data =>
      simp only [Option.map_some, bind, Option.bind]
      let movedState : MergeState (Occurrence alpha) nu :=
        { cursor.state with data := data }
      change
        Option.bind
            (mergeHiCopyTempToData? (mirrorMergeState size movedState)
              (cursor.dest - Int.ofNat cursor.na) cursor.ssb) _ =
          Option.map (mirrorMergeHiResult size)
            (Option.bind
              (mergeHiCopyTempToData? movedState
                (cursor.dest - Int.ofNat cursor.na) cursor.ssb) _)
      rw [mirrorMergeHiCopyTempToData]
      cases hcopy : mergeHiCopyTempToData? movedState
          (cursor.dest - Int.ofNat cursor.na) cursor.ssb with
      | none => rfl
      | some state => simp [mirrorMergeHiResult]

set_option maxHeartbeats 2000000 in
-- The B-side gallop proof follows several nested copy and termination branches.
theorem mirrorMergeHiGallopB (lt : BoolComparator alpha) (size : Nat)
    (afterB : MergeHiCursor (Occurrence alpha) nu) (aCount : Nat)
    (next next' : MergeHiCursor (Occurrence alpha) nu →
      Option (MergeHiResult (Occurrence alpha) nu))
    (hcompare : afterB.state.key_compare = occurrenceComparator lt)
    (hnext : ∀ cursor,
      cursor.state.key_compare = occurrenceComparator lt →
      next' (mirrorMergeHiCursor size cursor) =
        (next cursor).map (mirrorMergeHiResult size)) :
    mergeHiGallopB? (mirrorMergeHiCursor size afterB) aCount next' =
      (mergeHiGallopB? afterB aCount next).map
        (mirrorMergeHiResult size) := by
  unfold mergeHiGallopB?
  simp only [mirrorMergeHiCursor_state, mirrorMergeHiCursor_ssa,
    mirrorMergeHiCursor_nb, mirrorMergeHiCursor_dest,
    mirrorMergeHiCursor_ssb, mirrorMergeHiCursor_na,
    mirrorMergeHiCursor_minGallop]
  rw [mirrorMergeState_data, mirrorSortSlice_read]
  cases hleft : afterB.state.data.read? afterB.ssa with
  | none => rfl
  | some left =>
      simp only [Option.map_some, bind, Option.bind]
      rw [mirrorMergeState_tempStorage, mirrorInitializedTempPrefix]
      cases htemp : initializedTempPrefix? afterB.state.a afterB.nb with
      | none => rfl
      | some temp =>
          simp only [Option.map_some, mergeHiBindOptionAcross]
          change
            mergeHiBindOptionAcross
                (gallopLeft? (mirrorMergeState size afterB.state)
                  (mirrorSortSlice size temp) 0
                  (mirrorOccurrence size left.key) afterB.nb
                  (afterB.nb - 1)) _ =
              Option.map (mirrorMergeHiResult size)
                (mergeHiBindOptionAcross
                  (gallopLeft? afterB.state temp 0 left.key afterB.nb
                    (afterB.nb - 1)) _)
          rw [mirrorGallopLeft lt size afterB.state temp 0 left.key afterB.nb
            (afterB.nb - 1) hcompare]
          cases hgallop : gallopLeft? afterB.state temp 0 left.key afterB.nb
              (afterB.nb - 1) with
          | none => rfl
          | some gallopB =>
              change
                (if gallopB.fuelExhausted then
                    some (mergeHiFuelExhausted
                      (mirrorMergeHiCursor size afterB))
                  else _) =
                  Option.map (mirrorMergeHiResult size)
                    (if gallopB.fuelExhausted then
                        some (mergeHiFuelExhausted afterB)
                      else _)
              by_cases hfuel : gallopB.fuelExhausted = true
              · simp [hfuel]
              · simp only [hfuel, Bool.false_eq_true, if_false]
                simp only [mirrorMergeHiCursor_state,
                  mirrorMergeHiCursor_dest, mirrorMergeHiCursor_ssa,
                  mirrorMergeHiCursor_ssb, mirrorMergeHiCursor_basea,
                  mirrorMergeHiCursor_na, mirrorMergeHiCursor_nb,
                  mirrorMergeHiCursor_minGallop, mirrorMergeHiCursor_phase]
                have hfinish (movedB : MergeHiCursor (Occurrence alpha) nu)
                    (hmovedCompare : movedB.state.key_compare =
                      occurrenceComparator lt) :
                    (if movedB.nb = 0 ∨ movedB.nb = 1 then
                        next' (mirrorMergeHiCursor size movedB)
                      else
                        Option.bind
                          (mergeHiCopyDataDecr?
                            (mirrorMergeState size movedB.state)
                            movedB.dest movedB.ssa) fun copiedA =>
                          let afterA : MergeHiCursor (Occurrence alpha) nu :=
                            { mirrorMergeHiCursor size movedB with
                              state := copiedA.state
                              dest := copiedA.dst
                              ssa := copiedA.src
                              na := movedB.na - 1 }
                          if afterA.na = 0 then
                            next' afterA
                          else if mergeHiCountAtLeast aCount MIN_GALLOP ||
                              mergeHiCountAtLeast
                                (afterB.nb - gallopB.index) MIN_GALLOP then
                            next'
                              { afterA with
                                phase := .galloping aCount
                                  (afterB.nb - gallopB.index) }
                          else
                            let minGallop := afterB.minGallop + 1
                            let state :=
                              { afterA.state with min_gallop := minGallop }
                            next'
                              { afterA with
                                state := state
                                minGallop := minGallop
                                phase := .straight 0 0 }) =
                      Option.map (mirrorMergeHiResult size)
                        (if movedB.nb = 0 ∨ movedB.nb = 1 then
                            next movedB
                          else
                            Option.bind
                              (mergeHiCopyDataDecr? movedB.state movedB.dest
                                movedB.ssa) fun copiedA =>
                              let afterA :
                                  MergeHiCursor (Occurrence alpha) nu :=
                                { movedB with
                                  state := copiedA.state
                                  dest := copiedA.dst
                                  ssa := copiedA.src
                                  na := movedB.na - 1 }
                              if afterA.na = 0 then next afterA
                              else if mergeHiCountAtLeast aCount MIN_GALLOP ||
                                  mergeHiCountAtLeast
                                    (afterB.nb - gallopB.index) MIN_GALLOP then
                                next
                                  { afterA with
                                    phase := .galloping aCount
                                      (afterB.nb - gallopB.index) }
                              else
                                let minGallop := afterB.minGallop + 1
                                let state :=
                                  { afterA.state with min_gallop := minGallop }
                                next
                                  { afterA with
                                    state := state
                                    minGallop := minGallop
                                    phase := .straight 0 0 }) := by
                  by_cases hsmall : movedB.nb = 0 ∨ movedB.nb = 1
                  · simp only [hsmall, if_true]
                    exact hnext movedB hmovedCompare
                  · simp only [hsmall, if_false]
                    rw [mirrorMergeHiCopyDataDecr]
                    cases hcopy : mergeHiCopyDataDecr? movedB.state
                        movedB.dest movedB.ssa with
                    | none => rfl
                    | some copiedA =>
                        simp only [Option.map_some, Option.bind_some]
                        simp only [mirrorMergeHiDataCursorResult]
                        let afterA : MergeHiCursor (Occurrence alpha) nu :=
                          { movedB with
                            state := copiedA.state
                            dest := copiedA.dst
                            ssa := copiedA.src
                            na := movedB.na - 1 }
                        have hafterCompare : afterA.state.key_compare =
                            occurrenceComparator lt := by
                          calc
                            afterA.state.key_compare =
                                movedB.state.key_compare :=
                              mergeHiCopyDataDecr_key_compare_of_eq_some
                                movedB.state movedB.dest movedB.ssa copiedA hcopy
                            _ = occurrenceComparator lt := hmovedCompare
                        change
                          (if afterA.na = 0 then
                              next' (mirrorMergeHiCursor size afterA)
                            else if mergeHiCountAtLeast aCount MIN_GALLOP ||
                                mergeHiCountAtLeast
                                  (afterB.nb - gallopB.index) MIN_GALLOP then
                              next' (mirrorMergeHiCursor size
                                { afterA with
                                  phase := .galloping aCount
                                    (afterB.nb - gallopB.index) })
                            else _) =
                            Option.map (mirrorMergeHiResult size)
                              (if afterA.na = 0 then next afterA
                                else if mergeHiCountAtLeast aCount MIN_GALLOP ||
                                    mergeHiCountAtLeast
                                      (afterB.nb - gallopB.index) MIN_GALLOP then
                                  next
                                    { afterA with
                                      phase := .galloping aCount
                                        (afterB.nb - gallopB.index) }
                                else _)
                        split
                        · exact hnext afterA hafterCompare
                        · split
                          · apply hnext
                            simpa using hafterCompare
                          · let minGallop := afterB.minGallop + 1
                            let adjustedState :=
                              { afterA.state with min_gallop := minGallop }
                            let adjusted :
                                MergeHiCursor (Occurrence alpha) nu :=
                              { afterA with
                                state := adjustedState
                                minGallop := minGallop
                                phase := .straight 0 0 }
                            change
                              next' (mirrorMergeHiCursor size adjusted) =
                                Option.map (mirrorMergeHiResult size)
                                  (next adjusted)
                            apply hnext adjusted
                            simpa [adjusted, adjustedState] using hafterCompare
                by_cases hzero : afterB.nb - gallopB.index = 0
                · simp only [hzero, if_true]
                  change
                    (if afterB.nb = 0 ∨ afterB.nb = 1 then
                        next' (mirrorMergeHiCursor size afterB)
                      else
                        Option.bind
                          (mergeHiCopyDataDecr?
                            (mirrorMergeState size afterB.state)
                            afterB.dest afterB.ssa) _) =
                      Option.map (mirrorMergeHiResult size)
                        (if afterB.nb = 0 ∨ afterB.nb = 1 then
                            next afterB
                          else
                            Option.bind
                              (mergeHiCopyDataDecr? afterB.state
                                afterB.dest afterB.ssa) _)
                  simpa [hzero] using hfinish afterB hcompare
                · simp only [hzero, if_false]
                  rw [mirrorMergeHiGallopTempToData]
                  cases hcopy : mergeHiMemcpyTempToData?
                      .gallopTempToData rfl
                      (afterB.nb - gallopB.index) afterB.state
                      (afterB.dest - Int.ofNat
                        (afterB.nb - gallopB.index) + 1)
                      (afterB.ssb - Int.ofNat
                        (afterB.nb - gallopB.index) + 1) with
                  | none => rfl
                  | some state =>
                      simp only [Option.map_some]
                      let movedB : MergeHiCursor (Occurrence alpha) nu :=
                        { afterB with
                          state := state
                          dest := afterB.dest - Int.ofNat
                            (afterB.nb - gallopB.index)
                          ssb := afterB.ssb - Int.ofNat
                            (afterB.nb - gallopB.index)
                          nb := afterB.nb - (afterB.nb - gallopB.index) }
                      change
                        (if movedB.nb = 0 ∨ movedB.nb = 1 then
                            next' (mirrorMergeHiCursor size movedB)
                          else _) =
                          Option.map (mirrorMergeHiResult size)
                            (if movedB.nb = 0 ∨ movedB.nb = 1 then
                                next movedB
                              else _)
                      apply hfinish movedB
                      calc
                        movedB.state.key_compare = afterB.state.key_compare :=
                          mergeHiMemcpyTempToData_key_compare_of_eq_some
                            .gallopTempToData rfl
                            (afterB.nb - gallopB.index) afterB.state state
                            (afterB.dest - Int.ofNat
                              (afterB.nb - gallopB.index) + 1)
                            (afterB.ssb - Int.ofNat
                              (afterB.nb - gallopB.index) + 1) hcopy
                        _ = occurrenceComparator lt := hcompare

set_option maxHeartbeats 2000000 in
-- The full gallop round combines two branch-heavy gallop commutation proofs.
theorem mirrorMergeHiGallopRound (lt : BoolComparator alpha) (size : Nat)
    (cursor : MergeHiCursor (Occurrence alpha) nu)
    (next next' : MergeHiCursor (Occurrence alpha) nu →
      Option (MergeHiResult (Occurrence alpha) nu))
    (hcompare : cursor.state.key_compare = occurrenceComparator lt)
    (hnext : ∀ cursor,
      cursor.state.key_compare = occurrenceComparator lt →
      next' (mirrorMergeHiCursor size cursor) =
        (next cursor).map (mirrorMergeHiResult size)) :
    mergeHiGallopRound? (mirrorMergeHiCursor size cursor) next' =
      (mergeHiGallopRound? cursor next).map
        (mirrorMergeHiResult size) := by
  unfold mergeHiGallopRound?
  simp only [mirrorMergeHiCursor_state, mirrorMergeHiCursor_dest,
    mirrorMergeHiCursor_ssa, mirrorMergeHiCursor_ssb,
    mirrorMergeHiCursor_basea, mirrorMergeHiCursor_na,
    mirrorMergeHiCursor_nb, mirrorMergeHiCursor_minGallop,
    mirrorMergeHiCursor_phase, mirrorMergeState_data,
    mirrorMergeState_tempStorage]
  rw [expandedMirrorMergeStateWithMinGallop]
  let minGallop := mergeHiDecreaseMinGallop cursor.minGallop
  let adjustedState : MergeState (Occurrence alpha) nu :=
    { cursor.state with min_gallop := minGallop }
  have hcompare' : adjustedState.key_compare = occurrenceComparator lt := by
    simpa [adjustedState] using hcompare
  change
    Option.bind
        (mergeHiTempRead? (mirrorTempStorage size adjustedState.a)
          cursor.ssb) _ =
      Option.map (mirrorMergeHiResult size)
        (Option.bind (mergeHiTempRead? adjustedState.a cursor.ssb) _)
  rw [mirrorMergeHiTempRead]
  cases hright : mergeHiTempRead? adjustedState.a cursor.ssb with
  | none => rfl
  | some right =>
      simp only [Option.map_some, Option.bind_some,
        mergeHiBindOptionAcross]
      change
        mergeHiBindOptionAcross
            (gallopRight? (mirrorMergeState size adjustedState)
              (mirrorSortSlice size adjustedState.data) cursor.basea
              (mirrorOccurrence size right.key) cursor.na
              (cursor.na - 1)) _ =
          Option.map (mirrorMergeHiResult size)
            (mergeHiBindOptionAcross
              (gallopRight? adjustedState adjustedState.data cursor.basea
                right.key cursor.na (cursor.na - 1)) _)
      rw [mirrorGallopRight lt size adjustedState adjustedState.data
        cursor.basea right.key cursor.na (cursor.na - 1) hcompare']
      cases hgallop : gallopRight? adjustedState adjustedState.data
          cursor.basea right.key cursor.na (cursor.na - 1) with
      | none => rfl
      | some gallopA =>
          change
            (if gallopA.fuelExhausted then
                some (mergeHiFuelExhausted
                  (mirrorMergeHiCursor size
                    { cursor with state := adjustedState }))
              else _) =
              Option.map (mirrorMergeHiResult size)
                (if gallopA.fuelExhausted then
                    some (mergeHiFuelExhausted
                      { cursor with state := adjustedState })
                  else _)
          by_cases hfuel : gallopA.fuelExhausted = true
          · simp [hfuel]
          · simp only [hfuel, Bool.false_eq_true, if_false]
            have hfinish (movedA : MergeHiCursor (Occurrence alpha) nu)
                (hmovedCompare : movedA.state.key_compare =
                  occurrenceComparator lt) :
                (if movedA.na = 0 then
                    next' (mirrorMergeHiCursor size movedA)
                  else
                    Option.bind
                      (mergeHiCopyTempDecr?
                        (mirrorMergeState size movedA.state)
                        movedA.dest movedA.ssb) fun copiedB =>
                      let afterB : MergeHiCursor (Occurrence alpha) nu :=
                        { mirrorMergeHiCursor size movedA with
                          state := copiedB.state
                          dest := copiedB.dst
                          ssb := copiedB.src
                          nb := movedA.nb - 1 }
                      if afterB.nb = 1 then
                        next' afterB
                      else
                        mergeHiGallopB? afterB
                          (cursor.na - gallopA.index) next') =
                  Option.map (mirrorMergeHiResult size)
                    (if movedA.na = 0 then next movedA
                      else
                        Option.bind
                          (mergeHiCopyTempDecr? movedA.state movedA.dest
                            movedA.ssb) fun copiedB =>
                          let afterB : MergeHiCursor (Occurrence alpha) nu :=
                            { movedA with
                              state := copiedB.state
                              dest := copiedB.dst
                              ssb := copiedB.src
                              nb := movedA.nb - 1 }
                          if afterB.nb = 1 then next afterB
                          else
                            mergeHiGallopB? afterB
                              (cursor.na - gallopA.index) next) := by
              by_cases hdone : movedA.na = 0
              · simp only [hdone, if_true]
                exact hnext movedA hmovedCompare
              · simp only [hdone, if_false]
                rw [mirrorMergeHiCopyTempDecr]
                cases hcopy : mergeHiCopyTempDecr? movedA.state movedA.dest
                    movedA.ssb with
                | none => rfl
                | some copiedB =>
                    simp only [Option.map_some, Option.bind_some]
                    simp only [mirrorMergeHiDataCursorResult]
                    let afterB : MergeHiCursor (Occurrence alpha) nu :=
                      { movedA with
                        state := copiedB.state
                        dest := copiedB.dst
                        ssb := copiedB.src
                        nb := movedA.nb - 1 }
                    have hafterCompare : afterB.state.key_compare =
                        occurrenceComparator lt := by
                      calc
                        afterB.state.key_compare = movedA.state.key_compare :=
                          mergeHiCopyTempDecr_key_compare_of_eq_some
                            movedA.state movedA.dest movedA.ssb copiedB hcopy
                        _ = occurrenceComparator lt := hmovedCompare
                    change
                      (if afterB.nb = 1 then
                          next' (mirrorMergeHiCursor size afterB)
                        else
                          mergeHiGallopB?
                            (mirrorMergeHiCursor size afterB)
                            (cursor.na - gallopA.index) next') =
                        Option.map (mirrorMergeHiResult size)
                          (if afterB.nb = 1 then next afterB
                            else mergeHiGallopB? afterB
                              (cursor.na - gallopA.index) next)
                    split
                    · exact hnext afterB hafterCompare
                    · exact mirrorMergeHiGallopB lt size afterB
                        (cursor.na - gallopA.index) next next' hafterCompare
                        hnext
            by_cases hzero : cursor.na - gallopA.index = 0
            · simp only [hzero, if_true]
              let movedA : MergeHiCursor (Occurrence alpha) nu :=
                { cursor with state := adjustedState, minGallop := minGallop }
              change
                (if movedA.na = 0 then
                    next' (mirrorMergeHiCursor size movedA)
                  else _) =
                  Option.map (mirrorMergeHiResult size)
                    (if movedA.na = 0 then next movedA else _)
              simpa [movedA, adjustedState, minGallop, hzero] using
                hfinish movedA hcompare'
            · simp only [hzero, if_false]
              rw [mirrorMergeDataMemmove]
              cases hmove : mergeDataMemmove? .hiGallopA adjustedState.data
                  (cursor.dest - Int.ofNat (cursor.na - gallopA.index) + 1)
                  (cursor.ssa - Int.ofNat (cursor.na - gallopA.index) + 1)
                  (cursor.na - gallopA.index) with
              | none => rfl
              | some data =>
                  simp only [Option.map_some]
                  let movedA : MergeHiCursor (Occurrence alpha) nu :=
                    { cursor with
                      state := { adjustedState with data := data }
                      dest := cursor.dest - Int.ofNat
                        (cursor.na - gallopA.index)
                      ssa := cursor.ssa - Int.ofNat
                        (cursor.na - gallopA.index)
                      na := cursor.na - (cursor.na - gallopA.index)
                      minGallop := minGallop }
                  change
                    (if movedA.na = 0 then
                        next' (mirrorMergeHiCursor size movedA)
                      else _) =
                      Option.map (mirrorMergeHiResult size)
                        (if movedA.na = 0 then next movedA else _)
                  apply hfinish movedA
                  simpa [movedA] using hcompare'

set_option maxHeartbeats 2000000 in
-- Recursive merge-hi commutation expands straight and galloping loop phases.
theorem mirrorMergeHiLoop (lt : BoolComparator alpha) (size fuel : Nat)
    (cursor : MergeHiCursor (Occurrence alpha) nu)
    (hcompare : cursor.state.key_compare = occurrenceComparator lt) :
    mergeHiLoop? fuel (mirrorMergeHiCursor size cursor) =
      (mergeHiLoop? fuel cursor).map (mirrorMergeHiResult size) := by
  induction fuel generalizing cursor with
  | zero =>
      simp only [mergeHiLoop?, mirrorMergeHiCursor_na,
        mirrorMergeHiCursor_nb]
      by_cases hdone : cursor.na = 0 ∨ cursor.nb = 0
      · simp only [hdone, if_true]
        exact mirrorMergeHiSucceed size cursor
      · simp only [hdone, if_false]
        by_cases hone : cursor.nb = 1
        · simp only [hone, if_true]
          exact mirrorMergeHiCopyA size cursor
        · simp only [hone, if_false]
          exact congrArg some (mirrorMergeHiFuelExhausted size cursor)
  | succ fuel ih =>
      simp only [mergeHiLoop?, mirrorMergeHiCursor_na,
        mirrorMergeHiCursor_nb, mirrorMergeHiCursor_phase,
        mirrorMergeHiCursor_state, mirrorMergeHiCursor_dest,
        mirrorMergeHiCursor_ssa, mirrorMergeHiCursor_ssb,
        mirrorMergeHiCursor_basea, mirrorMergeHiCursor_minGallop]
      by_cases hdone : cursor.na = 0 ∨ cursor.nb = 0
      · simp only [hdone, if_true]
        exact mirrorMergeHiSucceed size cursor
      · simp only [hdone, if_false]
        by_cases hone : cursor.nb = 1
        · simp only [hone, if_true]
          exact mirrorMergeHiCopyA size cursor
        · simp only [hone, if_false]
          cases hphase : cursor.phase with
          | straight aCount bCount =>
              rw [mirrorMergeState_tempStorage, mirrorMergeHiTempRead]
              cases hright : mergeHiTempRead? cursor.state.a cursor.ssb with
              | none => rfl
              | some right =>
                  simp only [Option.map_some, bind, Option.bind]
                  rw [mirrorMergeState_data, mirrorSortSlice_read]
                  cases hleft : cursor.state.data.read? cursor.ssa with
                  | none => rfl
                  | some left =>
                      simp only [Option.map_some,
                        mirrorMergeState_key_compare, hcompare,
                        mirrorSortSliceEntry_key, iflt_mirrorOccurrence]
                      split
                      · rw [mirrorMergeHiCopyDataDecr]
                        cases hcopy : mergeHiCopyDataDecr? cursor.state
                            cursor.dest cursor.ssa with
                        | none => rfl
                        | some copied =>
                            simp only [Option.map_some,
                              mirrorMergeHiDataCursorResult]
                            let nextCursor :
                                MergeHiCursor (Occurrence alpha) nu :=
                              { cursor with
                                state := copied.state
                                dest := copied.dst
                                ssa := copied.src
                                na := cursor.na - 1
                                phase :=
                                  if mergeHiCountAtLeast (aCount + 1)
                                      cursor.minGallop then
                                    .galloping (aCount + 1) 0
                                  else
                                    .straight (aCount + 1) 0
                                minGallop :=
                                  if mergeHiCountAtLeast (aCount + 1)
                                      cursor.minGallop then
                                    cursor.minGallop + 1
                                  else
                                    cursor.minGallop }
                            change
                              mergeHiLoop? fuel
                                  (mirrorMergeHiCursor size nextCursor) =
                                Option.map (mirrorMergeHiResult size)
                                  (mergeHiLoop? fuel nextCursor)
                            apply ih nextCursor
                            calc
                              nextCursor.state.key_compare =
                                  cursor.state.key_compare :=
                                mergeHiCopyDataDecr_key_compare_of_eq_some
                                  cursor.state cursor.dest cursor.ssa copied
                                  hcopy
                              _ = occurrenceComparator lt := hcompare
                      · rw [mirrorMergeHiCopyTempDecr]
                        cases hcopy : mergeHiCopyTempDecr? cursor.state
                            cursor.dest cursor.ssb with
                        | none => rfl
                        | some copied =>
                            simp only [Option.map_some,
                              mirrorMergeHiDataCursorResult]
                            let nextCursor :
                                MergeHiCursor (Occurrence alpha) nu :=
                              { cursor with
                                state := copied.state
                                dest := copied.dst
                                ssb := copied.src
                                nb := cursor.nb - 1
                                phase :=
                                  if mergeHiCountAtLeast (bCount + 1)
                                      cursor.minGallop then
                                    .galloping 0 (bCount + 1)
                                  else
                                    .straight 0 (bCount + 1)
                                minGallop :=
                                  if mergeHiCountAtLeast (bCount + 1)
                                      cursor.minGallop then
                                    cursor.minGallop + 1
                                  else
                                    cursor.minGallop }
                            change
                              mergeHiLoop? fuel
                                  (mirrorMergeHiCursor size nextCursor) =
                                Option.map (mirrorMergeHiResult size)
                                  (mergeHiLoop? fuel nextCursor)
                            apply ih nextCursor
                            calc
                              nextCursor.state.key_compare =
                                  cursor.state.key_compare :=
                                mergeHiCopyTempDecr_key_compare_of_eq_some
                                  cursor.state cursor.dest cursor.ssb copied
                                  hcopy
                              _ = occurrenceComparator lt := hcompare
          | galloping aCount bCount =>
              exact mirrorMergeHiGallopRound lt size cursor
                (mergeHiLoop? fuel) (mergeHiLoop? fuel) hcompare
                (fun nextCursor hnextCompare =>
                  ih nextCursor hnextCompare)

@[simp]
theorem mirrorMergeHi (lt : BoolComparator alpha) (size : Nat)
    (state : MergeState (Occurrence alpha) nu) (ssa ssb : Int) (na nb : Nat)
    (hcompare : state.key_compare = occurrenceComparator lt) :
    mergeHi? (mirrorMergeState size state) ssa ssb na nb =
      (mergeHi? state ssa ssb na nb).map (mirrorMergeHiResult size) := by
  unfold mergeHi?
  split <;> try rfl
  rw [mirrorMergeGetmem]
  cases hallocated : mergeGetmem state (BitVec.ofNat 64 nb) with
  | mk allocatedState outcome =>
      cases outcome with
      | guardRejected =>
          simp [mirrorMergeGetmemResult, mirrorMergeHiResult]
      | reused =>
          simp only [mirrorMergeGetmemResult]
          rw [mirrorMergeHiInitialDataToTemp]
          cases hcopy : mergeHiMemcpyDataToTemp? .initialDataToTemp rfl nb
              allocatedState 0 ssb with
          | none => rfl
          | some copiedState =>
              simp only [Option.map_some, bind, Option.bind]
              let initial : MergeState (Occurrence alpha) nu := copiedState
              rw [mirrorMergeHiCopyDataDecr]
              cases hfirst : mergeHiCopyDataDecr? initial
                  (ssb + Int.ofNat (nb - 1))
                  (ssa + Int.ofNat (na - 1)) with
              | none => rfl
              | some copied =>
                  simp only [Option.map_some,
                    mirrorMergeHiDataCursorResult]
                  let cursor : MergeHiCursor (Occurrence alpha) nu :=
                    { state := copied.state
                      dest := copied.dst
                      ssa := copied.src
                      ssb := Int.ofNat (nb - 1)
                      basea := ssa
                      na := na - 1
                      nb := nb
                      minGallop := copied.state.min_gallop
                      phase := .straight 0 0 }
                  have hallocatedCompare : allocatedState.key_compare =
                      state.key_compare := by
                    have hframe := mergeGetmem_key_compare state
                      (BitVec.ofNat 64 nb)
                    simpa [hallocated] using hframe
                  have hcursorCompare : cursor.state.key_compare =
                      occurrenceComparator lt := by
                    calc
                      cursor.state.key_compare = initial.key_compare :=
                        mergeHiCopyDataDecr_key_compare_of_eq_some initial
                          (ssb + Int.ofNat (nb - 1))
                          (ssa + Int.ofNat (na - 1)) copied hfirst
                      _ = copiedState.key_compare := rfl
                      _ = allocatedState.key_compare :=
                        mergeHiMemcpyDataToTemp_key_compare_of_eq_some
                          .initialDataToTemp rfl nb allocatedState copiedState
                          0 ssb hcopy
                      _ = state.key_compare := hallocatedCompare
                      _ = occurrenceComparator lt := hcompare
                  change
                    mergeHiLoop? (na + nb)
                        (mirrorMergeHiCursor size cursor) =
                      Option.map (mirrorMergeHiResult size)
                        (mergeHiLoop? (na + nb) cursor)
                  exact mirrorMergeHiLoop lt size (na + nb) cursor
                    hcursorCompare
      | grown =>
          simp only [mirrorMergeGetmemResult]
          rw [mirrorMergeHiInitialDataToTemp]
          cases hcopy : mergeHiMemcpyDataToTemp? .initialDataToTemp rfl nb
              allocatedState 0 ssb with
          | none => rfl
          | some copiedState =>
              simp only [Option.map_some, bind, Option.bind]
              let initial : MergeState (Occurrence alpha) nu := copiedState
              rw [mirrorMergeHiCopyDataDecr]
              cases hfirst : mergeHiCopyDataDecr? initial
                  (ssb + Int.ofNat (nb - 1))
                  (ssa + Int.ofNat (na - 1)) with
              | none => rfl
              | some copied =>
                  simp only [Option.map_some,
                    mirrorMergeHiDataCursorResult]
                  let cursor : MergeHiCursor (Occurrence alpha) nu :=
                    { state := copied.state
                      dest := copied.dst
                      ssa := copied.src
                      ssb := Int.ofNat (nb - 1)
                      basea := ssa
                      na := na - 1
                      nb := nb
                      minGallop := copied.state.min_gallop
                      phase := .straight 0 0 }
                  have hallocatedCompare : allocatedState.key_compare =
                      state.key_compare := by
                    have hframe := mergeGetmem_key_compare state
                      (BitVec.ofNat 64 nb)
                    simpa [hallocated] using hframe
                  have hcursorCompare : cursor.state.key_compare =
                      occurrenceComparator lt := by
                    calc
                      cursor.state.key_compare = initial.key_compare :=
                        mergeHiCopyDataDecr_key_compare_of_eq_some initial
                          (ssb + Int.ofNat (nb - 1))
                          (ssa + Int.ofNat (na - 1)) copied hfirst
                      _ = copiedState.key_compare := rfl
                      _ = allocatedState.key_compare :=
                        mergeHiMemcpyDataToTemp_key_compare_of_eq_some
                          .initialDataToTemp rfl nb allocatedState copiedState
                          0 ssb hcopy
                      _ = state.key_compare := hallocatedCompare
                      _ = occurrenceComparator lt := hcompare
                  change
                    mergeHiLoop? (na + nb)
                        (mirrorMergeHiCursor size cursor) =
                      Option.map (mirrorMergeHiResult size)
                        (mergeHiLoop? (na + nb) cursor)
                  exact mirrorMergeHiLoop lt size (na + nb) cursor
                    hcursorCompare

/-! ## Comparator frames for the public merge evaluators -/

private theorem mergeLoSucceed_key_compare_of_eq_some
    (machine : MergeLoMachine κ ν) (result : MergeLoResult κ ν)
    (h : mergeLoSucceed? machine = some result) :
    result.state.key_compare = machine.state.key_compare := by
  unfold mergeLoSucceed? at h
  rcases Option.bind_eq_some_iff.mp h with ⟨state, hcopy, hresult⟩
  injection hresult with hresult
  subst result
  exact mergeLoMemcpyTempToData_key_compare_of_eq_some
    .finalTempToData rfl machine.na machine.state state machine.dest
    machine.aPos hcopy

private theorem mergeLoCopyB_key_compare_of_eq_some
    (machine : MergeLoMachine κ ν) (result : MergeLoResult κ ν)
    (h : mergeLoCopyB? machine = some result) :
    result.state.key_compare = machine.state.key_compare := by
  simp only [mergeLoCopyB?, bind, Option.bind] at h
  split at h <;> simp_all
  split at h <;> simp_all
  split at h <;> simp_all
  split at h <;> simp_all
  subst result
  rfl

private theorem mergeLoGallopFuelFailure_key_compare_of_eq_some
    (machine : MergeLoMachine κ ν) (result : MergeLoResult κ ν)
    (h : mergeLoGallopFuelFailure machine = some result) :
    result.state.key_compare = machine.state.key_compare := by
  simp [mergeLoGallopFuelFailure, mergeLoOutOfFuel] at h
  subst result
  rfl

private structure MergeComparatorFrame (before after : MergeState κ ν) : Prop
    where
  comparator : after.key_compare = before.key_compare

namespace MergeComparatorFrame

@[aesop safe forward]
private theorem refl (state : MergeState κ ν) :
    MergeComparatorFrame state state := ⟨rfl⟩

@[aesop safe forward]
private theorem trans {first second third : MergeState κ ν}
    (hfirst : MergeComparatorFrame first second)
    (hsecond : MergeComparatorFrame second third) :
    MergeComparatorFrame first third :=
  ⟨hsecond.comparator.trans hfirst.comparator⟩

end MergeComparatorFrame

@[aesop safe forward]
private theorem mergeLoMemcpyDataToTemp_comparatorFrame
    (site : MergeLoMemcpyCallsite)
    (hDirection : site.backings =
      { destination := .temporary, source := .main })
    (count : Nat) (state result : MergeState κ ν) (dst : Nat) (src : Int)
    (h : mergeLoMemcpyDataToTemp? site hDirection count state dst src =
      some result) :
    MergeComparatorFrame state result :=
  ⟨mergeLoMemcpyDataToTemp_key_compare_of_eq_some site hDirection count
    state result dst src h⟩

@[aesop safe forward]
private theorem mergeLoMemcpyTempToData_comparatorFrame
    (site : MergeLoMemcpyCallsite)
    (hDirection : site.backings =
      { destination := .main, source := .temporary })
    (count : Nat) (state result : MergeState κ ν) (dst : Int) (src : Nat)
    (h : mergeLoMemcpyTempToData? site hDirection count state dst src =
      some result) :
    MergeComparatorFrame state result :=
  ⟨mergeLoMemcpyTempToData_key_compare_of_eq_some site hDirection count
    state result dst src h⟩

@[aesop safe forward]
private theorem mergeLoCopyAIncr_comparatorFrame
    (machine result : MergeLoMachine κ ν)
    (h : mergeLoCopyAIncr? machine = some result) :
    MergeComparatorFrame machine.state result.state :=
  ⟨mergeLoCopyAIncr_key_compare_of_eq_some machine result h⟩

@[aesop safe forward]
private theorem mergeLoCopyBIncr_comparatorFrame
    (machine result : MergeLoMachine κ ν)
    (h : mergeLoCopyBIncr? machine = some result) :
    MergeComparatorFrame machine.state result.state :=
  ⟨mergeLoCopyBIncr_key_compare_of_eq_some machine result h⟩

@[aesop safe forward]
private theorem mergeLoSucceed_comparatorFrame
    (machine : MergeLoMachine κ ν) (result : MergeLoResult κ ν)
    (h : mergeLoSucceed? machine = some result) :
    MergeComparatorFrame machine.state result.state :=
  ⟨mergeLoSucceed_key_compare_of_eq_some machine result h⟩

@[aesop safe forward]
private theorem mergeLoCopyB_comparatorFrame
    (machine : MergeLoMachine κ ν) (result : MergeLoResult κ ν)
    (h : mergeLoCopyB? machine = some result) :
    MergeComparatorFrame machine.state result.state :=
  ⟨mergeLoCopyB_key_compare_of_eq_some machine result h⟩

@[aesop safe forward]
private theorem mergeLoGallopFuelFailure_comparatorFrame
    (machine : MergeLoMachine κ ν) (result : MergeLoResult κ ν)
    (h : mergeLoGallopFuelFailure machine = some result) :
    MergeComparatorFrame machine.state result.state :=
  ⟨mergeLoGallopFuelFailure_key_compare_of_eq_some machine result h⟩

set_option maxHeartbeats 5000000 in
-- Comparator framing traverses every nested gallop and terminal-copy branch.
set_option maxRecDepth 10000 in
private theorem mergeLoGallopRound_key_compare_of_eq_some
    (machine : MergeLoMachine κ ν)
    (next : MergeLoMachine κ ν → Nat → Nat → Option (MergeLoResult κ ν))
    (hnext : ∀ machine' aCount bCount result,
      next machine' aCount bCount = some result →
        MergeComparatorFrame machine'.state result.state)
    (result : MergeLoResult κ ν)
    (h : mergeLoGallopRound? machine next = some result) :
    MergeComparatorFrame machine.state result.state := by
  unfold mergeLoGallopRound? at h
  by_cases hactive : machine.na ≤ 1 ∨ machine.nb = 0
  · simp [hactive] at h
  · simp only [hactive, if_false] at h
    let minGallop :=
      if (1 : PySSize).slt machine.minGallop then
        machine.minGallop - 1
      else machine.minGallop
    let adjustedState := { machine.state with min_gallop := minGallop }
    let adjusted : MergeLoMachine κ ν :=
      { machine with state := adjustedState, minGallop := minGallop }
    have hadjust : MergeComparatorFrame machine.state adjusted.state := ⟨rfl⟩
    change Option.bind
      (adjusted.state.data.read? adjusted.bPos) _ = some result at h
    rcases Option.bind_eq_some_iff.mp h with ⟨firstB, hfirstB, h⟩
    change Option.bind
      (mergeLoTempRun? adjusted.state.a adjusted.aPos adjusted.na) _ =
        some result at h
    rcases Option.bind_eq_some_iff.mp h with ⟨activeA, hactiveA, h⟩
    change mergeLoBindOptionAcross
      (gallopRight? adjusted.state activeA 0 firstB.key adjusted.na 0) _ =
        some result at h
    cases hgallopA : gallopRight? adjusted.state activeA 0 firstB.key
        adjusted.na 0 with
    | none => simp [mergeLoBindOptionAcross, hgallopA] at h
    | some gallopA =>
        simp only [mergeLoBindOptionAcross, hgallopA] at h
        by_cases hfuelA : gallopA.fuelExhausted = true
        · simp only [hfuelA, if_true] at h
          exact hadjust.trans
            (mergeLoGallopFuelFailure_comparatorFrame adjusted result h)
        · simp only [hfuelA, Bool.false_eq_true, if_false] at h
          by_cases hindexA : gallopA.index > machine.na
          · simp [hindexA] at h
          · simp only [hindexA, if_false] at h
            rcases Option.bind_eq_some_iff.mp h with
              ⟨stateA, hcopyA, h⟩
            let afterA : MergeLoMachine κ ν :=
              { adjusted with
                state := stateA
                dest := adjusted.dest + Int.ofNat gallopA.index
                aPos := adjusted.aPos + gallopA.index
                na := adjusted.na - gallopA.index }
            have hframeA :
                MergeComparatorFrame adjusted.state afterA.state := by
              simpa [afterA] using
                (mergeLoMemcpyTempToData_comparatorFrame
                  .gallopTempToData rfl gallopA.index adjusted.state stateA
                  adjusted.dest adjusted.aPos hcopyA)
            change
              (if afterA.na = 0 then mergeLoSucceed? afterA
                else if afterA.na = 1 then mergeLoCopyB? afterA
                else Option.bind (mergeLoCopyBIncr? afterA) _) =
                some result at h
            by_cases hzeroA : afterA.na = 0
            · rw [if_pos hzeroA] at h
              exact (hadjust.trans hframeA).trans
                (mergeLoSucceed_comparatorFrame afterA result h)
            · rw [if_neg hzeroA] at h
              by_cases honeA : afterA.na = 1
              · rw [if_pos honeA] at h
                exact (hadjust.trans hframeA).trans
                  (mergeLoCopyB_comparatorFrame afterA result h)
              · rw [if_neg honeA] at h
                rcases Option.bind_eq_some_iff.mp h with
                  ⟨afterB, hcopyB, h⟩
                have hframeB :
                    MergeComparatorFrame afterA.state afterB.state :=
                  mergeLoCopyBIncr_comparatorFrame afterA afterB hcopyB
                change
                  (if afterB.nb = 0 then mergeLoSucceed? afterB
                    else Option.bind
                      (mergeLoTempRead? afterB.state.a afterB.aPos) _) =
                    some result at h
                by_cases hzeroB : afterB.nb = 0
                · rw [if_pos hzeroB] at h
                  exact ((hadjust.trans hframeA).trans hframeB).trans
                    (mergeLoSucceed_comparatorFrame afterB result h)
                · rw [if_neg hzeroB] at h
                  rcases Option.bind_eq_some_iff.mp h with
                    ⟨firstA, hfirstA, h⟩
                  change mergeLoBindOptionAcross
                    (gallopLeft? afterB.state afterB.state.data afterB.bPos
                      firstA.key afterB.nb 0) _ = some result at h
                  cases hgallopB : gallopLeft? afterB.state afterB.state.data
                      afterB.bPos firstA.key afterB.nb 0 with
                  | none => simp [mergeLoBindOptionAcross, hgallopB] at h
                  | some gallopB =>
                      simp only [mergeLoBindOptionAcross, hgallopB] at h
                      by_cases hfuelB : gallopB.fuelExhausted = true
                      · simp only [hfuelB, if_true] at h
                        exact ((hadjust.trans hframeA).trans hframeB).trans
                          (mergeLoGallopFuelFailure_comparatorFrame afterB
                            result h)
                      · simp only [hfuelB, Bool.false_eq_true, if_false] at h
                        by_cases hindexB : gallopB.index > afterB.nb
                        · simp [hindexB] at h
                        · simp only [hindexB, if_false] at h
                          rcases Option.bind_eq_some_iff.mp h with
                            ⟨data, hmove, h⟩
                          let movedB : MergeLoMachine κ ν :=
                            { afterB with
                              state := { afterB.state with data := data }
                              dest := afterB.dest + Int.ofNat gallopB.index
                              bPos := afterB.bPos + Int.ofNat gallopB.index
                              nb := afterB.nb - gallopB.index }
                          have hframeMoved : MergeComparatorFrame
                              afterB.state movedB.state := ⟨rfl⟩
                          change
                            (if movedB.nb = 0 then mergeLoSucceed? movedB
                              else Option.bind
                                (mergeLoCopyAIncr? movedB) _) = some result at h
                          by_cases hdoneB : movedB.nb = 0
                          · rw [if_pos hdoneB] at h
                            exact (((hadjust.trans hframeA).trans hframeB).trans
                              hframeMoved).trans
                                (mergeLoSucceed_comparatorFrame movedB result h)
                          · rw [if_neg hdoneB] at h
                            rcases Option.bind_eq_some_iff.mp h with
                              ⟨afterAOne, hcopyAOne, h⟩
                            have hframeAOne : MergeComparatorFrame movedB.state
                                afterAOne.state :=
                              mergeLoCopyAIncr_comparatorFrame movedB afterAOne
                                hcopyAOne
                            change
                              (if afterAOne.na = 1 then
                                  mergeLoCopyB? afterAOne
                                else next afterAOne gallopA.index gallopB.index) =
                                some result at h
                            by_cases honeFinal : afterAOne.na = 1
                            · rw [if_pos honeFinal] at h
                              exact ((((hadjust.trans hframeA).trans
                                hframeB).trans hframeMoved).trans
                                  hframeAOne).trans
                                    (mergeLoCopyB_comparatorFrame afterAOne
                                      result h)
                            · rw [if_neg honeFinal] at h
                              exact ((((hadjust.trans hframeA).trans
                                hframeB).trans hframeMoved).trans
                                  hframeAOne).trans
                                    (hnext afterAOne gallopA.index gallopB.index
                                      result h)

set_option maxHeartbeats 5000000 in
-- Loop framing analyzes all ordinary branches before invoking the induction step.
set_option maxRecDepth 10000 in
@[aesop safe forward]
private theorem mergeLoLoop_comparatorFrame_of_eq_some
    (fuel : Nat) (machine : MergeLoMachine κ ν) (phase : MergeLoPhase)
    (result : MergeLoResult κ ν)
    (h : mergeLoLoop? fuel machine phase = some result) :
    MergeComparatorFrame machine.state result.state := by
  induction fuel generalizing machine phase result with
  | zero =>
      simp only [mergeLoLoop?] at h
      injection h with h
      subst result
      exact MergeComparatorFrame.refl machine.state
  | succ fuel ih =>
      cases phase with
      | ordinary aCount bCount =>
          simp only [mergeLoLoop?, bind, Option.bind] at h
          by_cases hactive : machine.na ≤ 1 ∨ machine.nb = 0
          · simp only [hactive, if_true, reduceCtorEq] at h
          · simp only [hactive, if_false] at h
            rcases Option.bind_eq_some_iff.mp h with
              ⟨firstA, hfirstA, h⟩
            rcases Option.bind_eq_some_iff.mp h with
              ⟨firstB, hfirstB, h⟩
            by_cases hcompare :
                iflt machine.state.key_compare firstB.key firstA.key = true
            · simp only [hcompare, if_true] at h
              rcases Option.bind_eq_some_iff.mp h with
                ⟨next, hcopy, h⟩
              have hframe : MergeComparatorFrame machine.state next.state :=
                mergeLoCopyBIncr_comparatorFrame machine next hcopy
              by_cases hdone : next.nb = 0
              · rw [if_pos hdone] at h
                exact hframe.trans
                  (mergeLoSucceed_comparatorFrame next result h)
              · rw [if_neg hdone] at h
                by_cases hgallop :
                    mergeLoCountAtLeastWord (bCount + 1) next.minGallop = true
                · rw [if_pos hgallop] at h
                  let raised : MergeLoMachine κ ν :=
                    { next with minGallop := next.minGallop + 1 }
                  have hraised :
                      MergeComparatorFrame next.state raised.state := ⟨rfl⟩
                  exact hframe.trans
                    (hraised.trans (ih raised .galloping result h))
                · rw [if_neg hgallop] at h
                  exact hframe.trans
                    (ih next (.ordinary 0 (bCount + 1)) result h)
            · simp only [hcompare, Bool.false_eq_true, if_false] at h
              rcases Option.bind_eq_some_iff.mp h with
                ⟨next, hcopy, h⟩
              have hframe : MergeComparatorFrame machine.state next.state :=
                mergeLoCopyAIncr_comparatorFrame machine next hcopy
              by_cases hdone : next.na = 1
              · rw [if_pos hdone] at h
                exact hframe.trans
                  (mergeLoCopyB_comparatorFrame next result h)
              · rw [if_neg hdone] at h
                by_cases hgallop :
                    mergeLoCountAtLeastWord (aCount + 1) next.minGallop = true
                · rw [if_pos hgallop] at h
                  let raised : MergeLoMachine κ ν :=
                    { next with minGallop := next.minGallop + 1 }
                  have hraised :
                      MergeComparatorFrame next.state raised.state := ⟨rfl⟩
                  exact hframe.trans
                    (hraised.trans (ih raised .galloping result h))
                · rw [if_neg hgallop] at h
                  exact hframe.trans
                    (ih next (.ordinary (aCount + 1) 0) result h)
      | galloping =>
          let next : MergeLoMachine κ ν → Nat → Nat →
              Option (MergeLoResult κ ν) :=
            fun machine' aCount bCount =>
            if MIN_GALLOP.toNat ≤ aCount ∨ MIN_GALLOP.toNat ≤ bCount then
              mergeLoLoop? fuel machine' .galloping
            else
              let minGallop := machine'.minGallop + 1
              let state := { machine'.state with min_gallop := minGallop }
              mergeLoLoop? fuel
                { machine' with state := state, minGallop := minGallop }
                (.ordinary 0 0)
          have hround : mergeLoGallopRound? machine next = some result := by
            simpa only [mergeLoLoop?] using h
          apply mergeLoGallopRound_key_compare_of_eq_some machine next _
            result hround
          intro machine' aCount bCount result' hresult
          dsimp only [next] at hresult
          split at hresult
          · exact ih machine' .galloping result' hresult
          · have hframe := ih _ (.ordinary 0 0) result' hresult
            exact ⟨hframe.comparator⟩

@[aesop safe forward]
private theorem mergeGetmem_comparatorFrame
    (state : MergeState κ ν) (need : PySSize) :
    MergeComparatorFrame state (mergeGetmem state need).state :=
  ⟨mergeGetmem_key_compare state need⟩

@[aesop safe forward]
private theorem mergeLoFailure_comparatorFrame
    (state : MergeState κ ν) :
    MergeComparatorFrame state (mergeLoFailure state).state :=
  ⟨rfl⟩

private theorem mergeLo_comparatorFrame_of_eq_some
    (state : MergeState κ ν) (ssa ssb : Int) (na nb : Nat)
    (result : MergeLoResult κ ν)
    (h : mergeLo? state ssa ssb na nb = some result) :
    MergeComparatorFrame state result.state := by
  unfold mergeLo? at h
  by_cases hguard : 0 < na ∧ 0 < nb ∧ na ≤ PY_SSIZE_T_MAX ∧
      nb ≤ PY_SSIZE_T_MAX ∧ ssa + Int.ofNat na = ssb
  · rw [if_pos hguard] at h
    let allocated := mergeGetmem state (BitVec.ofNat 64 na)
    have hallocated : MergeComparatorFrame state allocated.state := by
      exact mergeGetmem_comparatorFrame state (BitVec.ofNat 64 na)
    by_cases hrejected : allocated.outcome = .guardRejected
    · rw [if_pos hrejected] at h
      injection h with hresult
      subst result
      exact hallocated
    · rw [if_neg hrejected] at h
      rcases Option.bind_eq_some_iff.mp h with
        ⟨copiedState, hcopy, h⟩
      let initial : MergeLoMachine κ ν :=
        { state := copiedState, dest := ssa, aPos := 0, bPos := ssb,
          na := na, nb := nb, minGallop := copiedState.min_gallop }
      rcases Option.bind_eq_some_iff.mp h with
        ⟨machine, hfirst, h⟩
      have hcopyFrame : MergeComparatorFrame allocated.state copiedState :=
        mergeLoMemcpyDataToTemp_comparatorFrame .initialDataToTemp rfl na
          allocated.state copiedState 0 ssa hcopy
      have hfirstFrame : MergeComparatorFrame copiedState machine.state := by
        simpa [initial] using
          (mergeLoCopyBIncr_comparatorFrame initial machine hfirst)
      change
        (if machine.nb = 0 then mergeLoSucceed? machine
          else if machine.na = 1 then mergeLoCopyB? machine
          else mergeLoLoop? (na + nb + 1) machine (.ordinary 0 0)) =
          some result at h
      have hprefix := (hallocated.trans hcopyFrame).trans hfirstFrame
      by_cases hnb : machine.nb = 0
      · rw [if_pos hnb] at h
        exact hprefix.trans
          (mergeLoSucceed_comparatorFrame machine result h)
      · rw [if_neg hnb] at h
        by_cases hna : machine.na = 1
        · rw [if_pos hna] at h
          exact hprefix.trans
            (mergeLoCopyB_comparatorFrame machine result h)
        · rw [if_neg hna] at h
          exact hprefix.trans
            (mergeLoLoop_comparatorFrame_of_eq_some (na + nb + 1) machine
              (.ordinary 0 0) result h)
  · rw [if_neg hguard] at h
    contradiction

/-- A successful `merge_lo` evaluation preserves the comparator stored in the
merge state. -/
theorem mergeLo?_key_compare_of_eq_some
    {state : MergeState (Occurrence alpha) nu} {ssa ssb : Int} {na nb : Nat}
    {result : MergeLoResult (Occurrence alpha) nu}
    (h : mergeLo? state ssa ssb na nb = some result) :
    result.state.key_compare = state.key_compare :=
  (mergeLo_comparatorFrame_of_eq_some state ssa ssb na nb result h).comparator

private theorem mergeHiCopyTempToData_key_compare_of_eq_some
    (state : MergeState κ ν) (dst src : Int) (result : MergeState κ ν)
    (h : mergeHiCopyTempToData? state dst src = some result) :
    result.key_compare = state.key_compare := by
  unfold mergeHiCopyTempToData? at h
  rcases Option.bind_eq_some_iff.mp h with ⟨entry, hread, h⟩
  rcases Option.bind_eq_some_iff.mp h with ⟨data, hwrite, hresult⟩
  injection hresult with hresult
  subst result
  rfl

private theorem mergeHiSucceed_key_compare_of_eq_some
    (cursor : MergeHiCursor κ ν) (result : MergeHiResult κ ν)
    (h : mergeHiSucceed? cursor = some result) :
    result.state.key_compare = cursor.state.key_compare := by
  unfold mergeHiSucceed? at h
  by_cases hzero : cursor.nb = 0
  · simp only [hzero, if_true, bind, Option.bind] at h
    injection h with h
    subst result
    rfl
  · simp only [hzero, if_false] at h
    rcases Option.bind_eq_some_iff.mp h with ⟨state, hcopy, hresult⟩
    injection hresult with hresult
    subst result
    exact mergeHiMemcpyTempToData_key_compare_of_eq_some
      .finalTempToData rfl cursor.nb cursor.state state
      (cursor.dest - Int.ofNat (cursor.nb - 1)) 0 hcopy

private theorem mergeHiCopyA_key_compare_of_eq_some
    (cursor : MergeHiCursor κ ν) (result : MergeHiResult κ ν)
    (h : mergeHiCopyA? cursor = some result) :
    result.state.key_compare = cursor.state.key_compare := by
  unfold mergeHiCopyA? at h
  by_cases hactive : cursor.nb = 1 ∧ 0 < cursor.na
  · simp only [hactive] at h
    rcases Option.bind_eq_some_iff.mp h with ⟨data, hmove, h⟩
    rcases Option.bind_eq_some_iff.mp h with ⟨state, hcopy, hresult⟩
    injection hresult with hresult
    subst result
    have hframe := mergeHiCopyTempToData_key_compare_of_eq_some
      { cursor.state with data := data }
      (cursor.dest - Int.ofNat cursor.na) cursor.ssb state hcopy
    exact hframe
  · simp [hactive] at h

private theorem mergeHiFuelExhausted_key_compare
    (cursor : MergeHiCursor κ ν) :
    (mergeHiFuelExhausted cursor).state.key_compare =
      cursor.state.key_compare := rfl

@[aesop safe forward]
private theorem mergeHiMemcpyDataToTemp_comparatorFrame
    (site : MergeHiMemcpyCallsite)
    (hDirection : site.backings =
      { destination := .temporary, source := .main })
    (count : Nat) (state result : MergeState κ ν) (dst src : Int)
    (h : mergeHiMemcpyDataToTemp? site hDirection count state dst src =
      some result) :
    MergeComparatorFrame state result :=
  ⟨mergeHiMemcpyDataToTemp_key_compare_of_eq_some site hDirection count
    state result dst src h⟩

@[aesop safe forward]
private theorem mergeHiMemcpyTempToData_comparatorFrame
    (site : MergeHiMemcpyCallsite)
    (hDirection : site.backings =
      { destination := .main, source := .temporary })
    (count : Nat) (state result : MergeState κ ν) (dst src : Int)
    (h : mergeHiMemcpyTempToData? site hDirection count state dst src =
      some result) :
    MergeComparatorFrame state result :=
  ⟨mergeHiMemcpyTempToData_key_compare_of_eq_some site hDirection count
    state result dst src h⟩

@[aesop safe forward]
private theorem mergeHiCopyDataDecr_comparatorFrame
    (state : MergeState κ ν) (dst src : Int)
    (result : MergeHiDataCursorResult κ ν)
    (h : mergeHiCopyDataDecr? state dst src = some result) :
    MergeComparatorFrame state result.state :=
  ⟨mergeHiCopyDataDecr_key_compare_of_eq_some state dst src result h⟩

@[aesop safe forward]
private theorem mergeHiCopyTempDecr_comparatorFrame
    (state : MergeState κ ν) (dst src : Int)
    (result : MergeHiDataCursorResult κ ν)
    (h : mergeHiCopyTempDecr? state dst src = some result) :
    MergeComparatorFrame state result.state :=
  ⟨mergeHiCopyTempDecr_key_compare_of_eq_some state dst src result h⟩

@[aesop safe forward]
private theorem mergeHiSucceed_comparatorFrame
    (cursor : MergeHiCursor κ ν) (result : MergeHiResult κ ν)
    (h : mergeHiSucceed? cursor = some result) :
    MergeComparatorFrame cursor.state result.state :=
  ⟨mergeHiSucceed_key_compare_of_eq_some cursor result h⟩

@[aesop safe forward]
private theorem mergeHiCopyA_comparatorFrame
    (cursor : MergeHiCursor κ ν) (result : MergeHiResult κ ν)
    (h : mergeHiCopyA? cursor = some result) :
    MergeComparatorFrame cursor.state result.state :=
  ⟨mergeHiCopyA_key_compare_of_eq_some cursor result h⟩

@[aesop safe forward]
private theorem mergeHiFuelExhausted_comparatorFrame
    (cursor : MergeHiCursor κ ν) :
    MergeComparatorFrame cursor.state (mergeHiFuelExhausted cursor).state :=
  ⟨mergeHiFuelExhausted_key_compare cursor⟩

set_option maxHeartbeats 2000000 in
-- B-side gallop framing composes frames across its nested optional operations.
private theorem mergeHiGallopB_comparatorFrame_of_eq_some
    (afterB : MergeHiCursor κ ν) (aCount : Nat)
    (next : MergeHiCursor κ ν → Option (MergeHiResult κ ν))
    (hnext : ∀ cursor result, next cursor = some result →
      MergeComparatorFrame cursor.state result.state)
    (result : MergeHiResult κ ν)
    (h : mergeHiGallopB? afterB aCount next = some result) :
    MergeComparatorFrame afterB.state result.state := by
  unfold mergeHiGallopB? at h
  rcases Option.bind_eq_some_iff.mp h with ⟨left, hleft, h⟩
  rcases Option.bind_eq_some_iff.mp h with ⟨temp, htemp, h⟩
  change mergeHiBindOptionAcross
    (gallopLeft? afterB.state temp 0 left.key afterB.nb
      (afterB.nb - 1)) _ = some result at h
  cases hgallop : gallopLeft? afterB.state temp 0 left.key afterB.nb
      (afterB.nb - 1) with
  | none => simp [mergeHiBindOptionAcross, hgallop] at h
  | some gallopB =>
      simp only [mergeHiBindOptionAcross, hgallop] at h
      by_cases hfuel : gallopB.fuelExhausted = true
      · simp only [hfuel, if_true, Option.some.injEq] at h
        subst result
        exact mergeHiFuelExhausted_comparatorFrame afterB
      · simp only [hfuel, Bool.false_eq_true, if_false] at h
        have hfinish (movedB : MergeHiCursor κ ν)
            (hmoved : MergeComparatorFrame afterB.state movedB.state)
            (heval :
              (if movedB.nb = 0 ∨ movedB.nb = 1 then next movedB
                else Option.bind
                  (mergeHiCopyDataDecr? movedB.state movedB.dest movedB.ssa)
                  fun copiedA =>
                    let afterA : MergeHiCursor κ ν :=
                      { movedB with
                        state := copiedA.state
                        dest := copiedA.dst
                        ssa := copiedA.src
                        na := movedB.na - 1 }
                    if afterA.na = 0 then next afterA
                    else if mergeHiCountAtLeast aCount MIN_GALLOP ||
                        mergeHiCountAtLeast
                          (afterB.nb - gallopB.index) MIN_GALLOP then
                      next { afterA with
                        phase := MergeHiPhase.galloping aCount
                          (afterB.nb - gallopB.index) }
                    else
                      let minGallop := afterB.minGallop + 1
                      let state :=
                        { afterA.state with min_gallop := minGallop }
                      next
                        { afterA with
                          state := state
                          minGallop := minGallop
                          phase := .straight 0 0 }) =
                some result) :
            MergeComparatorFrame afterB.state result.state := by
          by_cases hsmall : movedB.nb = 0 ∨ movedB.nb = 1
          · rw [if_pos hsmall] at heval
            exact hmoved.trans (hnext movedB result heval)
          · rw [if_neg hsmall] at heval
            rcases Option.bind_eq_some_iff.mp heval with
              ⟨copiedA, hcopyA, heval⟩
            let afterA : MergeHiCursor κ ν :=
              { movedB with
                state := copiedA.state
                dest := copiedA.dst
                ssa := copiedA.src
                na := movedB.na - 1 }
            have hframeA : MergeComparatorFrame movedB.state afterA.state := by
              simpa [afterA] using
                (mergeHiCopyDataDecr_comparatorFrame movedB.state movedB.dest
                  movedB.ssa copiedA hcopyA)
            change
              (if afterA.na = 0 then next afterA
                else if mergeHiCountAtLeast aCount MIN_GALLOP ||
                    mergeHiCountAtLeast
                      (afterB.nb - gallopB.index) MIN_GALLOP then
                  next { afterA with
                    phase := MergeHiPhase.galloping aCount
                      (afterB.nb - gallopB.index) }
                else
                  let minGallop := afterB.minGallop + 1
                  let state := { afterA.state with min_gallop := minGallop }
                  next
                    { afterA with
                      state := state
                      minGallop := minGallop
                      phase := .straight 0 0 }) =
                some result at heval
            by_cases hzeroA : afterA.na = 0
            · rw [if_pos hzeroA] at heval
              exact (hmoved.trans hframeA).trans
                (hnext afterA result heval)
            · rw [if_neg hzeroA] at heval
              by_cases hcontinue :
                  mergeHiCountAtLeast aCount MIN_GALLOP ||
                    mergeHiCountAtLeast
                      (afterB.nb - gallopB.index) MIN_GALLOP
              · rw [if_pos hcontinue] at heval
                let continued : MergeHiCursor κ ν :=
                  { afterA with
                    phase := .galloping aCount
                      (afterB.nb - gallopB.index) }
                change next continued = some result at heval
                exact (hmoved.trans hframeA).trans
                  (hnext continued result heval)
              · rw [if_neg hcontinue] at heval
                let minGallop := afterB.minGallop + 1
                let adjustedState :=
                  { afterA.state with min_gallop := minGallop }
                let adjusted : MergeHiCursor κ ν :=
                  { afterA with
                    state := adjustedState
                    minGallop := minGallop
                    phase := .straight 0 0 }
                have hadjust : MergeComparatorFrame afterA.state
                    adjusted.state := ⟨rfl⟩
                change next adjusted = some result at heval
                exact ((hmoved.trans hframeA).trans hadjust).trans
                  (hnext adjusted result heval)
        by_cases hzero : afterB.nb - gallopB.index = 0
        · simp only [hzero, if_true, bind, Option.bind] at h
          apply hfinish afterB (MergeComparatorFrame.refl afterB.state)
          change
            (if afterB.nb = 0 ∨ afterB.nb = 1 then next afterB
              else Option.bind
                (mergeHiCopyDataDecr? afterB.state afterB.dest afterB.ssa)
                _) = some result at h
          simpa [hzero] using h
        · simp only [hzero, if_false] at h
          rcases Option.bind_eq_some_iff.mp h with ⟨state, hcopy, h⟩
          let movedB : MergeHiCursor κ ν :=
            { afterB with
              state := state
              dest := afterB.dest - Int.ofNat
                (afterB.nb - gallopB.index)
              ssb := afterB.ssb - Int.ofNat
                (afterB.nb - gallopB.index)
              nb := afterB.nb - (afterB.nb - gallopB.index) }
          have hmoved : MergeComparatorFrame afterB.state movedB.state := by
            simpa [movedB] using
              (mergeHiMemcpyTempToData_comparatorFrame .gallopTempToData rfl
                (afterB.nb - gallopB.index) afterB.state state
                (afterB.dest - Int.ofNat
                  (afterB.nb - gallopB.index) + 1)
                (afterB.ssb - Int.ofNat
                  (afterB.nb - gallopB.index) + 1) hcopy)
          apply hfinish movedB hmoved
          simpa [movedB] using h

set_option maxHeartbeats 2000000 in
-- Round framing explores both gallops and their terminal outcomes.
private theorem mergeHiGallopRound_comparatorFrame_of_eq_some
    (cursor : MergeHiCursor κ ν)
    (next : MergeHiCursor κ ν → Option (MergeHiResult κ ν))
    (hnext : ∀ cursor result, next cursor = some result →
      MergeComparatorFrame cursor.state result.state)
    (result : MergeHiResult κ ν)
    (h : mergeHiGallopRound? cursor next = some result) :
    MergeComparatorFrame cursor.state result.state := by
  unfold mergeHiGallopRound? at h
  let minGallop := mergeHiDecreaseMinGallop cursor.minGallop
  let adjustedState := { cursor.state with min_gallop := minGallop }
  have hadjust : MergeComparatorFrame cursor.state adjustedState := ⟨rfl⟩
  change Option.bind (mergeHiTempRead? adjustedState.a cursor.ssb) _ =
    some result at h
  rcases Option.bind_eq_some_iff.mp h with ⟨right, hright, h⟩
  change mergeHiBindOptionAcross
    (gallopRight? adjustedState adjustedState.data cursor.basea right.key
      cursor.na (cursor.na - 1)) _ = some result at h
  cases hgallop : gallopRight? adjustedState adjustedState.data cursor.basea
      right.key cursor.na (cursor.na - 1) with
  | none => simp [mergeHiBindOptionAcross, hgallop] at h
  | some gallopA =>
      simp only [mergeHiBindOptionAcross, hgallop] at h
      by_cases hfuel : gallopA.fuelExhausted = true
      · simp only [hfuel, if_true, Option.some.injEq] at h
        subst result
        exact hadjust.trans
          (mergeHiFuelExhausted_comparatorFrame
            { cursor with state := adjustedState })
      · simp only [hfuel, Bool.false_eq_true, if_false] at h
        have hfinish (movedA : MergeHiCursor κ ν)
            (hmoved : MergeComparatorFrame cursor.state movedA.state)
            (heval :
              (if movedA.na = 0 then next movedA
                else Option.bind
                  (mergeHiCopyTempDecr? movedA.state movedA.dest movedA.ssb)
                  fun copiedB =>
                    let afterB : MergeHiCursor κ ν :=
                      { movedA with
                        state := copiedB.state
                        dest := copiedB.dst
                        ssb := copiedB.src
                        nb := movedA.nb - 1 }
                    if afterB.nb = 1 then next afterB
                    else mergeHiGallopB? afterB
                      (cursor.na - gallopA.index) next) = some result) :
            MergeComparatorFrame cursor.state result.state := by
          by_cases hdone : movedA.na = 0
          · rw [if_pos hdone] at heval
            exact hmoved.trans (hnext movedA result heval)
          · rw [if_neg hdone] at heval
            rcases Option.bind_eq_some_iff.mp heval with
              ⟨copiedB, hcopyB, heval⟩
            let afterB : MergeHiCursor κ ν :=
              { movedA with
                state := copiedB.state
                dest := copiedB.dst
                ssb := copiedB.src
                nb := movedA.nb - 1 }
            have hframeB : MergeComparatorFrame movedA.state afterB.state := by
              simpa [afterB] using
                (mergeHiCopyTempDecr_comparatorFrame movedA.state movedA.dest
                  movedA.ssb copiedB hcopyB)
            change
              (if afterB.nb = 1 then next afterB
                else mergeHiGallopB? afterB
                  (cursor.na - gallopA.index) next) = some result at heval
            by_cases hone : afterB.nb = 1
            · rw [if_pos hone] at heval
              exact (hmoved.trans hframeB).trans
                (hnext afterB result heval)
            · rw [if_neg hone] at heval
              exact (hmoved.trans hframeB).trans
                (mergeHiGallopB_comparatorFrame_of_eq_some afterB
                  (cursor.na - gallopA.index) next hnext result heval)
        by_cases hzero : cursor.na - gallopA.index = 0
        · simp only [hzero, if_true, bind, Option.bind] at h
          let movedA : MergeHiCursor κ ν :=
            { cursor with state := adjustedState, minGallop := minGallop }
          apply hfinish movedA
          · exact hadjust
          · simpa [movedA, adjustedState, minGallop, hzero,
              mergeHiBindOptionAcross, bind, Option.bind] using h
        · simp only [hzero, if_false] at h
          rcases Option.bind_eq_some_iff.mp h with ⟨data, hmove, h⟩
          let movedA : MergeHiCursor κ ν :=
            { cursor with
              state := { adjustedState with data := data }
              dest := cursor.dest - Int.ofNat (cursor.na - gallopA.index)
              ssa := cursor.ssa - Int.ofNat (cursor.na - gallopA.index)
              na := cursor.na - (cursor.na - gallopA.index)
              minGallop := minGallop }
          have hmoved : MergeComparatorFrame cursor.state movedA.state :=
            ⟨rfl⟩
          apply hfinish movedA hmoved
          simpa [movedA] using h

set_option maxHeartbeats 2000000 in
-- Loop framing recursively combines straight-step and gallop-round frames.
@[aesop safe forward]
private theorem mergeHiLoop_comparatorFrame_of_eq_some
    (fuel : Nat) (cursor : MergeHiCursor κ ν)
    (result : MergeHiResult κ ν)
    (h : mergeHiLoop? fuel cursor = some result) :
    MergeComparatorFrame cursor.state result.state := by
  induction fuel generalizing cursor result with
  | zero =>
      simp only [mergeHiLoop?] at h
      by_cases hdone : cursor.na = 0 ∨ cursor.nb = 0
      · rw [if_pos hdone] at h
        exact mergeHiSucceed_comparatorFrame cursor result h
      · rw [if_neg hdone] at h
        by_cases hone : cursor.nb = 1
        · rw [if_pos hone] at h
          exact mergeHiCopyA_comparatorFrame cursor result h
        · rw [if_neg hone] at h
          injection h with hresult
          subst result
          exact mergeHiFuelExhausted_comparatorFrame cursor
  | succ fuel ih =>
      simp only [mergeHiLoop?] at h
      by_cases hdone : cursor.na = 0 ∨ cursor.nb = 0
      · rw [if_pos hdone] at h
        exact mergeHiSucceed_comparatorFrame cursor result h
      · rw [if_neg hdone] at h
        by_cases hone : cursor.nb = 1
        · rw [if_pos hone] at h
          exact mergeHiCopyA_comparatorFrame cursor result h
        · rw [if_neg hone] at h
          cases hphase : cursor.phase with
          | straight aCount bCount =>
              simp only [hphase] at h
              rcases Option.bind_eq_some_iff.mp h with
                ⟨right, hright, h⟩
              rcases Option.bind_eq_some_iff.mp h with
                ⟨left, hleft, h⟩
              by_cases hlt :
                  iflt cursor.state.key_compare right.key left.key = true
              · rw [if_pos hlt] at h
                rcases Option.bind_eq_some_iff.mp h with
                  ⟨copied, hcopy, h⟩
                let nextCursor : MergeHiCursor κ ν :=
                  { cursor with
                    state := copied.state
                    dest := copied.dst
                    ssa := copied.src
                    na := cursor.na - 1
                    phase :=
                      if mergeHiCountAtLeast (aCount + 1)
                          cursor.minGallop then
                        .galloping (aCount + 1) 0
                      else .straight (aCount + 1) 0
                    minGallop :=
                      if mergeHiCountAtLeast (aCount + 1)
                          cursor.minGallop then
                        cursor.minGallop + 1
                      else cursor.minGallop }
                have hframe : MergeComparatorFrame cursor.state
                    nextCursor.state := by
                  simpa [nextCursor] using
                    (mergeHiCopyDataDecr_comparatorFrame cursor.state
                      cursor.dest cursor.ssa copied hcopy)
                change mergeHiLoop? fuel nextCursor = some result at h
                exact hframe.trans (ih nextCursor result h)
              · rw [if_neg hlt] at h
                rcases Option.bind_eq_some_iff.mp h with
                  ⟨copied, hcopy, h⟩
                let nextCursor : MergeHiCursor κ ν :=
                  { cursor with
                    state := copied.state
                    dest := copied.dst
                    ssb := copied.src
                    nb := cursor.nb - 1
                    phase :=
                      if mergeHiCountAtLeast (bCount + 1)
                          cursor.minGallop then
                        .galloping 0 (bCount + 1)
                      else .straight 0 (bCount + 1)
                    minGallop :=
                      if mergeHiCountAtLeast (bCount + 1)
                          cursor.minGallop then
                        cursor.minGallop + 1
                      else cursor.minGallop }
                have hframe : MergeComparatorFrame cursor.state
                    nextCursor.state := by
                  simpa [nextCursor] using
                    (mergeHiCopyTempDecr_comparatorFrame cursor.state
                      cursor.dest cursor.ssb copied hcopy)
                change mergeHiLoop? fuel nextCursor = some result at h
                exact hframe.trans (ih nextCursor result h)
          | galloping aCount bCount =>
              simp only [hphase] at h
              exact mergeHiGallopRound_comparatorFrame_of_eq_some cursor
                (mergeHiLoop? fuel) (fun nextCursor nextResult hnext =>
                  ih nextCursor nextResult hnext) result h

private theorem mergeHi_comparatorFrame_of_eq_some
    (state : MergeState κ ν) (ssa ssb : Int) (na nb : Nat)
    (result : MergeHiResult κ ν)
    (h : mergeHi? state ssa ssb na nb = some result) :
    MergeComparatorFrame state result.state := by
  unfold mergeHi? at h
  by_cases hguard : 0 < na ∧ 0 < nb ∧ na ≤ PY_SSIZE_T_MAX ∧
      nb ≤ PY_SSIZE_T_MAX ∧ ssa + Int.ofNat na = ssb
  · rw [if_pos hguard] at h
    cases hallocated : mergeGetmem state (BitVec.ofNat 64 nb) with
    | mk allocatedState outcome =>
        have hallocatedFrame : MergeComparatorFrame state allocatedState := by
          have hframe := mergeGetmem_comparatorFrame state
            (BitVec.ofNat 64 nb)
          simpa [hallocated] using hframe
        have hbody
            (heval :
              (do
                let copiedState ← mergeHiMemcpyDataToTemp?
                  .initialDataToTemp rfl nb allocatedState 0 ssb
                let copied ← mergeHiCopyDataDecr? copiedState
                  (ssb + Int.ofNat (nb - 1))
                  (ssa + Int.ofNat (na - 1))
                let cursor : MergeHiCursor κ ν :=
                  { state := copied.state
                    dest := copied.dst
                    ssa := copied.src
                    ssb := Int.ofNat (nb - 1)
                    basea := ssa
                    na := na - 1
                    nb := nb
                    minGallop := copied.state.min_gallop
                    phase := .straight 0 0 }
                mergeHiLoop? (na + nb) cursor) = some result) :
              MergeComparatorFrame allocatedState result.state := by
          rcases Option.bind_eq_some_iff.mp heval with
            ⟨copiedState, hcopy, heval⟩
          rcases Option.bind_eq_some_iff.mp heval with
            ⟨copied, hfirst, heval⟩
          let cursor : MergeHiCursor κ ν :=
            { state := copied.state
              dest := copied.dst
              ssa := copied.src
              ssb := Int.ofNat (nb - 1)
              basea := ssa
              na := na - 1
              nb := nb
              minGallop := copied.state.min_gallop
              phase := .straight 0 0 }
          have hcopyFrame : MergeComparatorFrame allocatedState copiedState :=
            mergeHiMemcpyDataToTemp_comparatorFrame .initialDataToTemp rfl nb
              allocatedState copiedState 0 ssb hcopy
          have hfirstFrame : MergeComparatorFrame copiedState cursor.state := by
            simpa [cursor] using
              (mergeHiCopyDataDecr_comparatorFrame copiedState
                (ssb + Int.ofNat (nb - 1))
                (ssa + Int.ofNat (na - 1)) copied hfirst)
          change mergeHiLoop? (na + nb) cursor = some result at heval
          exact (hcopyFrame.trans hfirstFrame).trans
            (mergeHiLoop_comparatorFrame_of_eq_some (na + nb) cursor result
              heval)
        cases outcome with
        | guardRejected =>
            simp only [hallocated] at h
            injection h with hresult
            subst result
            exact hallocatedFrame
        | reused =>
            simp only [hallocated] at h
            exact hallocatedFrame.trans (hbody h)
        | grown =>
            simp only [hallocated] at h
            exact hallocatedFrame.trans (hbody h)
  · rw [if_neg hguard] at h
    contradiction

/-- A successful `merge_hi` evaluation preserves the comparator stored in the
merge state. -/
theorem mergeHi?_key_compare_of_eq_some
    {state : MergeState (Occurrence alpha) nu} {ssa ssb : Int} {na nb : Nat}
    {result : MergeHiResult (Occurrence alpha) nu}
    (h : mergeHi? state ssa ssb na nb = some result) :
    result.state.key_compare = state.key_compare :=
  (mergeHi_comparatorFrame_of_eq_some state ssa ssb na nb result h).comparator

end CPythonListsort
