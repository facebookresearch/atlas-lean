/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Code.Correctness.OccurrenceErasure

/-!
# Occurrence-tag erasure for merge evaluators

The functional-correctness development carries ghost origins in its keys.
This module proves that temporary-storage allocation, galloping, and both
concrete merge engines commute with erasing those origins.
These are evaluator equations only: no ordering or stability law is assumed.
-/

namespace CPythonListsort

universe u v

variable {alpha : Type u} {nu : Type v}

/-! ## `merge_lo` primitives -/

@[simp]
theorem eraseOccurrenceMergeDataMemmove (site : MergeMemmoveCallsite)
    (data : SortSlice (Occurrence alpha) nu) (dst src : Int) (count : Nat) :
    mergeDataMemmove? site (eraseOccurrenceSlice data) dst src count =
      (mergeDataMemmove? site data dst src count).map (eraseOccurrenceSlice) := by
  simp [mergeDataMemmove?]

@[simp]
theorem eraseOccurrenceMergeLoTempRead (storage : TempStorage (Occurrence alpha) nu) (index : Nat) :
    mergeLoTempRead? (eraseOccurrenceTempStorage storage) index =
      (mergeLoTempRead? storage index).map (eraseOccurrenceEntry) := by
  cases hcell : storage.cells[index]? with
  | none => simp [mergeLoTempRead?, eraseOccurrenceTempStorage, hcell]
  | some cell =>
      cases cell <;> simp [mergeLoTempRead?, eraseOccurrenceTempStorage, hcell]

@[simp]
theorem eraseOccurrenceMergeLoTempWrite (storage : TempStorage (Occurrence alpha) nu) (index : Nat)
    (entry : SortSliceEntry (Occurrence alpha) nu) :
    mergeLoTempWrite? (eraseOccurrenceTempStorage storage) index
        (eraseOccurrenceEntry entry) =
      (mergeLoTempWrite? storage index entry).map (eraseOccurrenceTempStorage) := by
  unfold mergeLoTempWrite?
  simp only [eraseOccurrenceTempStorage_cells_size]
  split
  · simp [eraseOccurrenceTempStorage, Array.map_set]
  · rfl

theorem eraseOccurrenceMergeLoMemcpyDataToTemp
    (site : MergeLoMemcpyCallsite)
    (hDirection : site.backings =
      { destination := .temporary, source := .main })
    (count : Nat) (state : MergeState (Occurrence alpha) nu)
    (destination : Nat) (source : Int) :
    mergeLoMemcpyDataToTemp? site hDirection count
        (eraseOccurrenceMergeState state) destination source =
      (mergeLoMemcpyDataToTemp? site hDirection count state destination source).map
        (eraseOccurrenceMergeState) := by
  induction count generalizing state destination source with
  | zero => rfl
  | succ count ih =>
      simp only [mergeLoMemcpyDataToTemp?]
      simp only [eraseOccurrenceMergeState_data, eraseOccurrenceMergeState_tempStorage,
        eraseOccurrenceMergeState_minGallop, eraseOccurrenceMergeState_listlen,
        eraseOccurrenceMergeState_basekeys, eraseOccurrenceMergeState_alloced,
        eraseOccurrenceMergeState_pending, eraseOccurrenceMergeState_key_compare,
        eraseOccurrenceMergeState_mrCurrent, eraseOccurrenceMergeState_mrE,
        eraseOccurrenceMergeState_mrMask]
      rw [eraseOccurrenceSlice_read]
      cases hread : state.data.read? source with
      | none => rfl
      | some entry =>
          simp only [Option.map_some, bind, Option.bind]
          rw [eraseOccurrenceMergeLoTempWrite]
          cases hwrite : mergeLoTempWrite? state.a destination entry with
          | none => rfl
          | some storage =>
              simp only [Option.map_some]
              simpa [eraseOccurrenceMergeState] using
                ih (state := { state with a := storage })
                  (destination := destination + 1) (source := source + 1)

theorem eraseOccurrenceMergeLoMemcpyTempToData
    (site : MergeLoMemcpyCallsite)
    (hDirection : site.backings =
      { destination := .main, source := .temporary })
    (count : Nat) (state : MergeState (Occurrence alpha) nu)
    (destination : Int) (source : Nat) :
    mergeLoMemcpyTempToData? site hDirection count
        (eraseOccurrenceMergeState state) destination source =
      (mergeLoMemcpyTempToData? site hDirection count state destination source).map
        (eraseOccurrenceMergeState) := by
  induction count generalizing state destination source with
  | zero => rfl
  | succ count ih =>
      simp only [mergeLoMemcpyTempToData?]
      simp only [eraseOccurrenceMergeState_data, eraseOccurrenceMergeState_tempStorage,
        eraseOccurrenceMergeState_minGallop, eraseOccurrenceMergeState_listlen,
        eraseOccurrenceMergeState_basekeys, eraseOccurrenceMergeState_alloced,
        eraseOccurrenceMergeState_pending, eraseOccurrenceMergeState_key_compare,
        eraseOccurrenceMergeState_mrCurrent, eraseOccurrenceMergeState_mrE,
        eraseOccurrenceMergeState_mrMask]
      rw [eraseOccurrenceMergeLoTempRead]
      cases hread : mergeLoTempRead? state.a source with
      | none => rfl
      | some entry =>
          simp only [Option.map_some, bind, Option.bind]
          rw [eraseOccurrenceSlice_write]
          cases hwrite : state.data.write? destination entry with
          | none => rfl
          | some data =>
              simp only [Option.map_some]
              simpa [eraseOccurrenceMergeState] using
                ih (state := { state with data := data })
                  (destination := destination + 1) (source := source + 1)

@[simp]
theorem eraseOccurrenceMergeLoInitialDataToTemp (count : Nat)
    (state : MergeState (Occurrence alpha) nu) (destination : Nat)
    (source : Int) :
    mergeLoMemcpyDataToTemp? .initialDataToTemp rfl count
        (eraseOccurrenceMergeState state) destination source =
      (mergeLoMemcpyDataToTemp? .initialDataToTemp rfl count state
        destination source).map (eraseOccurrenceMergeState) := by
  exact eraseOccurrenceMergeLoMemcpyDataToTemp .initialDataToTemp rfl count state
    destination source

@[simp]
theorem eraseOccurrenceMergeLoGallopTempToData (count : Nat)
    (state : MergeState (Occurrence alpha) nu) (destination : Int)
    (source : Nat) :
    mergeLoMemcpyTempToData? .gallopTempToData rfl count
        (eraseOccurrenceMergeState state) destination source =
      (mergeLoMemcpyTempToData? .gallopTempToData rfl count state
        destination source).map (eraseOccurrenceMergeState) := by
  exact eraseOccurrenceMergeLoMemcpyTempToData .gallopTempToData rfl count state
    destination source

@[simp]
theorem eraseOccurrenceMergeLoFinalTempToData (count : Nat)
    (state : MergeState (Occurrence alpha) nu) (destination : Int)
    (source : Nat) :
    mergeLoMemcpyTempToData? .finalTempToData rfl count
        (eraseOccurrenceMergeState state) destination source =
      (mergeLoMemcpyTempToData? .finalTempToData rfl count state
        destination source).map (eraseOccurrenceMergeState) := by
  exact eraseOccurrenceMergeLoMemcpyTempToData .finalTempToData rfl count state
    destination source

theorem occurrenceErasure_mergeLoMemcpyDataToTemp_key_compare_of_eq_some
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

theorem occurrenceErasure_mergeLoMemcpyTempToData_key_compare_of_eq_some
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

theorem eraseOccurrenceMergeLoGatherTempEntries (count : Nat)
    (storage : TempStorage (Occurrence alpha) nu) (source : Nat)
    (entries : Array (SortSliceEntry (Occurrence alpha) nu)) :
    mergeLoGatherTempEntries? count (eraseOccurrenceTempStorage storage) source
        (entries.map (eraseOccurrenceEntry)) =
      (mergeLoGatherTempEntries? count storage source entries).map
        (Array.map (eraseOccurrenceEntry)) := by
  induction count generalizing source entries with
  | zero => rfl
  | succ count ih =>
      simp only [mergeLoGatherTempEntries?]
      rw [eraseOccurrenceMergeLoTempRead]
      cases hread : mergeLoTempRead? storage source with
      | none => rfl
      | some entry =>
          simp only [Option.map_some]
          simpa [Array.map_push] using
            ih (source := source + 1) (entries := entries.push entry)

@[simp]
theorem eraseOccurrenceMergeLoTempRun
    (storage : TempStorage (Occurrence alpha) nu) (source count : Nat) :
    mergeLoTempRun? (eraseOccurrenceTempStorage storage) source count =
      (mergeLoTempRun? storage source count).map (eraseOccurrenceSlice) := by
  unfold mergeLoTempRun?
  have hgather :
      mergeLoGatherTempEntries? count (eraseOccurrenceTempStorage storage) source #[] =
        (mergeLoGatherTempEntries? count storage source #[]).map
          (Array.map (eraseOccurrenceEntry)) := by
    simpa using eraseOccurrenceMergeLoGatherTempEntries count storage source #[]
  rw [hgather]
  cases hentries : mergeLoGatherTempEntries? count storage source #[] with
  | none => rfl
  | some entries => simp [eraseOccurrenceSlice]

/-- Erase the occurrence-bearing state of a forward merge machine. -/
def eraseOccurrenceMergeLoMachine (machine : MergeLoMachine (Occurrence alpha) nu) :
    MergeLoMachine alpha nu :=
  { state := eraseOccurrenceMergeState machine.state
    dest := machine.dest
    aPos := machine.aPos
    bPos := machine.bPos
    na := machine.na
    nb := machine.nb
    minGallop := machine.minGallop }

/-- Erase the occurrence-bearing state of a forward merge result. -/
def eraseOccurrenceMergeLoResult (result : MergeLoResult (Occurrence alpha) nu) :
    MergeLoResult alpha nu :=
  { state := eraseOccurrenceMergeState result.state
    returnCode := result.returnCode
    fuelExhausted := result.fuelExhausted }

@[simp] theorem eraseOccurrenceMergeLoResult_state (result : MergeLoResult (Occurrence alpha) nu) :
    (eraseOccurrenceMergeLoResult result).state =
      eraseOccurrenceMergeState result.state := rfl

@[simp]
theorem eraseOccurrenceMergeLoResult_returnCode
    (result : MergeLoResult (Occurrence alpha) nu) :
    (eraseOccurrenceMergeLoResult result).returnCode = result.returnCode := rfl

@[simp]
theorem eraseOccurrenceMergeLoResult_fuelExhausted
    (result : MergeLoResult (Occurrence alpha) nu) :
    (eraseOccurrenceMergeLoResult result).fuelExhausted = result.fuelExhausted := rfl

@[simp]
theorem eraseOccurrenceMergeLoMachine_state
    (machine : MergeLoMachine (Occurrence alpha) nu) :
    (eraseOccurrenceMergeLoMachine machine).state =
      eraseOccurrenceMergeState machine.state := rfl

@[simp]
theorem eraseOccurrenceMergeLoMachine_dest
    (machine : MergeLoMachine (Occurrence alpha) nu) :
    (eraseOccurrenceMergeLoMachine machine).dest = machine.dest := rfl

@[simp]
theorem eraseOccurrenceMergeLoMachine_aPos
    (machine : MergeLoMachine (Occurrence alpha) nu) :
    (eraseOccurrenceMergeLoMachine machine).aPos = machine.aPos := rfl

@[simp]
theorem eraseOccurrenceMergeLoMachine_bPos
    (machine : MergeLoMachine (Occurrence alpha) nu) :
    (eraseOccurrenceMergeLoMachine machine).bPos = machine.bPos := rfl

@[simp] theorem eraseOccurrenceMergeLoMachine_na (machine : MergeLoMachine (Occurrence alpha) nu) :
    (eraseOccurrenceMergeLoMachine machine).na = machine.na := rfl

@[simp] theorem eraseOccurrenceMergeLoMachine_nb (machine : MergeLoMachine (Occurrence alpha) nu) :
    (eraseOccurrenceMergeLoMachine machine).nb = machine.nb := rfl

@[simp]
theorem eraseOccurrenceMergeLoMachine_minGallop
    (machine : MergeLoMachine (Occurrence alpha) nu) :
    (eraseOccurrenceMergeLoMachine machine).minGallop = machine.minGallop := rfl

@[simp]
theorem eraseOccurrenceMergeLoFailure (state : MergeState (Occurrence alpha) nu) :
    mergeLoFailure (eraseOccurrenceMergeState state) =
      eraseOccurrenceMergeLoResult (mergeLoFailure state) := rfl

@[simp]
theorem eraseOccurrenceMergeLoOutOfFuel (state : MergeState (Occurrence alpha) nu) :
    mergeLoOutOfFuel (eraseOccurrenceMergeState state) =
      eraseOccurrenceMergeLoResult (mergeLoOutOfFuel state) := rfl

@[simp]
theorem eraseOccurrenceMergeLoSuccess (state : MergeState (Occurrence alpha) nu) :
    mergeLoSuccess (eraseOccurrenceMergeState state) =
      eraseOccurrenceMergeLoResult (mergeLoSuccess state) := rfl

@[simp]
theorem eraseOccurrenceMergeLoCopyAIncr (machine : MergeLoMachine (Occurrence alpha) nu) :
    mergeLoCopyAIncr? (eraseOccurrenceMergeLoMachine machine) =
      (mergeLoCopyAIncr? machine).map (eraseOccurrenceMergeLoMachine) := by
  unfold mergeLoCopyAIncr?
  simp only [eraseOccurrenceMergeLoMachine_state, eraseOccurrenceMergeLoMachine_aPos,
    eraseOccurrenceMergeLoMachine_dest, eraseOccurrenceMergeLoMachine_bPos,
    eraseOccurrenceMergeLoMachine_na, eraseOccurrenceMergeLoMachine_nb,
    eraseOccurrenceMergeLoMachine_minGallop, eraseOccurrenceMergeState_tempStorage,
    eraseOccurrenceMergeState_data]
  rw [eraseOccurrenceMergeLoTempRead]
  cases hread : mergeLoTempRead? machine.state.a machine.aPos with
  | none => rfl
  | some entry =>
      simp only [Option.map_some, bind, Option.bind]
      rw [eraseOccurrenceSlice_write]
      cases hwrite : machine.state.data.write? machine.dest entry with
      | none => rfl
      | some data => simp [eraseOccurrenceMergeLoMachine, eraseOccurrenceMergeState]

@[simp]
theorem eraseOccurrenceMergeLoCopyBIncr (machine : MergeLoMachine (Occurrence alpha) nu) :
    mergeLoCopyBIncr? (eraseOccurrenceMergeLoMachine machine) =
      (mergeLoCopyBIncr? machine).map (eraseOccurrenceMergeLoMachine) := by
  unfold mergeLoCopyBIncr?
  simp only [eraseOccurrenceMergeLoMachine_state, eraseOccurrenceMergeLoMachine_aPos,
    eraseOccurrenceMergeLoMachine_dest, eraseOccurrenceMergeLoMachine_bPos,
    eraseOccurrenceMergeLoMachine_na, eraseOccurrenceMergeLoMachine_nb,
    eraseOccurrenceMergeLoMachine_minGallop, eraseOccurrenceMergeState_tempStorage,
    eraseOccurrenceMergeState_data]
  rw [eraseOccurrenceSlice_read]
  cases hread : machine.state.data.read? machine.bPos with
  | none => rfl
  | some entry =>
      simp only [Option.map_some, bind, Option.bind]
      rw [eraseOccurrenceSlice_write]
      cases hwrite : machine.state.data.write? machine.dest entry with
      | none => rfl
      | some data => simp [eraseOccurrenceMergeLoMachine, eraseOccurrenceMergeState]

theorem occurrenceErasure_mergeLoCopyAIncr_key_compare_of_eq_some
    (machine result : MergeLoMachine κ ν)
    (h : mergeLoCopyAIncr? machine = some result) :
    result.state.key_compare = machine.state.key_compare := by
  simp only [mergeLoCopyAIncr?, bind, Option.bind] at h
  split at h <;> simp_all
  split at h <;> simp_all
  subst result
  rfl

theorem occurrenceErasure_mergeLoCopyBIncr_key_compare_of_eq_some
    (machine result : MergeLoMachine κ ν)
    (h : mergeLoCopyBIncr? machine = some result) :
    result.state.key_compare = machine.state.key_compare := by
  simp only [mergeLoCopyBIncr?, bind, Option.bind] at h
  split at h <;> simp_all
  split at h <;> simp_all
  subst result
  rfl

@[simp]
theorem eraseOccurrenceMergeLoSucceed (machine : MergeLoMachine (Occurrence alpha) nu) :
    mergeLoSucceed? (eraseOccurrenceMergeLoMachine machine) =
      (mergeLoSucceed? machine).map (eraseOccurrenceMergeLoResult) := by
  unfold mergeLoSucceed?
  simp only [eraseOccurrenceMergeLoMachine_state, eraseOccurrenceMergeLoMachine_na,
    eraseOccurrenceMergeLoMachine_dest, eraseOccurrenceMergeLoMachine_aPos]
  rw [eraseOccurrenceMergeLoFinalTempToData]
  cases hcopy : mergeLoMemcpyTempToData? .finalTempToData rfl machine.na
      machine.state machine.dest machine.aPos with
  | none => rfl
  | some state => simp

@[simp]
theorem eraseOccurrenceMergeLoCopyB (machine : MergeLoMachine (Occurrence alpha) nu) :
    mergeLoCopyB? (eraseOccurrenceMergeLoMachine machine) =
      (mergeLoCopyB? machine).map (eraseOccurrenceMergeLoResult) := by
  unfold mergeLoCopyB?
  by_cases hactive : machine.na = 1 ∧ 0 < machine.nb <;>
    simp only [eraseOccurrenceMergeLoMachine_state, eraseOccurrenceMergeLoMachine_na,
    eraseOccurrenceMergeLoMachine_nb, eraseOccurrenceMergeLoMachine_dest,
    eraseOccurrenceMergeLoMachine_bPos, eraseOccurrenceMergeLoMachine_aPos,
    eraseOccurrenceMergeState_data, eraseOccurrenceMergeState_tempStorage, hactive]
  · rw [eraseOccurrenceMergeDataMemmove]
    cases hmove : mergeDataMemmove? .loCopyBTail machine.state.data
        machine.dest machine.bPos machine.nb with
    | none => simp
    | some data =>
        simp only [Option.map_some, bind, Option.bind]
        rw [eraseOccurrenceMergeLoTempRead]
        cases hread : mergeLoTempRead? machine.state.a machine.aPos with
        | none => simp
        | some entry =>
            simp only [Option.map_some]
            rw [eraseOccurrenceSlice_write]
            cases hwrite : data.write?
                (machine.dest + Int.ofNat machine.nb) entry with
            | none => simp
            | some finalData =>
                simp [eraseOccurrenceMergeLoResult, eraseOccurrenceMergeState, mergeLoSuccess]
  · rfl

@[simp]
theorem eraseOccurrenceMergeLoGallopFuelFailure (machine : MergeLoMachine (Occurrence alpha) nu) :
    mergeLoGallopFuelFailure (eraseOccurrenceMergeLoMachine machine) =
      (mergeLoGallopFuelFailure machine).map (eraseOccurrenceMergeLoResult) := by
  rfl

set_option maxHeartbeats 2000000 in
-- The gallop-round commutation proof normalizes deeply nested optional branches.
theorem eraseOccurrenceMergeLoGallopRound (lt : BoolComparator alpha)
    (machine : MergeLoMachine (Occurrence alpha) nu)
    (next : MergeLoMachine (Occurrence alpha) nu → Nat → Nat →
      Option (MergeLoResult (Occurrence alpha) nu))
    (next' : MergeLoMachine alpha nu → Nat → Nat →
      Option (MergeLoResult alpha nu))
    (hcompare : machine.state.key_compare = occurrenceComparator lt)
    (hnext : ∀ machine aCount bCount,
      machine.state.key_compare = occurrenceComparator lt →
      next' (eraseOccurrenceMergeLoMachine machine) aCount bCount =
        (next machine aCount bCount).map (eraseOccurrenceMergeLoResult)) :
    mergeLoGallopRound? (eraseOccurrenceMergeLoMachine machine) next' =
      (mergeLoGallopRound? machine next).map (eraseOccurrenceMergeLoResult) := by
  unfold mergeLoGallopRound?
  simp only [eraseOccurrenceMergeLoMachine_na, eraseOccurrenceMergeLoMachine_nb,
    eraseOccurrenceMergeLoMachine_state, eraseOccurrenceMergeLoMachine_dest,
    eraseOccurrenceMergeLoMachine_aPos, eraseOccurrenceMergeLoMachine_bPos,
    eraseOccurrenceMergeLoMachine_minGallop]
  by_cases hactive : machine.na ≤ 1 ∨ machine.nb = 0 <;>
    simp only [hactive, if_pos, if_false, Option.map_none]
  rw [eraseOccurrenceMergeState_data, eraseOccurrenceSlice_read]
  cases hfirstB : machine.state.data.read? machine.bPos with
  | none => rfl
  | some firstB =>
      simp only [Option.map_some, bind, Option.bind]
      rw [eraseOccurrenceMergeState_tempStorage, eraseOccurrenceMergeLoTempRun]
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
                (gallopRight? (eraseOccurrenceMergeState adjustedState)
                  (eraseOccurrenceSlice activeA) 0
                  firstB.key.value machine.na 0) _ =
              Option.map (eraseOccurrenceMergeLoResult)
                (mergeLoBindOptionAcross
                  (gallopRight? adjustedState activeA 0 firstB.key
                    machine.na 0) _)
          rw [eraseOccurrenceGallopRight lt adjustedState activeA 0 firstB.key
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
                      (eraseOccurrenceMergeLoMachine adjustedMachine)
                  else _) =
                  Option.map (eraseOccurrenceMergeLoResult)
                    (if gallopA.fuelExhausted then
                        mergeLoGallopFuelFailure adjustedMachine
                      else _)
              by_cases hfuel : gallopA.fuelExhausted = true
              · simp only [hfuel, if_true]
                exact eraseOccurrenceMergeLoGallopFuelFailure adjustedMachine
              · simp only [hfuel, Bool.false_eq_true, if_false]
                by_cases hindex : gallopA.index > machine.na
                · simp only [hindex, if_true, Option.map_none]
                · simp only [hindex, if_false]
                  change
                    Option.bind
                        (mergeLoMemcpyTempToData? .gallopTempToData rfl
                          gallopA.index (eraseOccurrenceMergeState adjustedState)
                          machine.dest machine.aPos) _ =
                      Option.map (eraseOccurrenceMergeLoResult)
                        (Option.bind
                          (mergeLoMemcpyTempToData? .gallopTempToData rfl
                            gallopA.index adjustedState machine.dest machine.aPos)
                          _)
                  rw [eraseOccurrenceMergeLoGallopTempToData]
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
                              (eraseOccurrenceMergeLoMachine afterA)
                          else if afterA.na = 1 then
                            mergeLoCopyB? (eraseOccurrenceMergeLoMachine afterA)
                          else
                            Option.bind
                              (mergeLoCopyBIncr?
                                (eraseOccurrenceMergeLoMachine afterA)) _) =
                          Option.map (eraseOccurrenceMergeLoResult)
                            (if afterA.na = 0 then mergeLoSucceed? afterA
                              else if afterA.na = 1 then mergeLoCopyB? afterA
                              else Option.bind (mergeLoCopyBIncr? afterA) _)
                      split
                      · exact eraseOccurrenceMergeLoSucceed afterA
                      · split
                        · exact eraseOccurrenceMergeLoCopyB afterA
                        · rw [eraseOccurrenceMergeLoCopyBIncr]
                          cases hcopyB : mergeLoCopyBIncr? afterA with
                          | none => rfl
                          | some afterB =>
                              simp only [Option.map_some, Option.bind_some]
                              change
                                (if afterB.nb = 0 then
                                    mergeLoSucceed?
                                      (eraseOccurrenceMergeLoMachine afterB)
                                  else _) =
                                  Option.map (eraseOccurrenceMergeLoResult)
                                    (if afterB.nb = 0 then
                                        mergeLoSucceed? afterB
                                      else _)
                              by_cases hnb : afterB.nb = 0
                              · simp only [hnb, if_true]
                                exact eraseOccurrenceMergeLoSucceed afterB
                              · simp only [hnb, if_false]
                                change
                                  Option.bind
                                      (mergeLoTempRead?
                                        (eraseOccurrenceTempStorage afterB.state.a)
                                        afterB.aPos) _ =
                                    Option.map (eraseOccurrenceMergeLoResult)
                                      (Option.bind
                                        (mergeLoTempRead? afterB.state.a
                                          afterB.aPos) _)
                                rw [eraseOccurrenceMergeLoTempRead]
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
                                          occurrenceErasure_mergeLoCopyBIncr_key_compare_of_eq_some
                                            afterA afterB hcopyB
                                        _ = state.key_compare := rfl
                                        _ = adjustedState.key_compare :=
                                    occurrenceErasure_mergeLoMemcpyTempToData_key_compare_of_eq_some
                                            .gallopTempToData rfl gallopA.index
                                            adjustedState state machine.dest
                                            machine.aPos hcopyA
                                        _ = occurrenceComparator lt := hcompare'
                                    change
                                      mergeLoBindOptionAcross
                                          (gallopLeft?
                                            (eraseOccurrenceMergeState afterB.state)
                                            (eraseOccurrenceSlice
                                              afterB.state.data)
                                            afterB.bPos
                                            firstA.key.value
                                            afterB.nb 0) _ =
                                        Option.map (eraseOccurrenceMergeLoResult)
                                          (mergeLoBindOptionAcross
                                            (gallopLeft? afterB.state
                                              afterB.state.data afterB.bPos
                                              firstA.key afterB.nb 0) _)
                                    rw [eraseOccurrenceGallopLeft lt afterB.state
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
                                                (eraseOccurrenceMergeLoMachine afterB)
                                            else if gallopB.index > afterB.nb then
                                              none
                                            else _) =
                                            Option.map (eraseOccurrenceMergeLoResult)
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
                                              eraseOccurrenceMergeLoGallopFuelFailure afterB
                                          | skip
                                        by_cases hindexB : gallopB.index > afterB.nb <;>
                                          simp only [hindexB, if_true, if_false,
                                            Option.map_none]
                                        change
                                          Option.bind
                                              (mergeDataMemmove? .loGallopB
                                                (eraseOccurrenceSlice
                                                  afterB.state.data)
                                                afterB.dest afterB.bPos
                                                gallopB.index) _ =
                                            Option.map (eraseOccurrenceMergeLoResult)
                                              (Option.bind
                                                (mergeDataMemmove? .loGallopB
                                                  afterB.state.data afterB.dest
                                                  afterB.bPos gallopB.index) _)
                                        rw [eraseOccurrenceMergeDataMemmove]
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
                                                    (eraseOccurrenceMergeLoMachine
                                                      movedB)
                                                else
                                                  Option.bind
                                                    (mergeLoCopyAIncr?
                                                      (eraseOccurrenceMergeLoMachine
                                                        movedB)) _) =
                                                Option.map
                                                  (eraseOccurrenceMergeLoResult)
                                                  (if movedB.nb = 0 then
                                                      mergeLoSucceed? movedB
                                                    else
                                                      Option.bind
                                                        (mergeLoCopyAIncr? movedB)
                                                        _)
                                            split
                                            · exact
                                                eraseOccurrenceMergeLoSucceed movedB
                                            · rw [eraseOccurrenceMergeLoCopyAIncr]
                                              cases hcopyAOne :
                                                  mergeLoCopyAIncr? movedB with
                                              | none => rfl
                                              | some afterA =>
                                                  simp only [Option.map_some,
                                                    Option.bind_some]
                                                  change
                                                    (if afterA.na = 1 then
                                                        mergeLoCopyB?
                                                          (eraseOccurrenceMergeLoMachine afterA)
                                                      else next'
                                                        (eraseOccurrenceMergeLoMachine afterA)
                                                        gallopA.index
                                                        gallopB.index) =
                                                      Option.map
                                                        (eraseOccurrenceMergeLoResult)
                                                        (if afterA.na = 1 then
                                                            mergeLoCopyB? afterA
                                                          else next afterA
                                                            gallopA.index
                                                            gallopB.index)
                                                  split
                                                  · exact
                                                      eraseOccurrenceMergeLoCopyB
                                                        afterA
                                                  · apply hnext afterA
                                                      gallopA.index gallopB.index
                                                    calc
                                                      afterA.state.key_compare =
                                                          movedB.state.key_compare :=
                                        occurrenceErasure_mergeLoCopyAIncr_key_compare_of_eq_some
                                                          movedB afterA hcopyAOne
                                                      _ = afterB.state.key_compare :=
                                                        rfl
                                                      _ = occurrenceComparator lt :=
                                                        hafterCompare

set_option maxHeartbeats 2000000 in
-- Induction through the merge loop expands both ordinary and galloping phases.
theorem eraseOccurrenceMergeLoLoop (lt : BoolComparator alpha) (fuel : Nat)
    (machine : MergeLoMachine (Occurrence alpha) nu) (phase : MergeLoPhase)
    (hcompare : machine.state.key_compare = occurrenceComparator lt) :
    mergeLoLoop? fuel (eraseOccurrenceMergeLoMachine machine) phase =
      (mergeLoLoop? fuel machine phase).map (eraseOccurrenceMergeLoResult) := by
  induction fuel generalizing machine phase with
  | zero => simp [mergeLoLoop?, eraseOccurrenceMergeLoResult]
  | succ fuel ih =>
      cases phase with
      | ordinary aCount bCount =>
          simp only [mergeLoLoop?]
          simp only [eraseOccurrenceMergeLoMachine_na, eraseOccurrenceMergeLoMachine_nb,
            eraseOccurrenceMergeLoMachine_state, eraseOccurrenceMergeLoMachine_aPos,
            eraseOccurrenceMergeLoMachine_bPos]
          by_cases hactive : machine.na ≤ 1 ∨ machine.nb = 0 <;>
            simp only [hactive, if_pos, if_false, Option.map_none]
          rw [eraseOccurrenceMergeState_tempStorage, eraseOccurrenceMergeLoTempRead]
          cases hfirstA : mergeLoTempRead? machine.state.a machine.aPos with
          | none => rfl
          | some firstA =>
              simp only [Option.map_some, bind, Option.bind]
              rw [eraseOccurrenceMergeState_data, eraseOccurrenceSlice_read]
              cases hfirstB : machine.state.data.read? machine.bPos with
              | none => rfl
              | some firstB =>
                  simp only [Option.map_some]
                  simp only [eraseOccurrenceMergeState_key_compare, hcompare,
                    eraseOccurrenceComparator_occurrenceComparator,
                    eraseOccurrenceEntry_key,
                    iflt_eraseOccurrence]
                  split
                  · rw [eraseOccurrenceMergeLoCopyBIncr]
                    cases hcopy : mergeLoCopyBIncr? machine with
                    | none => rfl
                    | some next =>
                        simp only [Option.map_some]
                        have hnextCompare : next.state.key_compare =
                            occurrenceComparator lt :=
                          (occurrenceErasure_mergeLoCopyBIncr_key_compare_of_eq_some
                            machine next hcopy).trans hcompare
                        let raised : MergeLoMachine (Occurrence alpha) nu :=
                          { next with minGallop := next.minGallop + 1 }
                        simp only [eraseOccurrenceMergeLoMachine_nb,
                          eraseOccurrenceMergeLoMachine_na,
                          eraseOccurrenceMergeLoMachine_minGallop]
                        change
                          (if next.nb = 0 then
                              mergeLoSucceed?
                                (eraseOccurrenceMergeLoMachine next)
                            else if mergeLoCountAtLeastWord (bCount + 1)
                                next.minGallop then
                              mergeLoLoop? fuel
                                (eraseOccurrenceMergeLoMachine raised) .galloping
                            else
                              mergeLoLoop? fuel
                                (eraseOccurrenceMergeLoMachine next)
                                (.ordinary 0 (bCount + 1))) =
                            Option.map (eraseOccurrenceMergeLoResult)
                              (if next.nb = 0 then mergeLoSucceed? next
                                else if mergeLoCountAtLeastWord (bCount + 1)
                                    next.minGallop then
                                  mergeLoLoop? fuel raised .galloping
                                else
                                  mergeLoLoop? fuel next
                                    (.ordinary 0 (bCount + 1)))
                        split
                        · exact eraseOccurrenceMergeLoSucceed next
                        · split
                          · apply ih raised .galloping
                            simpa [raised] using hnextCompare
                          · exact ih next (.ordinary 0 (bCount + 1))
                              hnextCompare
                  · rw [eraseOccurrenceMergeLoCopyAIncr]
                    cases hcopy : mergeLoCopyAIncr? machine with
                    | none => rfl
                    | some next =>
                        simp only [Option.map_some]
                        have hnextCompare : next.state.key_compare =
                            occurrenceComparator lt :=
                          (occurrenceErasure_mergeLoCopyAIncr_key_compare_of_eq_some
                            machine next hcopy).trans hcompare
                        let raised : MergeLoMachine (Occurrence alpha) nu :=
                          { next with minGallop := next.minGallop + 1 }
                        simp only [eraseOccurrenceMergeLoMachine_nb,
                          eraseOccurrenceMergeLoMachine_na,
                          eraseOccurrenceMergeLoMachine_minGallop]
                        change
                          (if next.na = 1 then
                              mergeLoCopyB?
                                (eraseOccurrenceMergeLoMachine next)
                            else if mergeLoCountAtLeastWord (aCount + 1)
                                next.minGallop then
                              mergeLoLoop? fuel
                                (eraseOccurrenceMergeLoMachine raised) .galloping
                            else
                              mergeLoLoop? fuel
                                (eraseOccurrenceMergeLoMachine next)
                                (.ordinary (aCount + 1) 0)) =
                            Option.map (eraseOccurrenceMergeLoResult)
                              (if next.na = 1 then mergeLoCopyB? next
                                else if mergeLoCountAtLeastWord (aCount + 1)
                                    next.minGallop then
                                  mergeLoLoop? fuel raised .galloping
                                else
                                  mergeLoLoop? fuel next
                                    (.ordinary (aCount + 1) 0))
                        split
                        · exact eraseOccurrenceMergeLoCopyB next
                        · split
                          · apply ih raised .galloping
                            simpa [raised] using hnextCompare
                          · exact ih next (.ordinary (aCount + 1) 0)
                              hnextCompare
      | galloping =>
          apply eraseOccurrenceMergeLoGallopRound lt machine _ _ hcompare
          intro next aCount bCount hnextCompare
          split
          · exact ih next .galloping hnextCompare
          · let minGallop := next.minGallop + 1
            let adjustedState := { next.state with min_gallop := minGallop }
            let adjusted : MergeLoMachine (Occurrence alpha) nu :=
              { next with state := adjustedState, minGallop := minGallop }
            change
              mergeLoLoop? fuel (eraseOccurrenceMergeLoMachine adjusted)
                  (.ordinary 0 0) =
                Option.map (eraseOccurrenceMergeLoResult)
                  (mergeLoLoop? fuel adjusted (.ordinary 0 0))
            apply ih adjusted (.ordinary 0 0)
            simpa [adjusted, adjustedState] using hnextCompare

@[simp]
theorem eraseOccurrenceMergeLo (lt : BoolComparator alpha)
    (state : MergeState (Occurrence alpha) nu) (ssa ssb : Int) (na nb : Nat)
    (hcompare : state.key_compare = occurrenceComparator lt) :
    mergeLo? (eraseOccurrenceMergeState state) ssa ssb na nb =
      (mergeLo? state ssa ssb na nb).map (eraseOccurrenceMergeLoResult) := by
  unfold mergeLo?
  split <;> try rfl
  rw [eraseOccurrenceMergeGetmem]
  cases hallocated : mergeGetmem state (BitVec.ofNat 64 na) with
  | mk allocatedState outcome =>
      cases outcome with
      | guardRejected => simp
      | reused =>
          simp only [eraseOccurrenceMergeGetmemResult]
          simp only [reduceCtorEq, if_false]
          rw [eraseOccurrenceMergeLoInitialDataToTemp]
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
                    (eraseOccurrenceMergeLoMachine initial)) _ =
                  Option.map (eraseOccurrenceMergeLoResult)
                    (Option.bind (mergeLoCopyBIncr? initial) _)
              rw [eraseOccurrenceMergeLoCopyBIncr]
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
                        occurrenceErasure_mergeLoCopyBIncr_key_compare_of_eq_some initial machine
                          hfirst
                      _ = copiedState.key_compare := rfl
                      _ = allocatedState.key_compare :=
                        occurrenceErasure_mergeLoMemcpyDataToTemp_key_compare_of_eq_some
                          .initialDataToTemp rfl na allocatedState copiedState 0
                          ssa hcopy
                      _ = state.key_compare := hallocatedCompare
                      _ = occurrenceComparator lt := hcompare
                  change
                    (if machine.nb = 0 then
                        mergeLoSucceed? (eraseOccurrenceMergeLoMachine machine)
                      else if machine.na = 1 then
                        mergeLoCopyB? (eraseOccurrenceMergeLoMachine machine)
                      else
                        mergeLoLoop? (na + nb + 1)
                          (eraseOccurrenceMergeLoMachine machine)
                          (.ordinary 0 0)) =
                      Option.map (eraseOccurrenceMergeLoResult)
                        (if machine.nb = 0 then mergeLoSucceed? machine
                          else if machine.na = 1 then mergeLoCopyB? machine
                          else mergeLoLoop? (na + nb + 1) machine
                            (.ordinary 0 0))
                  split
                  · exact eraseOccurrenceMergeLoSucceed machine
                  · split
                    · exact eraseOccurrenceMergeLoCopyB machine
                    · exact eraseOccurrenceMergeLoLoop lt (na + nb + 1) machine
                        (.ordinary 0 0) hmachineCompare
      | grown =>
          simp only [eraseOccurrenceMergeGetmemResult]
          simp only [reduceCtorEq, if_false]
          rw [eraseOccurrenceMergeLoInitialDataToTemp]
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
                    (eraseOccurrenceMergeLoMachine initial)) _ =
                  Option.map (eraseOccurrenceMergeLoResult)
                    (Option.bind (mergeLoCopyBIncr? initial) _)
              rw [eraseOccurrenceMergeLoCopyBIncr]
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
                        occurrenceErasure_mergeLoCopyBIncr_key_compare_of_eq_some initial machine
                          hfirst
                      _ = copiedState.key_compare := rfl
                      _ = allocatedState.key_compare :=
                        occurrenceErasure_mergeLoMemcpyDataToTemp_key_compare_of_eq_some
                          .initialDataToTemp rfl na allocatedState copiedState 0
                          ssa hcopy
                      _ = state.key_compare := hallocatedCompare
                      _ = occurrenceComparator lt := hcompare
                  change
                    (if machine.nb = 0 then
                        mergeLoSucceed? (eraseOccurrenceMergeLoMachine machine)
                      else if machine.na = 1 then
                        mergeLoCopyB? (eraseOccurrenceMergeLoMachine machine)
                      else
                        mergeLoLoop? (na + nb + 1)
                          (eraseOccurrenceMergeLoMachine machine)
                          (.ordinary 0 0)) =
                      Option.map (eraseOccurrenceMergeLoResult)
                        (if machine.nb = 0 then mergeLoSucceed? machine
                          else if machine.na = 1 then mergeLoCopyB? machine
                          else mergeLoLoop? (na + nb + 1) machine
                            (.ordinary 0 0))
                  split
                  · exact eraseOccurrenceMergeLoSucceed machine
                  · split
                    · exact eraseOccurrenceMergeLoCopyB machine
                    · exact eraseOccurrenceMergeLoLoop lt (na + nb + 1) machine
                        (.ordinary 0 0) hmachineCompare

/-! ## `merge_hi` primitives -/

@[simp]
theorem eraseOccurrenceMergeHiTempRead (storage : TempStorage (Occurrence alpha) nu) (index : Int) :
    mergeHiTempRead? (eraseOccurrenceTempStorage storage) index =
      (mergeHiTempRead? storage index).map (eraseOccurrenceEntry) := by
  unfold mergeHiTempRead?
  by_cases hnonnegative : 0 ≤ index
  · simp only [hnonnegative, if_true]
    cases hcell : storage.cells[index.toNat]? with
    | none => simp [eraseOccurrenceTempStorage, hcell]
    | some cell => cases cell <;> simp [eraseOccurrenceTempStorage, hcell]
  · simp [hnonnegative]

@[simp]
theorem eraseOccurrenceMergeHiTempWrite (storage : TempStorage (Occurrence alpha) nu) (index : Int)
    (entry : SortSliceEntry (Occurrence alpha) nu) :
    mergeHiTempWrite? (eraseOccurrenceTempStorage storage) index
        (eraseOccurrenceEntry entry) =
      (mergeHiTempWrite? storage index entry).map (eraseOccurrenceTempStorage) := by
  unfold mergeHiTempWrite?
  split <;> try rfl
  simp only [eraseOccurrenceTempStorage_cells_size]
  split
  · simp [eraseOccurrenceTempStorage, Array.map_set]
  · rfl

@[simp]
theorem eraseOccurrenceMergeHiCopyDataToTemp
    (state : MergeState (Occurrence alpha) nu) (dst src : Int) :
    mergeHiCopyDataToTemp? (eraseOccurrenceMergeState state) dst src =
      (mergeHiCopyDataToTemp? state dst src).map (eraseOccurrenceMergeState) := by
  unfold mergeHiCopyDataToTemp?
  simp only [eraseOccurrenceMergeState_data, eraseOccurrenceMergeState_tempStorage,
    eraseOccurrenceMergeState_minGallop, eraseOccurrenceMergeState_listlen,
    eraseOccurrenceMergeState_basekeys, eraseOccurrenceMergeState_alloced,
    eraseOccurrenceMergeState_pending, eraseOccurrenceMergeState_key_compare,
    eraseOccurrenceMergeState_mrCurrent, eraseOccurrenceMergeState_mrE,
    eraseOccurrenceMergeState_mrMask]
  rw [eraseOccurrenceSlice_read]
  cases hread : state.data.read? src with
  | none => rfl
  | some entry =>
      simp only [Option.map_some, bind, Option.bind]
      rw [eraseOccurrenceMergeHiTempWrite]
      cases hwrite : mergeHiTempWrite? state.a dst entry with
      | none => rfl
      | some storage => simp [eraseOccurrenceMergeState]

@[simp]
theorem eraseOccurrenceMergeHiCopyTempToData
    (state : MergeState (Occurrence alpha) nu) (dst src : Int) :
    mergeHiCopyTempToData? (eraseOccurrenceMergeState state) dst src =
      (mergeHiCopyTempToData? state dst src).map (eraseOccurrenceMergeState) := by
  unfold mergeHiCopyTempToData?
  simp only [eraseOccurrenceMergeState_data, eraseOccurrenceMergeState_tempStorage,
    eraseOccurrenceMergeState_minGallop, eraseOccurrenceMergeState_listlen,
    eraseOccurrenceMergeState_basekeys, eraseOccurrenceMergeState_alloced,
    eraseOccurrenceMergeState_pending, eraseOccurrenceMergeState_key_compare,
    eraseOccurrenceMergeState_mrCurrent, eraseOccurrenceMergeState_mrE,
    eraseOccurrenceMergeState_mrMask]
  rw [eraseOccurrenceMergeHiTempRead]
  cases hread : mergeHiTempRead? state.a src with
  | none => rfl
  | some entry =>
      simp only [Option.map_some, bind, Option.bind]
      rw [eraseOccurrenceSlice_write]
      cases hwrite : state.data.write? dst entry with
      | none => rfl
      | some data => simp [eraseOccurrenceMergeState]

theorem eraseOccurrenceMergeHiMemcpyDataToTemp
    (site : MergeHiMemcpyCallsite)
    (hDirection : site.backings =
      { destination := .temporary, source := .main })
    (count : Nat) (state : MergeState (Occurrence alpha) nu)
    (dst src : Int) :
    mergeHiMemcpyDataToTemp? site hDirection count
        (eraseOccurrenceMergeState state) dst src =
      (mergeHiMemcpyDataToTemp? site hDirection count state dst src).map
        (eraseOccurrenceMergeState) := by
  induction count generalizing state dst src with
  | zero => rfl
  | succ count ih =>
      simp only [mergeHiMemcpyDataToTemp?]
      rw [eraseOccurrenceMergeHiCopyDataToTemp]
      cases hcopy : mergeHiCopyDataToTemp? state dst src with
      | none => rfl
      | some state =>
          simp only [Option.map_some]
          exact ih (state := state) (dst := dst + 1) (src := src + 1)

theorem eraseOccurrenceMergeHiMemcpyTempToData
    (site : MergeHiMemcpyCallsite)
    (hDirection : site.backings =
      { destination := .main, source := .temporary })
    (count : Nat) (state : MergeState (Occurrence alpha) nu)
    (dst src : Int) :
    mergeHiMemcpyTempToData? site hDirection count
        (eraseOccurrenceMergeState state) dst src =
      (mergeHiMemcpyTempToData? site hDirection count state dst src).map
        (eraseOccurrenceMergeState) := by
  induction count generalizing state dst src with
  | zero => rfl
  | succ count ih =>
      simp only [mergeHiMemcpyTempToData?]
      rw [eraseOccurrenceMergeHiCopyTempToData]
      cases hcopy : mergeHiCopyTempToData? state dst src with
      | none => rfl
      | some state =>
          simp only [Option.map_some]
          exact ih (state := state) (dst := dst + 1) (src := src + 1)

@[simp]
theorem eraseOccurrenceMergeHiInitialDataToTemp (count : Nat)
    (state : MergeState (Occurrence alpha) nu) (dst src : Int) :
    mergeHiMemcpyDataToTemp? .initialDataToTemp rfl count
        (eraseOccurrenceMergeState state) dst src =
      (mergeHiMemcpyDataToTemp? .initialDataToTemp rfl count state dst src).map
        (eraseOccurrenceMergeState) := by
  exact eraseOccurrenceMergeHiMemcpyDataToTemp .initialDataToTemp rfl count state
    dst src

@[simp]
theorem eraseOccurrenceMergeHiGallopTempToData (count : Nat)
    (state : MergeState (Occurrence alpha) nu) (dst src : Int) :
    mergeHiMemcpyTempToData? .gallopTempToData rfl count
        (eraseOccurrenceMergeState state) dst src =
      (mergeHiMemcpyTempToData? .gallopTempToData rfl count state dst src).map
        (eraseOccurrenceMergeState) := by
  exact eraseOccurrenceMergeHiMemcpyTempToData .gallopTempToData rfl count state
    dst src

@[simp]
theorem eraseOccurrenceMergeHiFinalTempToData (count : Nat)
    (state : MergeState (Occurrence alpha) nu) (dst src : Int) :
    mergeHiMemcpyTempToData? .finalTempToData rfl count
        (eraseOccurrenceMergeState state) dst src =
      (mergeHiMemcpyTempToData? .finalTempToData rfl count state dst src).map
        (eraseOccurrenceMergeState) := by
  exact eraseOccurrenceMergeHiMemcpyTempToData .finalTempToData rfl count state
    dst src

theorem eraseOccurrenceMergeHiInitializedTempPrefixLoop (count : Nat)
    (storage : TempStorage (Occurrence alpha) nu) (source : Nat)
    (entries : Array (SortSliceEntry (Occurrence alpha) nu)) :
    mergeHiInitializedTempPrefixLoop? count (eraseOccurrenceTempStorage storage)
        source (entries.map (eraseOccurrenceEntry)) =
      (mergeHiInitializedTempPrefixLoop? count storage source entries).map
        (Array.map (eraseOccurrenceEntry)) := by
  induction count generalizing source entries with
  | zero => rfl
  | succ count ih =>
      simp only [mergeHiInitializedTempPrefixLoop?]
      rw [eraseOccurrenceMergeHiTempRead]
      cases hread : mergeHiTempRead? storage (Int.ofNat source) with
      | none => rfl
      | some entry =>
          simp only [Option.map_some]
          simpa [Array.map_push] using
            ih (source := source + 1) (entries := entries.push entry)

@[simp]
theorem eraseOccurrenceInitializedTempPrefix
    (storage : TempStorage (Occurrence alpha) nu) (count : Nat) :
    initializedTempPrefix? (eraseOccurrenceTempStorage storage) count =
      (initializedTempPrefix? storage count).map (eraseOccurrenceSlice) := by
  unfold initializedTempPrefix?
  have hloop :
      mergeHiInitializedTempPrefixLoop? count
          (eraseOccurrenceTempStorage storage) 0 #[] =
        (mergeHiInitializedTempPrefixLoop? count storage 0 #[]).map
          (Array.map (eraseOccurrenceEntry)) := by
    simpa using
      eraseOccurrenceMergeHiInitializedTempPrefixLoop count storage 0 #[]
  rw [hloop]
  cases hentries : mergeHiInitializedTempPrefixLoop? count storage 0 #[] with
  | none => rfl
  | some entries => simp [eraseOccurrenceSlice]

/-- Erase the state carried by one backward-copy cursor result. -/
def eraseOccurrenceMergeHiDataCursorResult
    (result : MergeHiDataCursorResult (Occurrence alpha) nu) :
    MergeHiDataCursorResult alpha nu :=
  { state := eraseOccurrenceMergeState result.state
    dst := result.dst
    src := result.src }

/-- Erase the state carried by a backward merge result. -/
def eraseOccurrenceMergeHiResult (result : MergeHiResult (Occurrence alpha) nu) :
    MergeHiResult alpha nu :=
  { state := eraseOccurrenceMergeState result.state
    returnCode := result.returnCode
    fuelExhausted := result.fuelExhausted }

/-- Erase the state carried by a backward merge cursor. -/
def eraseOccurrenceMergeHiCursor (cursor : MergeHiCursor (Occurrence alpha) nu) :
    MergeHiCursor alpha nu :=
  { state := eraseOccurrenceMergeState cursor.state
    dest := cursor.dest
    ssa := cursor.ssa
    ssb := cursor.ssb
    basea := cursor.basea
    na := cursor.na
    nb := cursor.nb
    minGallop := cursor.minGallop
    phase := cursor.phase }

@[simp] theorem eraseOccurrenceMergeHiCursor_state (cursor : MergeHiCursor (Occurrence alpha) nu) :
    (eraseOccurrenceMergeHiCursor cursor).state =
      eraseOccurrenceMergeState cursor.state := rfl

@[simp] theorem eraseOccurrenceMergeHiCursor_dest (cursor : MergeHiCursor (Occurrence alpha) nu) :
    (eraseOccurrenceMergeHiCursor cursor).dest = cursor.dest := rfl

@[simp] theorem eraseOccurrenceMergeHiCursor_ssa (cursor : MergeHiCursor (Occurrence alpha) nu) :
    (eraseOccurrenceMergeHiCursor cursor).ssa = cursor.ssa := rfl

@[simp] theorem eraseOccurrenceMergeHiCursor_ssb (cursor : MergeHiCursor (Occurrence alpha) nu) :
    (eraseOccurrenceMergeHiCursor cursor).ssb = cursor.ssb := rfl

@[simp] theorem eraseOccurrenceMergeHiCursor_basea (cursor : MergeHiCursor (Occurrence alpha) nu) :
    (eraseOccurrenceMergeHiCursor cursor).basea = cursor.basea := rfl

@[simp] theorem eraseOccurrenceMergeHiCursor_na (cursor : MergeHiCursor (Occurrence alpha) nu) :
    (eraseOccurrenceMergeHiCursor cursor).na = cursor.na := rfl

@[simp] theorem eraseOccurrenceMergeHiCursor_nb (cursor : MergeHiCursor (Occurrence alpha) nu) :
    (eraseOccurrenceMergeHiCursor cursor).nb = cursor.nb := rfl

@[simp]
theorem eraseOccurrenceMergeHiCursor_minGallop
    (cursor : MergeHiCursor (Occurrence alpha) nu) :
    (eraseOccurrenceMergeHiCursor cursor).minGallop = cursor.minGallop := rfl

@[simp] theorem eraseOccurrenceMergeHiCursor_phase (cursor : MergeHiCursor (Occurrence alpha) nu) :
    (eraseOccurrenceMergeHiCursor cursor).phase = cursor.phase := rfl

@[simp]
theorem eraseOccurrenceMergeHiCopyDataDecr
    (state : MergeState (Occurrence alpha) nu) (dst src : Int) :
    mergeHiCopyDataDecr? (eraseOccurrenceMergeState state) dst src =
      (mergeHiCopyDataDecr? state dst src).map
        (eraseOccurrenceMergeHiDataCursorResult) := by
  unfold mergeHiCopyDataDecr?
  simp only [eraseOccurrenceMergeState_data, eraseOccurrenceMergeState_tempStorage,
    eraseOccurrenceMergeState_minGallop, eraseOccurrenceMergeState_listlen,
    eraseOccurrenceMergeState_basekeys, eraseOccurrenceMergeState_alloced,
    eraseOccurrenceMergeState_pending, eraseOccurrenceMergeState_key_compare,
    eraseOccurrenceMergeState_mrCurrent, eraseOccurrenceMergeState_mrE,
    eraseOccurrenceMergeState_mrMask]
  rw [eraseOccurrenceSlice_copyDecr]
  cases hcopy : state.data.copyDecr? dst src with
  | none => rfl
  | some copied => simp [eraseOccurrenceMergeHiDataCursorResult, eraseOccurrenceMergeState,
      eraseOccurrenceCursorResult]

@[simp]
theorem eraseOccurrenceMergeHiCopyTempDecr
    (state : MergeState (Occurrence alpha) nu) (dst src : Int) :
    mergeHiCopyTempDecr? (eraseOccurrenceMergeState state) dst src =
      (mergeHiCopyTempDecr? state dst src).map
        (eraseOccurrenceMergeHiDataCursorResult) := by
  unfold mergeHiCopyTempDecr?
  rw [eraseOccurrenceMergeHiCopyTempToData]
  cases hcopy : mergeHiCopyTempToData? state dst src with
  | none => rfl
  | some state => simp [eraseOccurrenceMergeHiDataCursorResult]

theorem occurrenceErasure_mergeHiMemcpyDataToTemp_key_compare_of_eq_some
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

theorem occurrenceErasure_mergeHiMemcpyTempToData_key_compare_of_eq_some
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

theorem occurrenceErasure_mergeHiCopyDataDecr_key_compare_of_eq_some
    (state : MergeState κ ν) (dst src : Int)
    (result : MergeHiDataCursorResult κ ν)
    (hcopy : mergeHiCopyDataDecr? state dst src = some result) :
    result.state.key_compare = state.key_compare := by
  unfold mergeHiCopyDataDecr? at hcopy
  rcases Option.bind_eq_some_iff.mp hcopy with ⟨copied, _hcopied, hresult⟩
  injection hresult with hresult
  subst result
  rfl

theorem occurrenceErasure_mergeHiCopyTempDecr_key_compare_of_eq_some
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
theorem eraseOccurrenceMergeHiFuelExhausted (cursor : MergeHiCursor (Occurrence alpha) nu) :
    mergeHiFuelExhausted (eraseOccurrenceMergeHiCursor cursor) =
      eraseOccurrenceMergeHiResult (mergeHiFuelExhausted cursor) := rfl

@[simp]
theorem eraseOccurrenceMergeHiSucceed (cursor : MergeHiCursor (Occurrence alpha) nu) :
    mergeHiSucceed? (eraseOccurrenceMergeHiCursor cursor) =
      (mergeHiSucceed? cursor).map (eraseOccurrenceMergeHiResult) := by
  unfold mergeHiSucceed?
  simp only [eraseOccurrenceMergeHiCursor_nb, eraseOccurrenceMergeHiCursor_state,
    eraseOccurrenceMergeHiCursor_dest]
  by_cases hnb : cursor.nb = 0
  · simp [hnb, eraseOccurrenceMergeHiResult]
  · simp only [hnb, if_false]
    change
      Option.bind
          (mergeHiMemcpyTempToData? .finalTempToData rfl cursor.nb
            (eraseOccurrenceMergeState cursor.state)
            (cursor.dest - Int.ofNat (cursor.nb - 1)) 0) _ =
        Option.map (eraseOccurrenceMergeHiResult)
          (Option.bind
            (mergeHiMemcpyTempToData? .finalTempToData rfl cursor.nb
              cursor.state (cursor.dest - Int.ofNat (cursor.nb - 1)) 0) _)
    rw [eraseOccurrenceMergeHiFinalTempToData]
    cases hcopy : mergeHiMemcpyTempToData? .finalTempToData rfl cursor.nb
        cursor.state (cursor.dest - Int.ofNat (cursor.nb - 1)) 0 with
    | none => rfl
    | some state => simp [eraseOccurrenceMergeHiResult]

@[simp]
theorem eraseOccurrenceMergeHiCopyA (cursor : MergeHiCursor (Occurrence alpha) nu) :
    mergeHiCopyA? (eraseOccurrenceMergeHiCursor cursor) =
      (mergeHiCopyA? cursor).map (eraseOccurrenceMergeHiResult) := by
  unfold mergeHiCopyA?
  simp only [eraseOccurrenceMergeHiCursor_state, eraseOccurrenceMergeHiCursor_dest,
    eraseOccurrenceMergeHiCursor_ssa, eraseOccurrenceMergeHiCursor_ssb,
    eraseOccurrenceMergeHiCursor_na, eraseOccurrenceMergeState_data,
    eraseOccurrenceMergeState_tempStorage, eraseOccurrenceMergeState_minGallop,
    eraseOccurrenceMergeState_listlen, eraseOccurrenceMergeState_basekeys,
    eraseOccurrenceMergeState_alloced, eraseOccurrenceMergeState_pending,
    eraseOccurrenceMergeState_key_compare, eraseOccurrenceMergeState_mrCurrent,
    eraseOccurrenceMergeState_mrE, eraseOccurrenceMergeState_mrMask]
  change
    (if cursor.nb = 1 ∧ 0 < cursor.na then _ else none) =
      Option.map (eraseOccurrenceMergeHiResult)
        (if cursor.nb = 1 ∧ 0 < cursor.na then _ else none)
  by_cases hactive : cursor.nb = 1 ∧ 0 < cursor.na <;>
    simp only [hactive, if_false, Option.map_none]
  rw [eraseOccurrenceMergeDataMemmove]
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
            (mergeHiCopyTempToData? (eraseOccurrenceMergeState movedState)
              (cursor.dest - Int.ofNat cursor.na) cursor.ssb) _ =
          Option.map (eraseOccurrenceMergeHiResult)
            (Option.bind
              (mergeHiCopyTempToData? movedState
                (cursor.dest - Int.ofNat cursor.na) cursor.ssb) _)
      rw [eraseOccurrenceMergeHiCopyTempToData]
      cases hcopy : mergeHiCopyTempToData? movedState
          (cursor.dest - Int.ofNat cursor.na) cursor.ssb with
      | none => rfl
      | some state => simp [eraseOccurrenceMergeHiResult]

set_option maxHeartbeats 2000000 in
-- The B-side gallop proof follows several nested copy and termination branches.
theorem eraseOccurrenceMergeHiGallopB (lt : BoolComparator alpha)
    (afterB : MergeHiCursor (Occurrence alpha) nu) (aCount : Nat)
    (next : MergeHiCursor (Occurrence alpha) nu →
      Option (MergeHiResult (Occurrence alpha) nu))
    (next' : MergeHiCursor alpha nu → Option (MergeHiResult alpha nu))
    (hcompare : afterB.state.key_compare = occurrenceComparator lt)
    (hnext : ∀ cursor,
      cursor.state.key_compare = occurrenceComparator lt →
      next' (eraseOccurrenceMergeHiCursor cursor) =
        (next cursor).map (eraseOccurrenceMergeHiResult)) :
    mergeHiGallopB? (eraseOccurrenceMergeHiCursor afterB) aCount next' =
      (mergeHiGallopB? afterB aCount next).map
        (eraseOccurrenceMergeHiResult) := by
  unfold mergeHiGallopB?
  simp only [eraseOccurrenceMergeHiCursor_state, eraseOccurrenceMergeHiCursor_ssa,
    eraseOccurrenceMergeHiCursor_nb, eraseOccurrenceMergeHiCursor_dest,
    eraseOccurrenceMergeHiCursor_ssb, eraseOccurrenceMergeHiCursor_na,
    eraseOccurrenceMergeHiCursor_minGallop]
  rw [eraseOccurrenceMergeState_data, eraseOccurrenceSlice_read]
  cases hleft : afterB.state.data.read? afterB.ssa with
  | none => rfl
  | some left =>
      simp only [Option.map_some, bind, Option.bind]
      rw [eraseOccurrenceMergeState_tempStorage, eraseOccurrenceInitializedTempPrefix]
      cases htemp : initializedTempPrefix? afterB.state.a afterB.nb with
      | none => rfl
      | some temp =>
          simp only [Option.map_some, mergeHiBindOptionAcross]
          change
            mergeHiBindOptionAcross
                (gallopLeft? (eraseOccurrenceMergeState afterB.state)
                  (eraseOccurrenceSlice temp) 0
                  left.key.value afterB.nb
                  (afterB.nb - 1)) _ =
              Option.map (eraseOccurrenceMergeHiResult)
                (mergeHiBindOptionAcross
                  (gallopLeft? afterB.state temp 0 left.key afterB.nb
                    (afterB.nb - 1)) _)
          rw [eraseOccurrenceGallopLeft lt afterB.state temp 0 left.key afterB.nb
            (afterB.nb - 1) hcompare]
          cases hgallop : gallopLeft? afterB.state temp 0 left.key afterB.nb
              (afterB.nb - 1) with
          | none => rfl
          | some gallopB =>
              change
                (if gallopB.fuelExhausted then
                    some (mergeHiFuelExhausted
                      (eraseOccurrenceMergeHiCursor afterB))
                  else _) =
                  Option.map (eraseOccurrenceMergeHiResult)
                    (if gallopB.fuelExhausted then
                        some (mergeHiFuelExhausted afterB)
                      else _)
              by_cases hfuel : gallopB.fuelExhausted = true
              · simp [hfuel]
              · simp only [hfuel, Bool.false_eq_true, if_false]
                simp only [eraseOccurrenceMergeHiCursor_state,
                  eraseOccurrenceMergeHiCursor_dest, eraseOccurrenceMergeHiCursor_ssa,
                  eraseOccurrenceMergeHiCursor_ssb, eraseOccurrenceMergeHiCursor_basea,
                  eraseOccurrenceMergeHiCursor_na, eraseOccurrenceMergeHiCursor_nb,
                  eraseOccurrenceMergeHiCursor_minGallop, eraseOccurrenceMergeHiCursor_phase]
                have hfinish (movedB : MergeHiCursor (Occurrence alpha) nu)
                    (hmovedCompare : movedB.state.key_compare =
                      occurrenceComparator lt) :
                    (if movedB.nb = 0 ∨ movedB.nb = 1 then
                        next' (eraseOccurrenceMergeHiCursor movedB)
                      else
                        Option.bind
                          (mergeHiCopyDataDecr?
                            (eraseOccurrenceMergeState movedB.state)
                            movedB.dest movedB.ssa) fun copiedA =>
                          let afterA : MergeHiCursor alpha nu :=
                            { eraseOccurrenceMergeHiCursor movedB with
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
                      Option.map (eraseOccurrenceMergeHiResult)
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
                    rw [eraseOccurrenceMergeHiCopyDataDecr]
                    cases hcopy : mergeHiCopyDataDecr? movedB.state
                        movedB.dest movedB.ssa with
                    | none => rfl
                    | some copiedA =>
                        simp only [Option.map_some, Option.bind_some]
                        simp only [eraseOccurrenceMergeHiDataCursorResult]
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
                              occurrenceErasure_mergeHiCopyDataDecr_key_compare_of_eq_some
                                movedB.state movedB.dest movedB.ssa copiedA hcopy
                            _ = occurrenceComparator lt := hmovedCompare
                        change
                          (if afterA.na = 0 then
                              next' (eraseOccurrenceMergeHiCursor afterA)
                            else if mergeHiCountAtLeast aCount MIN_GALLOP ||
                                mergeHiCountAtLeast
                                  (afterB.nb - gallopB.index) MIN_GALLOP then
                              next' (eraseOccurrenceMergeHiCursor
                                { afterA with
                                  phase := .galloping aCount
                                    (afterB.nb - gallopB.index) })
                            else _) =
                            Option.map (eraseOccurrenceMergeHiResult)
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
                              next' (eraseOccurrenceMergeHiCursor adjusted) =
                                Option.map (eraseOccurrenceMergeHiResult)
                                  (next adjusted)
                            apply hnext adjusted
                            simpa [adjusted, adjustedState] using hafterCompare
                by_cases hzero : afterB.nb - gallopB.index = 0
                · simp only [hzero, if_true]
                  change
                    (if afterB.nb = 0 ∨ afterB.nb = 1 then
                        next' (eraseOccurrenceMergeHiCursor afterB)
                      else
                        Option.bind
                          (mergeHiCopyDataDecr?
                            (eraseOccurrenceMergeState afterB.state)
                            afterB.dest afterB.ssa) _) =
                      Option.map (eraseOccurrenceMergeHiResult)
                        (if afterB.nb = 0 ∨ afterB.nb = 1 then
                            next afterB
                          else
                            Option.bind
                              (mergeHiCopyDataDecr? afterB.state
                                afterB.dest afterB.ssa) _)
                  simpa [hzero] using hfinish afterB hcompare
                · simp only [hzero, if_false]
                  rw [eraseOccurrenceMergeHiGallopTempToData]
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
                            next' (eraseOccurrenceMergeHiCursor movedB)
                          else _) =
                          Option.map (eraseOccurrenceMergeHiResult)
                            (if movedB.nb = 0 ∨ movedB.nb = 1 then
                                next movedB
                              else _)
                      apply hfinish movedB
                      calc
                        movedB.state.key_compare = afterB.state.key_compare :=
                          occurrenceErasure_mergeHiMemcpyTempToData_key_compare_of_eq_some
                            .gallopTempToData rfl
                            (afterB.nb - gallopB.index) afterB.state state
                            (afterB.dest - Int.ofNat
                              (afterB.nb - gallopB.index) + 1)
                            (afterB.ssb - Int.ofNat
                              (afterB.nb - gallopB.index) + 1) hcopy
                        _ = occurrenceComparator lt := hcompare

set_option maxHeartbeats 2000000 in
-- The full gallop round combines two branch-heavy gallop commutation proofs.
theorem eraseOccurrenceMergeHiGallopRound (lt : BoolComparator alpha)
    (cursor : MergeHiCursor (Occurrence alpha) nu)
    (next : MergeHiCursor (Occurrence alpha) nu →
      Option (MergeHiResult (Occurrence alpha) nu))
    (next' : MergeHiCursor alpha nu → Option (MergeHiResult alpha nu))
    (hcompare : cursor.state.key_compare = occurrenceComparator lt)
    (hnext : ∀ cursor,
      cursor.state.key_compare = occurrenceComparator lt →
      next' (eraseOccurrenceMergeHiCursor cursor) =
        (next cursor).map (eraseOccurrenceMergeHiResult)) :
    mergeHiGallopRound? (eraseOccurrenceMergeHiCursor cursor) next' =
      (mergeHiGallopRound? cursor next).map
        (eraseOccurrenceMergeHiResult) := by
  unfold mergeHiGallopRound?
  simp only [eraseOccurrenceMergeHiCursor_state, eraseOccurrenceMergeHiCursor_dest,
    eraseOccurrenceMergeHiCursor_ssa, eraseOccurrenceMergeHiCursor_ssb,
    eraseOccurrenceMergeHiCursor_basea, eraseOccurrenceMergeHiCursor_na,
    eraseOccurrenceMergeHiCursor_nb, eraseOccurrenceMergeHiCursor_minGallop,
    eraseOccurrenceMergeHiCursor_phase, eraseOccurrenceMergeState_data,
    eraseOccurrenceMergeState_tempStorage]
  rw [expandedEraseOccurrenceMergeStateWithMinGallop]
  let minGallop := mergeHiDecreaseMinGallop cursor.minGallop
  let adjustedState : MergeState (Occurrence alpha) nu :=
    { cursor.state with min_gallop := minGallop }
  have hcompare' : adjustedState.key_compare = occurrenceComparator lt := by
    simpa [adjustedState] using hcompare
  change
    Option.bind
        (mergeHiTempRead? (eraseOccurrenceTempStorage adjustedState.a)
          cursor.ssb) _ =
      Option.map (eraseOccurrenceMergeHiResult)
        (Option.bind (mergeHiTempRead? adjustedState.a cursor.ssb) _)
  rw [eraseOccurrenceMergeHiTempRead]
  cases hright : mergeHiTempRead? adjustedState.a cursor.ssb with
  | none => rfl
  | some right =>
      simp only [Option.map_some, Option.bind_some,
        mergeHiBindOptionAcross]
      change
        mergeHiBindOptionAcross
            (gallopRight? (eraseOccurrenceMergeState adjustedState)
              (eraseOccurrenceSlice adjustedState.data) cursor.basea
              right.key.value cursor.na
              (cursor.na - 1)) _ =
          Option.map (eraseOccurrenceMergeHiResult)
            (mergeHiBindOptionAcross
              (gallopRight? adjustedState adjustedState.data cursor.basea
                right.key cursor.na (cursor.na - 1)) _)
      rw [eraseOccurrenceGallopRight lt adjustedState adjustedState.data
        cursor.basea right.key cursor.na (cursor.na - 1) hcompare']
      cases hgallop : gallopRight? adjustedState adjustedState.data
          cursor.basea right.key cursor.na (cursor.na - 1) with
      | none => rfl
      | some gallopA =>
          change
            (if gallopA.fuelExhausted then
                some (mergeHiFuelExhausted
                  (eraseOccurrenceMergeHiCursor
                    { cursor with state := adjustedState }))
              else _) =
              Option.map (eraseOccurrenceMergeHiResult)
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
                    next' (eraseOccurrenceMergeHiCursor movedA)
                  else
                    Option.bind
                      (mergeHiCopyTempDecr?
                        (eraseOccurrenceMergeState movedA.state)
                        movedA.dest movedA.ssb) fun copiedB =>
                      let afterB : MergeHiCursor alpha nu :=
                        { eraseOccurrenceMergeHiCursor movedA with
                          state := copiedB.state
                          dest := copiedB.dst
                          ssb := copiedB.src
                          nb := movedA.nb - 1 }
                      if afterB.nb = 1 then
                        next' afterB
                      else
                        mergeHiGallopB? afterB
                          (cursor.na - gallopA.index) next') =
                  Option.map (eraseOccurrenceMergeHiResult)
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
                rw [eraseOccurrenceMergeHiCopyTempDecr]
                cases hcopy : mergeHiCopyTempDecr? movedA.state movedA.dest
                    movedA.ssb with
                | none => rfl
                | some copiedB =>
                    simp only [Option.map_some, Option.bind_some]
                    simp only [eraseOccurrenceMergeHiDataCursorResult]
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
                          occurrenceErasure_mergeHiCopyTempDecr_key_compare_of_eq_some
                            movedA.state movedA.dest movedA.ssb copiedB hcopy
                        _ = occurrenceComparator lt := hmovedCompare
                    change
                      (if afterB.nb = 1 then
                          next' (eraseOccurrenceMergeHiCursor afterB)
                        else
                          mergeHiGallopB?
                            (eraseOccurrenceMergeHiCursor afterB)
                            (cursor.na - gallopA.index) next') =
                        Option.map (eraseOccurrenceMergeHiResult)
                          (if afterB.nb = 1 then next afterB
                            else mergeHiGallopB? afterB
                              (cursor.na - gallopA.index) next)
                    split
                    · exact hnext afterB hafterCompare
                    · exact eraseOccurrenceMergeHiGallopB lt afterB
                        (cursor.na - gallopA.index) next next' hafterCompare
                        hnext
            by_cases hzero : cursor.na - gallopA.index = 0
            · simp only [hzero, if_true]
              let movedA : MergeHiCursor (Occurrence alpha) nu :=
                { cursor with state := adjustedState, minGallop := minGallop }
              change
                (if movedA.na = 0 then
                    next' (eraseOccurrenceMergeHiCursor movedA)
                  else _) =
                  Option.map (eraseOccurrenceMergeHiResult)
                    (if movedA.na = 0 then next movedA else _)
              simpa [movedA, adjustedState, minGallop, hzero] using
                hfinish movedA hcompare'
            · simp only [hzero, if_false]
              rw [eraseOccurrenceMergeDataMemmove]
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
                        next' (eraseOccurrenceMergeHiCursor movedA)
                      else _) =
                      Option.map (eraseOccurrenceMergeHiResult)
                        (if movedA.na = 0 then next movedA else _)
                  apply hfinish movedA
                  simpa [movedA] using hcompare'

set_option maxHeartbeats 2000000 in
-- Recursive merge-hi commutation expands straight and galloping loop phases.
theorem eraseOccurrenceMergeHiLoop (lt : BoolComparator alpha) (fuel : Nat)
    (cursor : MergeHiCursor (Occurrence alpha) nu)
    (hcompare : cursor.state.key_compare = occurrenceComparator lt) :
    mergeHiLoop? fuel (eraseOccurrenceMergeHiCursor cursor) =
      (mergeHiLoop? fuel cursor).map (eraseOccurrenceMergeHiResult) := by
  induction fuel generalizing cursor with
  | zero =>
      simp only [mergeHiLoop?, eraseOccurrenceMergeHiCursor_na,
        eraseOccurrenceMergeHiCursor_nb]
      by_cases hdone : cursor.na = 0 ∨ cursor.nb = 0
      · simp only [hdone, if_true]
        exact eraseOccurrenceMergeHiSucceed cursor
      · simp only [hdone, if_false]
        by_cases hone : cursor.nb = 1
        · simp only [hone, if_true]
          exact eraseOccurrenceMergeHiCopyA cursor
        · simp only [hone, if_false]
          exact congrArg some (eraseOccurrenceMergeHiFuelExhausted cursor)
  | succ fuel ih =>
      simp only [mergeHiLoop?, eraseOccurrenceMergeHiCursor_na,
        eraseOccurrenceMergeHiCursor_nb, eraseOccurrenceMergeHiCursor_phase,
        eraseOccurrenceMergeHiCursor_state, eraseOccurrenceMergeHiCursor_dest,
        eraseOccurrenceMergeHiCursor_ssa, eraseOccurrenceMergeHiCursor_ssb,
        eraseOccurrenceMergeHiCursor_basea, eraseOccurrenceMergeHiCursor_minGallop]
      by_cases hdone : cursor.na = 0 ∨ cursor.nb = 0
      · simp only [hdone, if_true]
        exact eraseOccurrenceMergeHiSucceed cursor
      · simp only [hdone, if_false]
        by_cases hone : cursor.nb = 1
        · simp only [hone, if_true]
          exact eraseOccurrenceMergeHiCopyA cursor
        · simp only [hone, if_false]
          cases hphase : cursor.phase with
          | straight aCount bCount =>
              rw [eraseOccurrenceMergeState_tempStorage, eraseOccurrenceMergeHiTempRead]
              cases hright : mergeHiTempRead? cursor.state.a cursor.ssb with
              | none => rfl
              | some right =>
                  simp only [Option.map_some, bind, Option.bind]
                  rw [eraseOccurrenceMergeState_data, eraseOccurrenceSlice_read]
                  cases hleft : cursor.state.data.read? cursor.ssa with
                  | none => rfl
                  | some left =>
                      simp only [Option.map_some,
                        eraseOccurrenceMergeState_key_compare, hcompare,
                        eraseOccurrenceComparator_occurrenceComparator,
                        eraseOccurrenceEntry_key, iflt_eraseOccurrence]
                      split
                      · rw [eraseOccurrenceMergeHiCopyDataDecr]
                        cases hcopy : mergeHiCopyDataDecr? cursor.state
                            cursor.dest cursor.ssa with
                        | none => rfl
                        | some copied =>
                            simp only [Option.map_some,
                              eraseOccurrenceMergeHiDataCursorResult]
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
                                  (eraseOccurrenceMergeHiCursor nextCursor) =
                                Option.map (eraseOccurrenceMergeHiResult)
                                  (mergeHiLoop? fuel nextCursor)
                            apply ih nextCursor
                            calc
                              nextCursor.state.key_compare =
                                  cursor.state.key_compare :=
                                occurrenceErasure_mergeHiCopyDataDecr_key_compare_of_eq_some
                                  cursor.state cursor.dest cursor.ssa copied
                                  hcopy
                              _ = occurrenceComparator lt := hcompare
                      · rw [eraseOccurrenceMergeHiCopyTempDecr]
                        cases hcopy : mergeHiCopyTempDecr? cursor.state
                            cursor.dest cursor.ssb with
                        | none => rfl
                        | some copied =>
                            simp only [Option.map_some,
                              eraseOccurrenceMergeHiDataCursorResult]
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
                                  (eraseOccurrenceMergeHiCursor nextCursor) =
                                Option.map (eraseOccurrenceMergeHiResult)
                                  (mergeHiLoop? fuel nextCursor)
                            apply ih nextCursor
                            calc
                              nextCursor.state.key_compare =
                                  cursor.state.key_compare :=
                                occurrenceErasure_mergeHiCopyTempDecr_key_compare_of_eq_some
                                  cursor.state cursor.dest cursor.ssb copied
                                  hcopy
                              _ = occurrenceComparator lt := hcompare
          | galloping aCount bCount =>
              exact eraseOccurrenceMergeHiGallopRound lt cursor
                (mergeHiLoop? fuel) (mergeHiLoop? fuel) hcompare
                (fun nextCursor hnextCompare =>
                  ih nextCursor hnextCompare)

@[simp]
theorem eraseOccurrenceMergeHi (lt : BoolComparator alpha)
    (state : MergeState (Occurrence alpha) nu) (ssa ssb : Int) (na nb : Nat)
    (hcompare : state.key_compare = occurrenceComparator lt) :
    mergeHi? (eraseOccurrenceMergeState state) ssa ssb na nb =
      (mergeHi? state ssa ssb na nb).map (eraseOccurrenceMergeHiResult) := by
  unfold mergeHi?
  split <;> try rfl
  rw [eraseOccurrenceMergeGetmem]
  cases hallocated : mergeGetmem state (BitVec.ofNat 64 nb) with
  | mk allocatedState outcome =>
      cases outcome with
      | guardRejected =>
          simp [eraseOccurrenceMergeGetmemResult, eraseOccurrenceMergeHiResult]
      | reused =>
          simp only [eraseOccurrenceMergeGetmemResult]
          rw [eraseOccurrenceMergeHiInitialDataToTemp]
          cases hcopy : mergeHiMemcpyDataToTemp? .initialDataToTemp rfl nb
              allocatedState 0 ssb with
          | none => rfl
          | some copiedState =>
              simp only [Option.map_some, bind, Option.bind]
              let initial : MergeState (Occurrence alpha) nu := copiedState
              rw [eraseOccurrenceMergeHiCopyDataDecr]
              cases hfirst : mergeHiCopyDataDecr? initial
                  (ssb + Int.ofNat (nb - 1))
                  (ssa + Int.ofNat (na - 1)) with
              | none => rfl
              | some copied =>
                  simp only [Option.map_some,
                    eraseOccurrenceMergeHiDataCursorResult]
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
                        occurrenceErasure_mergeHiCopyDataDecr_key_compare_of_eq_some initial
                          (ssb + Int.ofNat (nb - 1))
                          (ssa + Int.ofNat (na - 1)) copied hfirst
                      _ = copiedState.key_compare := rfl
                      _ = allocatedState.key_compare :=
                        occurrenceErasure_mergeHiMemcpyDataToTemp_key_compare_of_eq_some
                          .initialDataToTemp rfl nb allocatedState copiedState
                          0 ssb hcopy
                      _ = state.key_compare := hallocatedCompare
                      _ = occurrenceComparator lt := hcompare
                  change
                    mergeHiLoop? (na + nb)
                        (eraseOccurrenceMergeHiCursor cursor) =
                      Option.map (eraseOccurrenceMergeHiResult)
                        (mergeHiLoop? (na + nb) cursor)
                  exact eraseOccurrenceMergeHiLoop lt (na + nb) cursor
                    hcursorCompare
      | grown =>
          simp only [eraseOccurrenceMergeGetmemResult]
          rw [eraseOccurrenceMergeHiInitialDataToTemp]
          cases hcopy : mergeHiMemcpyDataToTemp? .initialDataToTemp rfl nb
              allocatedState 0 ssb with
          | none => rfl
          | some copiedState =>
              simp only [Option.map_some, bind, Option.bind]
              let initial : MergeState (Occurrence alpha) nu := copiedState
              rw [eraseOccurrenceMergeHiCopyDataDecr]
              cases hfirst : mergeHiCopyDataDecr? initial
                  (ssb + Int.ofNat (nb - 1))
                  (ssa + Int.ofNat (na - 1)) with
              | none => rfl
              | some copied =>
                  simp only [Option.map_some,
                    eraseOccurrenceMergeHiDataCursorResult]
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
                        occurrenceErasure_mergeHiCopyDataDecr_key_compare_of_eq_some initial
                          (ssb + Int.ofNat (nb - 1))
                          (ssa + Int.ofNat (na - 1)) copied hfirst
                      _ = copiedState.key_compare := rfl
                      _ = allocatedState.key_compare :=
                        occurrenceErasure_mergeHiMemcpyDataToTemp_key_compare_of_eq_some
                          .initialDataToTemp rfl nb allocatedState copiedState
                          0 ssb hcopy
                      _ = state.key_compare := hallocatedCompare
                      _ = occurrenceComparator lt := hcompare
                  change
                    mergeHiLoop? (na + nb)
                        (eraseOccurrenceMergeHiCursor cursor) =
                      Option.map (eraseOccurrenceMergeHiResult)
                        (mergeHiLoop? (na + nb) cursor)
                  exact eraseOccurrenceMergeHiLoop lt (na + nb) cursor
                    hcursorCompare

end CPythonListsort
