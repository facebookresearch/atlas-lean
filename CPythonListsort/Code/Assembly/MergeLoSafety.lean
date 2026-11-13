/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Code.Assembly.MergeTracePrimitives
import Code.Assembly.MergeGetmemRequestBound
import Code.Assembly.MergeGetmemStorageValid
import Code.Assembly.GallopLeftSafety
import Code.Assembly.GallopRightSafety

/-!
# `merge_lo` lockstep safety

This module instruments the reviewed `merge_lo` transcription with the typed
main-data and temporary-storage primitives from `MergeTracePrimitives`.
Temporary gallops read their actual temporary backing directly; the
materialized `SortSlice` is used only as an untraced semantic bridge to the
reviewed evaluator.
-/

namespace CPythonListsort

universe u v w

variable {κ : Type u} {ν : Type v}

/-! ## Classified bulk-copy permits -/

/-- Provenance permit consumed by the initial main-to-temporary copy. -/
theorem mergeLoInitialDataToTempPermit :
    (MergeMemcpySite.lo .initialDataToTemp).MainToTempPermit where
  direction := rfl
  distinctBacking := MergeMemcpySite.distinct _

/-- Provenance permit consumed by an A-side gallop block copy. -/
theorem mergeLoGallopTempToDataPermit :
    (MergeMemcpySite.lo .gallopTempToData).TempToMainPermit where
  direction := rfl
  distinctBacking := MergeMemcpySite.distinct _

/-- Provenance permit consumed by the final A-side remainder copy. -/
theorem mergeLoFinalTempToDataPermit :
    (MergeMemcpySite.lo .finalTempToData).TempToMainPermit where
  direction := rfl
  distinctBacking := MergeMemcpySite.distinct _

/-! ## Trace-preserving control helpers -/

/-- Lift an already-reviewed partial, non-accessing computation into the trace
monad. -/
def mergeLoTraceOption : Option α → TraceResult α
  | none => TraceResult.failure
  | some value => TraceResult.pure value

@[simp]
theorem mergeLoTraceOption_erase (value : Option α) :
    (mergeLoTraceOption value).erase = value := by
  cases value <;> rfl

/-! ## Exact primitive bridges -/

/-- The natural-index temporary read used by `merge_lo` is the nonnegative
specialization of the common signed temporary read. -/
@[simp]
theorem mergeTempRead_ofNat (storage : TempStorage κ ν) (index : Nat) :
    mergeTempRead? storage (Int.ofNat index) =
      mergeLoTempRead? storage index := by
  simp [mergeTempRead?, mergeLoTempRead?]

/-- The natural-index temporary write used by `merge_lo` is the nonnegative
specialization of the common signed temporary write. -/
@[simp]
theorem mergeTempWrite_ofNat (storage : TempStorage κ ν) (index : Nat)
    (entry : SortSliceEntry κ ν) :
    mergeTempWrite? storage (Int.ofNat index) entry =
      mergeLoTempWrite? storage index entry := by
  by_cases hindex : index < storage.cells.size
  · simp [mergeTempWrite?, mergeLoTempWrite?, hindex,
      Array.setIfInBounds_def]
  · simp [mergeTempWrite?, mergeLoTempWrite?, hindex]

/-- One shared main-to-temporary cell copy at a natural temporary index is the
cell step used by the reviewed `merge_lo` transcription. -/
theorem mainToTempCell_ofNat (state : MergeState κ ν) (destination : Nat)
    (source : Int) :
    mainToTempCell? state (Int.ofNat destination) source = (do
      let entry ← state.data.read? source
      let storage ← mergeLoTempWrite? state.a destination entry
      pure { state with a := storage }) := by
  unfold mainToTempCell?
  cases hread : state.data.read? source with
  | none => rfl
  | some entry =>
      simp only [bind, Option.bind]
      rw [show mergeTempWrite? state.a (Int.ofNat destination) entry =
        mergeLoTempWrite? state.a destination entry from
          mergeTempWrite_ofNat state.a destination entry]

/-- One shared temporary-to-main cell copy at a natural temporary index is the
cell step used by the reviewed `merge_lo` transcription. -/
theorem tempToMainCell_ofNat (state : MergeState κ ν) (destination : Int)
    (source : Nat) :
    tempToMainCell? state destination (Int.ofNat source) = (do
      let entry ← mergeLoTempRead? state.a source
      let data ← state.data.write? destination entry
      pure { state with data := data }) := by
  unfold tempToMainCell?
  rw [show mergeTempRead? state.a (Int.ofNat source) =
    mergeLoTempRead? state.a source from mergeTempRead_ofNat state.a source]

/-- Erasing the shared main-to-temp core at a natural destination is exactly
the reviewed tagged `merge_lo` helper. -/
theorem mainToTempMemcpy_eq_mergeLo
    (site : MergeLoMemcpyCallsite)
    (hDirection : site.backings =
      { destination := .temporary, source := .main })
    (count : Nat) (state : MergeState κ ν) (destination : Nat) (source : Int) :
    mainToTempMemcpy? count state (Int.ofNat destination) source =
      mergeLoMemcpyDataToTemp? site hDirection count state destination source := by
  induction count generalizing state destination source with
  | zero => rfl
  | succ count ih =>
      simp only [mainToTempMemcpy?, mergeLoMemcpyDataToTemp?]
      rw [mainToTempCell_ofNat]
      cases hread : state.data.read? source with
      | none => simp
      | some entry =>
          cases hwrite : mergeLoTempWrite? state.a destination entry with
          | none => simp [hwrite]
          | some storage =>
              simpa [hread, hwrite, bind, Option.bind,
                Int.ofNat_eq_natCast, Nat.cast_add, Nat.cast_one] using
                ih { state with a := storage } (destination + 1) (source + 1)

/-- Erasing the shared temp-to-main core at a natural temporary source is
exactly the reviewed tagged `merge_lo` helper. -/
theorem tempToMainMemcpy_eq_mergeLo
    (site : MergeLoMemcpyCallsite)
    (hDirection : site.backings =
      { destination := .main, source := .temporary })
    (count : Nat) (state : MergeState κ ν) (destination : Int) (source : Nat) :
    tempToMainMemcpy? count state destination (Int.ofNat source) =
      mergeLoMemcpyTempToData? site hDirection count state destination source := by
  induction count generalizing state destination source with
  | zero => rfl
  | succ count ih =>
      simp only [tempToMainMemcpy?, mergeLoMemcpyTempToData?]
      rw [tempToMainCell_ofNat]
      cases hread : mergeLoTempRead? state.a source with
      | none => simp
      | some entry =>
          cases hwrite : state.data.write? destination entry with
          | none => simp [hwrite]
          | some data =>
              simpa [hread, hwrite, bind, Option.bind,
                Int.ofNat_eq_natCast, Nat.cast_add, Nat.cast_one] using
                ih { state with data := data } (destination + 1) (source + 1)

/-- An initialized, allocated natural temporary range is a valid direct gallop
source. -/
theorem mergeLoTemporary_validRange (storage : TempStorage κ ν)
    (start count : Nat) (hbound : start + count ≤ storage.cells.size)
    (hinitialized : MergeLoTempRangeInitialized storage start count) :
    (GallopKeySource.temporary storage (Int.ofNat start)).ValidRange count := by
  refine ⟨Int.natCast_nonneg start, ?_, ?_⟩
  · simpa only [GallopKeySource.base, GallopKeySource.extent,
      Int.ofNat_eq_natCast, Nat.cast_add] using Int.ofNat_le.mpr hbound
  · intro i hi
    rcases hinitialized i hi with ⟨entry, hentry⟩
    refine ⟨entry, ?_⟩
    change mergeTempRead? storage
      (Int.ofNat start + Int.ofNat i) = some entry
    rw [show Int.ofNat start + Int.ofNat i = Int.ofNat (start + i) by
      simp only [Int.ofNat_eq_natCast, Nat.cast_add]]
    rw [mergeTempRead_ofNat]
    exact hentry

/-- Exact bridge from the direct temporary gallop used by the traced merge to
the materialized-slice gallop used by the reviewed transcription. -/
theorem erase_mergeLoTemporaryGallopRight (state : MergeState κ ν)
    (start count : Nat) (slice : SortSlice κ ν) (key : κ)
    (hbound : start + count ≤ state.a.cells.size)
    (hinitialized : MergeLoTempRangeInitialized state.a start count)
    (hslice : mergeLoTempRun? state.a start count = some slice)
    (hcount : 0 < count) (hmax : count ≤ PY_LIST_MAX) :
    (gallopRightTraced? state
      (.temporary state.a (Int.ofNat start)) key count 0).erase =
        gallopRight? state slice 0 key count 0 := by
  apply erase_gallopRightTraced_eq_slice state
    (.temporary state.a (Int.ofNat start)) slice 0 key count 0
  · exact mergeLoTemporary_validRange state.a start count hbound hinitialized
  · exact tempRun_agreesWithSlice_of_eq_some state.a start count slice hslice
  · exact hcount
  · omega
  · exact hmax

/-- Record that the outer merge driver, or a nested gallop, exhausted fuel. -/
def mergeLoFuelFailureTraced (machine : MergeLoMachine κ ν) :
    TraceResult (MergeLoResult κ ν) :=
  (TraceResult.pure (mergeLoOutOfFuel machine.state)).markFuelExhausted

/-! ## One-step movement -/

/-- Copy one left-run entry from temporary storage and advance forward. -/
def mergeLoCopyAIncrTraced? (machine : MergeLoMachine κ ν) :
    TraceResult (MergeLoMachine κ ν) :=
  (tempToMainCellTraced? machine.state machine.dest (Int.ofNat machine.aPos)).map
    fun state =>
      { machine with
        state := state
        dest := machine.dest + 1
        aPos := machine.aPos + 1
        na := machine.na - 1 }

/-- Copy one right-run entry within main data and advance forward. -/
def mergeLoCopyBIncrTraced? (machine : MergeLoMachine κ ν) :
    TraceResult (MergeLoMachine κ ν) :=
  (mainDataMemmoveTraced? machine.state machine.dest machine.bPos 1).map
    fun state =>
    { machine with
      state := state
      dest := machine.dest + 1
      bPos := machine.bPos + 1
      nb := machine.nb - 1 }

/-- The successful tail copies the unconsumed temporary remainder. -/
def mergeLoSucceedTraced? (machine : MergeLoMachine κ ν) :
    TraceResult (MergeLoResult κ ν) :=
  (tempToMainMemcpyTraced? (.lo .finalTempToData)
      mergeLoFinalTempToDataPermit machine.na machine.state machine.dest
      (Int.ofNat machine.aPos)).map mergeLoSuccess

/-- The `CopyB` label shifts the right remainder and installs the unique
remaining left entry. -/
def mergeLoCopyBTraced? (machine : MergeLoMachine κ ν) :
    TraceResult (MergeLoResult κ ν) :=
  if machine.na = 1 ∧ 0 < machine.nb then
    (mainDataMemmoveTraced? machine.state machine.dest machine.bPos
        machine.nb).bind fun state =>
      (tempToMainCellTraced? state
        (machine.dest + Int.ofNat machine.nb)
        (Int.ofNat machine.aPos)).map mergeLoSuccess
  else
    TraceResult.failure

/-! ## Galloping and outer driver -/

/-- One traced galloping iteration.  The A-side search uses the physical
temporary source.  `activeA` is materialized without trace solely to relate the
direct-source gallop to the reviewed `gallopRight?` call during erasure. -/
def mergeLoGallopRoundTraced?
    (machine : MergeLoMachine κ ν)
    (next : MergeLoMachine κ ν → Nat → Nat →
      TraceResult (MergeLoResult κ ν)) :
    TraceResult (MergeLoResult κ ν) :=
  if machine.na ≤ 1 ∨ machine.nb = 0 then
    TraceResult.failure
  else
    let minGallop :=
      if (1 : PySSize).slt machine.minGallop then
        machine.minGallop - 1
      else
        machine.minGallop
    let state := { machine.state with min_gallop := minGallop }
    let machine := { machine with state := state, minGallop := minGallop }
    (TraceResult.sortSliceKeysRead? machine.state.data machine.bPos).bind
      fun firstB =>
        (mergeLoTraceOption
          (mergeLoTempRun? machine.state.a machine.aPos machine.na)).bind
          fun _activeA =>
            (gallopRightTraced? machine.state
              (.temporary machine.state.a (Int.ofNat machine.aPos))
              firstB.key machine.na 0).bind fun gallopA =>
              if gallopA.fuelExhausted then
                mergeLoFuelFailureTraced machine
              else
                let aCount := gallopA.index
                if aCount > machine.na then
                  TraceResult.failure
                else
                  (tempToMainMemcpyTraced? (.lo .gallopTempToData)
                    mergeLoGallopTempToDataPermit aCount machine.state
                    machine.dest (Int.ofNat machine.aPos)).bind fun state =>
                    let machine : MergeLoMachine κ ν :=
                      { machine with
                        state := state
                        dest := machine.dest + Int.ofNat aCount
                        aPos := machine.aPos + aCount
                        na := machine.na - aCount }
                    if machine.na = 0 then
                      mergeLoSucceedTraced? machine
                    else if machine.na = 1 then
                      mergeLoCopyBTraced? machine
                    else
                      (mergeLoCopyBIncrTraced? machine).bind fun machine =>
                        if machine.nb = 0 then
                          mergeLoSucceedTraced? machine
                        else
                          (TraceResult.tempPayloadRead? machine.state.a
                            (Int.ofNat machine.aPos)).bind fun firstA =>
                            (gallopLeftTraced? machine.state
                              (.main machine.state.data machine.bPos)
                              firstA.key machine.nb 0).bind fun gallopB =>
                              if gallopB.fuelExhausted then
                                mergeLoFuelFailureTraced machine
                              else
                                let bCount := gallopB.index
                                if bCount > machine.nb then
                                  TraceResult.failure
                                else
                                  (mainDataMemmoveTraced? machine.state
                                    machine.dest machine.bPos bCount).bind
                                    fun state =>
                                      let machine : MergeLoMachine κ ν :=
                                        { machine with
                                          state := state
                                          dest := machine.dest + Int.ofNat bCount
                                          bPos := machine.bPos + Int.ofNat bCount
                                          nb := machine.nb - bCount }
                                      if machine.nb = 0 then
                                        mergeLoSucceedTraced? machine
                                      else
                                        (mergeLoCopyAIncrTraced? machine).bind
                                          fun machine =>
                                            if machine.na = 1 then
                                              mergeLoCopyBTraced? machine
                                            else
                                              next machine aCount bCount

/-- Fuel-bounded traced phase driver. -/
def mergeLoLoopTraced? :
    Nat → MergeLoMachine κ ν → MergeLoPhase →
      TraceResult (MergeLoResult κ ν)
  | 0, machine, _ => mergeLoFuelFailureTraced machine
  | fuel + 1, machine, .ordinary aCount bCount =>
      if machine.na ≤ 1 ∨ machine.nb = 0 then
        TraceResult.failure
      else
        (TraceResult.tempPayloadRead? machine.state.a
          (Int.ofNat machine.aPos)).bind fun firstA =>
          (TraceResult.sortSliceKeysRead? machine.state.data machine.bPos).bind
            fun firstB =>
              if iflt machine.state.key_compare firstB.key firstA.key then
                (mergeLoCopyBIncrTraced? machine).bind fun machine =>
                  let bCount := bCount + 1
                  if machine.nb = 0 then
                    mergeLoSucceedTraced? machine
                  else if mergeLoCountAtLeastWord bCount machine.minGallop then
                    mergeLoLoopTraced? fuel
                      { machine with minGallop := machine.minGallop + 1 }
                      .galloping
                  else
                    mergeLoLoopTraced? fuel machine (.ordinary 0 bCount)
              else
                (mergeLoCopyAIncrTraced? machine).bind fun machine =>
                  let aCount := aCount + 1
                  if machine.na = 1 then
                    mergeLoCopyBTraced? machine
                  else if mergeLoCountAtLeastWord aCount machine.minGallop then
                    mergeLoLoopTraced? fuel
                      { machine with minGallop := machine.minGallop + 1 }
                      .galloping
                  else
                    mergeLoLoopTraced? fuel machine (.ordinary aCount 0)
  | fuel + 1, machine, .galloping =>
      mergeLoGallopRoundTraced? machine fun machine aCount bCount =>
        if MIN_GALLOP.toNat ≤ aCount ∨ MIN_GALLOP.toNat ≤ bCount then
          mergeLoLoopTraced? fuel machine .galloping
        else
          let minGallop := machine.minGallop + 1
          let state := { machine.state with min_gallop := minGallop }
          mergeLoLoopTraced? fuel
            { machine with state := state, minGallop := minGallop }
            (.ordinary 0 0)

/-! ## Public traced evaluator -/

/-- A genuine instrumented execution of `merge_lo`.  Allocation itself has no
array access event; every subsequent movement and comparison access is routed
through a typed primitive. -/
def mergeLoTraced? (state : MergeState κ ν) (ssa ssb : Int) (na nb : Nat) :
    TraceResult (MergeLoResult κ ν) :=
  if 0 < na ∧ 0 < nb ∧ na ≤ PY_SSIZE_T_MAX ∧ nb ≤ PY_SSIZE_T_MAX ∧
      ssa + Int.ofNat na = ssb then
    let allocated := mergeGetmem state (BitVec.ofNat 64 na)
    if allocated.outcome = .guardRejected then
      TraceResult.pure (mergeLoFailure allocated.state)
    else
      (mainToTempMemcpyTraced? (.lo .initialDataToTemp)
        mergeLoInitialDataToTempPermit na allocated.state 0 ssa).bind fun state =>
        let machine : MergeLoMachine κ ν :=
          { state := state
            dest := ssa
            aPos := 0
            bPos := ssb
            na := na
            nb := nb
            minGallop := state.min_gallop }
        (mergeLoCopyBIncrTraced? machine).bind fun machine =>
          if machine.nb = 0 then
            mergeLoSucceedTraced? machine
          else if machine.na = 1 then
            mergeLoCopyBTraced? machine
          else
            mergeLoLoopTraced? (na + nb + 1) machine (.ordinary 0 0)
  else
    TraceResult.failure

/-! ## Absence of nested merge-memory and policy events -/

/-- A local trace fragment contains neither a top-level merge-memory boundary
nor a merge-policy event.  Keeping the two channels together makes the
structural induction below the single source of truth for both absence
claims. -/
private def MergeLoMemoryEventFree (execution : TraceResult α) : Prop :=
  execution.trace.memoryEvents = [] ∧ execution.trace.policyEvents = []

private theorem mergeLoMemoryEventFree_pure (value : α) :
    MergeLoMemoryEventFree (TraceResult.pure value) := by
  exact ⟨rfl, rfl⟩

private theorem mergeLoMemoryEventFree_failure :
    MergeLoMemoryEventFree (TraceResult.failure : TraceResult α) := by
  exact ⟨rfl, rfl⟩

private theorem mergeLoMemoryEventFree_map (current : TraceResult α)
    (transform : α → β) (hcurrent : MergeLoMemoryEventFree current) :
    MergeLoMemoryEventFree (current.map transform) :=
  hcurrent

private theorem mergeLoMemoryEventFree_bind (current : TraceResult α)
    (next : α → TraceResult β) (hcurrent : MergeLoMemoryEventFree current)
    (hnext : ∀ value, MergeLoMemoryEventFree (next value)) :
    MergeLoMemoryEventFree (current.bind next) := by
  exact
    ⟨TraceResult.memoryEvents_bind_eq_nil current next hcurrent.1
        (fun value => (hnext value).1),
      TraceResult.policyEvents_bind_eq_nil current next hcurrent.2
        (fun value => (hnext value).2)⟩

private theorem mergeLoMemoryEventFree_markFuelExhausted
    (current : TraceResult α) (hcurrent : MergeLoMemoryEventFree current) :
    MergeLoMemoryEventFree current.markFuelExhausted := by
  simpa [MergeLoMemoryEventFree, TraceResult.markFuelExhausted,
    AccessTrace.compose, AccessTrace.exhausted] using hcurrent

private theorem mergeLoMemoryEventFree_sourceRead
    (source : GallopKeySource κ ν) (index : Int) :
    MergeLoMemoryEventFree (source.readTraced? index) := by
  simp [MergeLoMemoryEventFree, GallopKeySource.trace_readTraced,
    AccessTrace.singletonAccess]

private theorem mergeLoMemoryEventFree_tempRead
    (storage : TempStorage κ ν) (index : Int) :
    MergeLoMemoryEventFree (TraceResult.tempPayloadRead? storage index) := by
  unfold MergeLoMemoryEventFree
  rw [TraceResult.trace_tempPayloadRead]
  exact ⟨rfl, rfl⟩

private theorem mergeLoMemoryEventFree_tempWrite
    (storage : TempStorage κ ν) (index : Int)
    (entry : SortSliceEntry κ ν) :
    MergeLoMemoryEventFree
      (TraceResult.tempPayloadWrite? storage index entry) := by
  exact ⟨rfl, rfl⟩

private theorem mergeLoMemoryEventFree_keyRead
    (slice : SortSlice κ ν) (index : Int) :
    MergeLoMemoryEventFree (TraceResult.sortSliceKeysRead? slice index) := by
  exact ⟨rfl, rfl⟩

private theorem mergeLoMemoryEventFree_valueRead
    (slice : SortSlice κ ν) (index : Int) :
    MergeLoMemoryEventFree (TraceResult.sortSliceValuesRead? slice index) := by
  exact ⟨rfl, rfl⟩

private theorem mergeLoMemoryEventFree_keyWrite
    (slice : SortSlice κ ν) (index : Int) (entry : SortSliceEntry κ ν) :
    MergeLoMemoryEventFree
      (TraceResult.sortSliceKeysWrite? slice index entry) := by
  exact ⟨rfl, rfl⟩

private theorem mergeLoMemoryEventFree_valueWrite
    (slice : SortSlice κ ν) (index : Int) (entry : SortSliceEntry κ ν) :
    MergeLoMemoryEventFree
      (TraceResult.sortSliceValuesWrite? slice index entry) := by
  exact ⟨rfl, rfl⟩

private theorem mergeLoMemoryEventFree_copyKeys
    (destination source : SortSlice κ ν) (dst src : Int) :
    MergeLoMemoryEventFree
      (SortSlice.copyKeysFromTraced? destination source dst src) := by
  apply mergeLoMemoryEventFree_bind
  · exact mergeLoMemoryEventFree_keyRead _ _
  · intro entry
    exact mergeLoMemoryEventFree_keyWrite _ _ _

private theorem mergeLoMemoryEventFree_copyValues
    (destination source : SortSlice κ ν) (dst src : Int) :
    MergeLoMemoryEventFree
      (SortSlice.copyValuesFromTraced? destination source dst src) := by
  apply mergeLoMemoryEventFree_bind
  · exact mergeLoMemoryEventFree_valueRead _ _
  · intro entry
    exact mergeLoMemoryEventFree_valueWrite _ _ _

private theorem mergeLoMemoryEventFree_mainToTempKey
    (state : MergeState κ ν) (tempDst mainSrc : Int) :
    MergeLoMemoryEventFree (mainToTempKeyTraced? state tempDst mainSrc) := by
  unfold mainToTempKeyTraced?
  apply mergeLoMemoryEventFree_bind
  · exact mergeLoMemoryEventFree_keyRead _ _
  · intro entry
    apply mergeLoMemoryEventFree_map
    exact mergeLoMemoryEventFree_tempWrite _ _ _

private theorem mergeLoMemoryEventFree_mainToTempValues
    (state : MergeState κ ν) (tempDst mainSrc : Int) :
    MergeLoMemoryEventFree (mainToTempValuesTraced? state tempDst mainSrc) := by
  unfold mainToTempValuesTraced?
  apply mergeLoMemoryEventFree_bind
  · exact mergeLoMemoryEventFree_valueRead _ _
  · intro entry
    apply mergeLoMemoryEventFree_map
    exact mergeLoMemoryEventFree_tempWrite _ _ _

private theorem mergeLoMemoryEventFree_tempToMainKey
    (state : MergeState κ ν) (mainDst tempSrc : Int) :
    MergeLoMemoryEventFree (tempToMainKeyTraced? state mainDst tempSrc) := by
  unfold tempToMainKeyTraced?
  apply mergeLoMemoryEventFree_bind
  · exact mergeLoMemoryEventFree_tempRead _ _
  · intro entry
    apply mergeLoMemoryEventFree_map
    exact mergeLoMemoryEventFree_keyWrite _ _ _

private theorem mergeLoMemoryEventFree_tempToMainValues
    (state : MergeState κ ν) (mainDst tempSrc : Int) :
    MergeLoMemoryEventFree (tempToMainValuesTraced? state mainDst tempSrc) := by
  unfold tempToMainValuesTraced?
  apply mergeLoMemoryEventFree_bind
  · exact mergeLoMemoryEventFree_tempRead _ _
  · intro entry
    apply mergeLoMemoryEventFree_map
    exact mergeLoMemoryEventFree_valueWrite _ _ _

private theorem mergeLoMemoryEventFree_tempToMainCell
    (state : MergeState κ ν) (mainDst tempSrc : Int) :
    MergeLoMemoryEventFree (tempToMainCellTraced? state mainDst tempSrc) := by
  unfold tempToMainCellTraced?
  apply mergeLoMemoryEventFree_bind
  · exact mergeLoMemoryEventFree_tempToMainKey _ _ _
  · intro keyResult
    split
    · exact mergeLoMemoryEventFree_tempToMainValues _ _ _
    · exact mergeLoMemoryEventFree_pure _

private theorem mergeLoMemoryEventFree_mainToTempKeys
    (site : MergeMemcpySite) (permit : site.MainToTempPermit) (count : Nat)
    (state : MergeState κ ν) (tempDst mainSrc : Int) :
    MergeLoMemoryEventFree
      (mainToTempKeysTraced? site permit count state tempDst mainSrc) := by
  induction count generalizing state tempDst mainSrc with
  | zero => exact mergeLoMemoryEventFree_pure _
  | succ count ih =>
      simp only [mainToTempKeysTraced?]
      apply mergeLoMemoryEventFree_bind
      · exact mergeLoMemoryEventFree_mainToTempKey _ _ _
      · intro nextState
        exact ih _ _ _

private theorem mergeLoMemoryEventFree_mainToTempValuesPhase
    (site : MergeMemcpySite) (permit : site.MainToTempPermit) (count : Nat)
    (state : MergeState κ ν) (tempDst mainSrc : Int) :
    MergeLoMemoryEventFree
      (mainToTempValuesPhaseTraced? site permit count state tempDst mainSrc) := by
  induction count generalizing state tempDst mainSrc with
  | zero => exact mergeLoMemoryEventFree_pure _
  | succ count ih =>
      simp only [mainToTempValuesPhaseTraced?]
      apply mergeLoMemoryEventFree_bind
      · exact mergeLoMemoryEventFree_mainToTempValues _ _ _
      · intro nextState
        exact ih _ _ _

private theorem mergeLoMemoryEventFree_mainToTempMemcpy
    (site : MergeMemcpySite) (permit : site.MainToTempPermit) (count : Nat)
    (state : MergeState κ ν) (tempDst mainSrc : Int) :
    MergeLoMemoryEventFree
      (mainToTempMemcpyTraced? site permit count state tempDst mainSrc) := by
  unfold mainToTempMemcpyTraced?
  apply mergeLoMemoryEventFree_bind
  · exact mergeLoMemoryEventFree_mainToTempKeys _ _ _ _ _ _
  · intro keyResult
    split
    · exact mergeLoMemoryEventFree_mainToTempValuesPhase _ _ _ _ _ _
    · exact mergeLoMemoryEventFree_pure _

private theorem mergeLoMemoryEventFree_tempToMainKeys
    (site : MergeMemcpySite) (permit : site.TempToMainPermit) (count : Nat)
    (state : MergeState κ ν) (mainDst tempSrc : Int) :
    MergeLoMemoryEventFree
      (tempToMainKeysTraced? site permit count state mainDst tempSrc) := by
  induction count generalizing state mainDst tempSrc with
  | zero => exact mergeLoMemoryEventFree_pure _
  | succ count ih =>
      simp only [tempToMainKeysTraced?]
      apply mergeLoMemoryEventFree_bind
      · exact mergeLoMemoryEventFree_tempToMainKey _ _ _
      · intro nextState
        exact ih _ _ _

private theorem mergeLoMemoryEventFree_tempToMainValuesPhase
    (site : MergeMemcpySite) (permit : site.TempToMainPermit) (count : Nat)
    (state : MergeState κ ν) (mainDst tempSrc : Int) :
    MergeLoMemoryEventFree
      (tempToMainValuesPhaseTraced? site permit count state mainDst tempSrc) := by
  induction count generalizing state mainDst tempSrc with
  | zero => exact mergeLoMemoryEventFree_pure _
  | succ count ih =>
      simp only [tempToMainValuesPhaseTraced?]
      apply mergeLoMemoryEventFree_bind
      · exact mergeLoMemoryEventFree_tempToMainValues _ _ _
      · intro nextState
        exact ih _ _ _

private theorem mergeLoMemoryEventFree_tempToMainMemcpy
    (site : MergeMemcpySite) (permit : site.TempToMainPermit) (count : Nat)
    (state : MergeState κ ν) (mainDst tempSrc : Int) :
    MergeLoMemoryEventFree
      (tempToMainMemcpyTraced? site permit count state mainDst tempSrc) := by
  unfold tempToMainMemcpyTraced?
  apply mergeLoMemoryEventFree_bind
  · exact mergeLoMemoryEventFree_tempToMainKeys _ _ _ _ _ _
  · intro keyResult
    split
    · exact mergeLoMemoryEventFree_tempToMainValuesPhase _ _ _ _ _ _
    · exact mergeLoMemoryEventFree_pure _

private theorem mergeLoMemoryEventFree_memmoveForwardKeys
    (count : Nat) (slice : SortSlice κ ν) (dst src : Int) :
    MergeLoMemoryEventFree
      (SortSlice.memmoveForwardKeysTraced? count slice dst src) := by
  induction count generalizing slice dst src with
  | zero => exact mergeLoMemoryEventFree_pure _
  | succ count ih =>
      simp only [SortSlice.memmoveForwardKeysTraced?]
      apply mergeLoMemoryEventFree_bind
      · exact mergeLoMemoryEventFree_copyKeys _ _ _ _
      · intro updated
        exact ih _ _ _

private theorem mergeLoMemoryEventFree_memmoveForwardValues
    (count : Nat) (slice : SortSlice κ ν) (dst src : Int) :
    MergeLoMemoryEventFree
      (SortSlice.memmoveForwardValuesTraced? count slice dst src) := by
  induction count generalizing slice dst src with
  | zero => exact mergeLoMemoryEventFree_pure _
  | succ count ih =>
      simp only [SortSlice.memmoveForwardValuesTraced?]
      apply mergeLoMemoryEventFree_bind
      · exact mergeLoMemoryEventFree_copyValues _ _ _ _
      · intro updated
        exact ih _ _ _

private theorem mergeLoMemoryEventFree_memmoveBackwardKeys
    (count : Nat) (slice : SortSlice κ ν) (dst src : Int) :
    MergeLoMemoryEventFree
      (SortSlice.memmoveBackwardKeysTraced? count slice dst src) := by
  induction count generalizing slice dst src with
  | zero => exact mergeLoMemoryEventFree_pure _
  | succ count ih =>
      simp only [SortSlice.memmoveBackwardKeysTraced?]
      apply mergeLoMemoryEventFree_bind
      · exact mergeLoMemoryEventFree_copyKeys _ _ _ _
      · intro updated
        exact ih _ _ _

private theorem mergeLoMemoryEventFree_memmoveBackwardValues
    (count : Nat) (slice : SortSlice κ ν) (dst src : Int) :
    MergeLoMemoryEventFree
      (SortSlice.memmoveBackwardValuesTraced? count slice dst src) := by
  induction count generalizing slice dst src with
  | zero => exact mergeLoMemoryEventFree_pure _
  | succ count ih =>
      simp only [SortSlice.memmoveBackwardValuesTraced?]
      apply mergeLoMemoryEventFree_bind
      · exact mergeLoMemoryEventFree_copyValues _ _ _ _
      · intro updated
        exact ih _ _ _

private theorem mergeLoMemoryEventFree_memmove
    (valuesPresent : Bool) (slice : SortSlice κ ν)
    (dst src : Int) (count : Nat) :
    MergeLoMemoryEventFree
      (SortSlice.memmoveTraced? valuesPresent slice dst src count) := by
  unfold SortSlice.memmoveTraced?
  split
  · apply mergeLoMemoryEventFree_bind
    · exact mergeLoMemoryEventFree_memmoveForwardKeys _ _ _ _
    · intro keyResult
      split
      · exact mergeLoMemoryEventFree_memmoveForwardValues _ _ _ _
      · constructor <;> rfl
  · apply mergeLoMemoryEventFree_bind
    · exact mergeLoMemoryEventFree_memmoveBackwardKeys _ _ _ _
    · intro keyResult
      split
      · exact mergeLoMemoryEventFree_memmoveBackwardValues _ _ _ _
      · constructor <;> rfl

private theorem mergeLoMemoryEventFree_mainDataMemmove
    (state : MergeState κ ν) (dst src : Int) (count : Nat) :
    MergeLoMemoryEventFree (mainDataMemmoveTraced? state dst src count) := by
  unfold mainDataMemmoveTraced?
  apply mergeLoMemoryEventFree_map
  exact mergeLoMemoryEventFree_memmove _ _ _ _ _

set_option linter.flexible false in
private theorem mergeLoMemoryEventFree_leftRightExponential
    (fuel : Nat) (lt : BoolComparator κ) (source : GallopKeySource κ ν)
    (key : κ) (hint maxOffset lastOffset offset : Nat) :
    MergeLoMemoryEventFree
      (gallopLeftRightExponentialTraced? fuel lt source key hint maxOffset
        lastOffset offset) := by
  induction fuel generalizing lastOffset offset with
  | zero =>
      by_cases hfuel : offset < maxOffset <;>
        simp [gallopLeftRightExponentialTraced?, MergeLoMemoryEventFree,
          hfuel] <;> (constructor <;> rfl)
  | succ fuel ih =>
      simp only [gallopLeftRightExponentialTraced?]
      split
      · apply mergeLoMemoryEventFree_bind
        · exact mergeLoMemoryEventFree_sourceRead _ _
        · intro entry
          split
          · split
            · exact ih _ _
            · exact mergeLoMemoryEventFree_failure
          · exact mergeLoMemoryEventFree_pure _
      · exact mergeLoMemoryEventFree_pure _

set_option linter.flexible false in
private theorem mergeLoMemoryEventFree_leftLeftExponential
    (fuel : Nat) (lt : BoolComparator κ) (source : GallopKeySource κ ν)
    (key : κ) (hint maxOffset lastOffset offset : Nat) :
    MergeLoMemoryEventFree
      (gallopLeftLeftExponentialTraced? fuel lt source key hint maxOffset
        lastOffset offset) := by
  induction fuel generalizing lastOffset offset with
  | zero =>
      by_cases hfuel : offset < maxOffset <;>
        simp [gallopLeftLeftExponentialTraced?, MergeLoMemoryEventFree,
          hfuel] <;> (constructor <;> rfl)
  | succ fuel ih =>
      simp only [gallopLeftLeftExponentialTraced?]
      split
      · apply mergeLoMemoryEventFree_bind
        · exact mergeLoMemoryEventFree_sourceRead _ _
        · intro entry
          split
          · exact mergeLoMemoryEventFree_pure _
          · split
            · exact ih _ _
            · exact mergeLoMemoryEventFree_failure
      · exact mergeLoMemoryEventFree_pure _

set_option linter.flexible false in
private theorem mergeLoMemoryEventFree_rightLeftExponential
    (fuel : Nat) (lt : BoolComparator κ) (source : GallopKeySource κ ν)
    (key : κ) (hint maxOffset lastOffset offset : Nat) :
    MergeLoMemoryEventFree
      (gallopRightLeftExponentialTraced? fuel lt source key hint maxOffset
        lastOffset offset) := by
  induction fuel generalizing lastOffset offset with
  | zero =>
      by_cases hfuel : offset < maxOffset <;>
        simp [gallopRightLeftExponentialTraced?, MergeLoMemoryEventFree,
          hfuel] <;> (constructor <;> rfl)
  | succ fuel ih =>
      simp only [gallopRightLeftExponentialTraced?]
      split
      · apply mergeLoMemoryEventFree_bind
        · exact mergeLoMemoryEventFree_sourceRead _ _
        · intro entry
          split
          · split
            · exact ih _ _
            · exact mergeLoMemoryEventFree_failure
          · exact mergeLoMemoryEventFree_pure _
      · exact mergeLoMemoryEventFree_pure _

set_option linter.flexible false in
private theorem mergeLoMemoryEventFree_rightRightExponential
    (fuel : Nat) (lt : BoolComparator κ) (source : GallopKeySource κ ν)
    (key : κ) (hint maxOffset lastOffset offset : Nat) :
    MergeLoMemoryEventFree
      (gallopRightRightExponentialTraced? fuel lt source key hint maxOffset
        lastOffset offset) := by
  induction fuel generalizing lastOffset offset with
  | zero =>
      by_cases hfuel : offset < maxOffset <;>
        simp [gallopRightRightExponentialTraced?, MergeLoMemoryEventFree,
          hfuel] <;> (constructor <;> rfl)
  | succ fuel ih =>
      simp only [gallopRightRightExponentialTraced?]
      split
      · apply mergeLoMemoryEventFree_bind
        · exact mergeLoMemoryEventFree_sourceRead _ _
        · intro entry
          split
          · exact mergeLoMemoryEventFree_pure _
          · split
            · exact ih _ _
            · exact mergeLoMemoryEventFree_failure
      · exact mergeLoMemoryEventFree_pure _

set_option linter.flexible false in
private theorem mergeLoMemoryEventFree_leftBinary
    (fuel : Nat) (lt : BoolComparator κ) (source : GallopKeySource κ ν)
    (key : κ) (lower upper : Nat) :
    MergeLoMemoryEventFree
      (gallopLeftBinaryTraced? fuel lt source key lower upper) := by
  induction fuel generalizing lower upper with
  | zero =>
      by_cases hfuel : lower < upper <;>
        simp [gallopLeftBinaryTraced?, MergeLoMemoryEventFree, hfuel] <;>
          (constructor <;> rfl)
  | succ fuel ih =>
      simp only [gallopLeftBinaryTraced?]
      split
      · apply mergeLoMemoryEventFree_bind
        · exact mergeLoMemoryEventFree_sourceRead _ _
        · intro entry
          split
          · exact ih _ _
          · exact ih _ _
      · exact mergeLoMemoryEventFree_pure _

set_option linter.flexible false in
private theorem mergeLoMemoryEventFree_rightBinary
    (fuel : Nat) (lt : BoolComparator κ) (source : GallopKeySource κ ν)
    (key : κ) (lower upper : Nat) :
    MergeLoMemoryEventFree
      (gallopRightBinaryTraced? fuel lt source key lower upper) := by
  induction fuel generalizing lower upper with
  | zero =>
      by_cases hfuel : lower < upper <;>
        simp [gallopRightBinaryTraced?, MergeLoMemoryEventFree, hfuel] <;>
          (constructor <;> rfl)
  | succ fuel ih =>
      simp only [gallopRightBinaryTraced?]
      split
      · apply mergeLoMemoryEventFree_bind
        · exact mergeLoMemoryEventFree_sourceRead _ _
        · intro entry
          split
          · exact ih _ _
          · exact ih _ _
      · exact mergeLoMemoryEventFree_pure _

private theorem mergeLoMemoryEventFree_finishLeft
    (fuel : Nat) (lt : BoolComparator κ) (source : GallopKeySource κ ν)
    (key : κ) (n : Nat) (lastOffset upperOffset : Int)
    (exponentialFuelExhausted : Bool) :
    MergeLoMemoryEventFree
      (finishGallopLeftTraced? fuel lt source key n lastOffset upperOffset
        exponentialFuelExhausted) := by
  unfold finishGallopLeftTraced?
  split
  · dsimp only
    split
    · split
      · constructor <;> rfl
      · exact mergeLoMemoryEventFree_leftBinary _ _ _ _ _ _
    · exact mergeLoMemoryEventFree_failure
  · exact mergeLoMemoryEventFree_failure

private theorem mergeLoMemoryEventFree_finishRight
    (fuel : Nat) (lt : BoolComparator κ) (source : GallopKeySource κ ν)
    (key : κ) (n : Nat) (lastOffset upperOffset : Int)
    (exponentialFuelExhausted : Bool) :
    MergeLoMemoryEventFree
      (finishGallopRightTraced? fuel lt source key n lastOffset upperOffset
        exponentialFuelExhausted) := by
  unfold finishGallopRightTraced?
  split
  · dsimp only
    split
    · split
      · constructor <;> rfl
      · exact mergeLoMemoryEventFree_rightBinary _ _ _ _ _ _
    · exact mergeLoMemoryEventFree_failure
  · exact mergeLoMemoryEventFree_failure

private theorem mergeLoMemoryEventFree_gallopLeft
    (state : MergeState κ ν) (source : GallopKeySource κ ν)
    (key : κ) (n hint : Nat) :
    MergeLoMemoryEventFree (gallopLeftTraced? state source key n hint) := by
  unfold gallopLeftTraced?
  split
  · apply mergeLoMemoryEventFree_bind
    · exact mergeLoMemoryEventFree_sourceRead _ _
    · intro hinted
      split
      · apply mergeLoMemoryEventFree_bind
        · exact mergeLoMemoryEventFree_leftRightExponential _ _ _ _ _ _ _ _
        · intro exponential
          exact mergeLoMemoryEventFree_finishLeft _ _ _ _ _ _ _ _
      · apply mergeLoMemoryEventFree_bind
        · exact mergeLoMemoryEventFree_leftLeftExponential _ _ _ _ _ _ _ _
        · intro exponential
          exact mergeLoMemoryEventFree_finishLeft _ _ _ _ _ _ _ _
  · exact mergeLoMemoryEventFree_failure

private theorem mergeLoMemoryEventFree_gallopRight
    (state : MergeState κ ν) (source : GallopKeySource κ ν)
    (key : κ) (n hint : Nat) :
    MergeLoMemoryEventFree (gallopRightTraced? state source key n hint) := by
  unfold gallopRightTraced?
  split
  · apply mergeLoMemoryEventFree_bind
    · exact mergeLoMemoryEventFree_sourceRead _ _
    · intro hinted
      split
      · apply mergeLoMemoryEventFree_bind
        · exact mergeLoMemoryEventFree_rightLeftExponential _ _ _ _ _ _ _ _
        · intro exponential
          exact mergeLoMemoryEventFree_finishRight _ _ _ _ _ _ _ _
      · apply mergeLoMemoryEventFree_bind
        · exact mergeLoMemoryEventFree_rightRightExponential _ _ _ _ _ _ _ _
        · intro exponential
          exact mergeLoMemoryEventFree_finishRight _ _ _ _ _ _ _ _
  · exact mergeLoMemoryEventFree_failure

private theorem mergeLoMemoryEventFree_traceOption (value : Option α) :
    MergeLoMemoryEventFree (mergeLoTraceOption value) := by
  cases value
  · exact mergeLoMemoryEventFree_failure
  · exact mergeLoMemoryEventFree_pure _

private theorem mergeLoMemoryEventFree_fuelFailure
    (machine : MergeLoMachine κ ν) :
    MergeLoMemoryEventFree (mergeLoFuelFailureTraced machine) := by
  apply mergeLoMemoryEventFree_markFuelExhausted
  exact mergeLoMemoryEventFree_pure _

private theorem mergeLoMemoryEventFree_copyAIncr
    (machine : MergeLoMachine κ ν) :
    MergeLoMemoryEventFree (mergeLoCopyAIncrTraced? machine) := by
  unfold mergeLoCopyAIncrTraced?
  apply mergeLoMemoryEventFree_map
  exact mergeLoMemoryEventFree_tempToMainCell _ _ _

private theorem mergeLoMemoryEventFree_copyBIncr
    (machine : MergeLoMachine κ ν) :
    MergeLoMemoryEventFree (mergeLoCopyBIncrTraced? machine) := by
  unfold mergeLoCopyBIncrTraced?
  apply mergeLoMemoryEventFree_map
  exact mergeLoMemoryEventFree_mainDataMemmove _ _ _ _

private theorem mergeLoMemoryEventFree_succeed
    (machine : MergeLoMachine κ ν) :
    MergeLoMemoryEventFree (mergeLoSucceedTraced? machine) := by
  unfold mergeLoSucceedTraced?
  apply mergeLoMemoryEventFree_map
  exact mergeLoMemoryEventFree_tempToMainMemcpy _ _ _ _ _ _

private theorem mergeLoMemoryEventFree_copyB
    (machine : MergeLoMachine κ ν) :
    MergeLoMemoryEventFree (mergeLoCopyBTraced? machine) := by
  unfold mergeLoCopyBTraced?
  split
  · apply mergeLoMemoryEventFree_bind
    · exact mergeLoMemoryEventFree_mainDataMemmove _ _ _ _
    · intro state
      apply mergeLoMemoryEventFree_map
      exact mergeLoMemoryEventFree_tempToMainCell _ _ _
  · exact mergeLoMemoryEventFree_failure

private theorem mergeLoMemoryEventFree_gallopRound
    (machine : MergeLoMachine κ ν)
    (next : MergeLoMachine κ ν → Nat → Nat →
      TraceResult (MergeLoResult κ ν))
    (hnext : ∀ machine aCount bCount,
      MergeLoMemoryEventFree (next machine aCount bCount)) :
    MergeLoMemoryEventFree (mergeLoGallopRoundTraced? machine next) := by
  unfold mergeLoGallopRoundTraced?
  split
  · exact mergeLoMemoryEventFree_failure
  · dsimp only
    apply mergeLoMemoryEventFree_bind
    · exact mergeLoMemoryEventFree_keyRead _ _
    · intro firstB
      apply mergeLoMemoryEventFree_bind
      · exact mergeLoMemoryEventFree_traceOption _
      · intro _activeA
        apply mergeLoMemoryEventFree_bind
        · exact mergeLoMemoryEventFree_gallopRight _ _ _ _ _
        · intro gallopA
          split
          · exact mergeLoMemoryEventFree_fuelFailure _
          · split
            · exact mergeLoMemoryEventFree_failure
            · apply mergeLoMemoryEventFree_bind
              · exact mergeLoMemoryEventFree_tempToMainMemcpy _ _ _ _ _ _
              · intro state
                split
                · exact mergeLoMemoryEventFree_succeed _
                · split
                  · exact mergeLoMemoryEventFree_copyB _
                  · apply mergeLoMemoryEventFree_bind
                    · exact mergeLoMemoryEventFree_copyBIncr _
                    · intro afterB
                      split
                      · exact mergeLoMemoryEventFree_succeed _
                      · apply mergeLoMemoryEventFree_bind
                        · exact mergeLoMemoryEventFree_tempRead _ _
                        · intro firstA
                          apply mergeLoMemoryEventFree_bind
                          · exact mergeLoMemoryEventFree_gallopLeft _ _ _ _ _
                          · intro gallopB
                            split
                            · exact mergeLoMemoryEventFree_fuelFailure _
                            · split
                              · exact mergeLoMemoryEventFree_failure
                              · apply mergeLoMemoryEventFree_bind
                                · exact mergeLoMemoryEventFree_mainDataMemmove _ _ _ _
                                · intro movedState
                                  split
                                  · exact mergeLoMemoryEventFree_succeed _
                                  · apply mergeLoMemoryEventFree_bind
                                    · exact mergeLoMemoryEventFree_copyAIncr _
                                    · intro afterA
                                      split
                                      · exact mergeLoMemoryEventFree_copyB _
                                      · exact hnext _ _ _

private theorem mergeLoMemoryEventFree_loop
    (fuel : Nat) (machine : MergeLoMachine κ ν) (phase : MergeLoPhase) :
    MergeLoMemoryEventFree (mergeLoLoopTraced? fuel machine phase) := by
  induction fuel generalizing machine phase with
  | zero =>
      cases phase <;> exact mergeLoMemoryEventFree_fuelFailure _
  | succ fuel ih =>
      cases phase with
      | ordinary aCount bCount =>
          simp only [mergeLoLoopTraced?]
          split
          · exact mergeLoMemoryEventFree_failure
          · apply mergeLoMemoryEventFree_bind
            · exact mergeLoMemoryEventFree_tempRead _ _
            · intro firstA
              apply mergeLoMemoryEventFree_bind
              · exact mergeLoMemoryEventFree_keyRead _ _
              · intro firstB
                split
                · apply mergeLoMemoryEventFree_bind
                  · exact mergeLoMemoryEventFree_copyBIncr _
                  · intro afterB
                    split
                    · exact mergeLoMemoryEventFree_succeed _
                    · split
                      · exact ih _ _
                      · exact ih _ _
                · apply mergeLoMemoryEventFree_bind
                  · exact mergeLoMemoryEventFree_copyAIncr _
                  · intro afterA
                    split
                    · exact mergeLoMemoryEventFree_copyB _
                    · split
                      · exact ih _ _
                      · exact ih _ _
      | galloping =>
          simp only [mergeLoLoopTraced?]
          apply mergeLoMemoryEventFree_gallopRound
          intro nextMachine aCount bCount
          split
          · exact ih _ _
          · exact ih _ _

private theorem mergeLoTraced_topLevelEvents_empty
    (state : MergeState κ ν) (ssa ssb : Int) (na nb : Nat) :
    MergeLoMemoryEventFree (mergeLoTraced? state ssa ssb na nb) := by
  unfold mergeLoTraced?
  split
  · dsimp only
    split
    · exact mergeLoMemoryEventFree_pure _
    · apply mergeLoMemoryEventFree_bind
      · exact mergeLoMemoryEventFree_mainToTempMemcpy _ _ _ _ _ _
      · intro copied
        apply mergeLoMemoryEventFree_bind
        · exact mergeLoMemoryEventFree_copyBIncr _
        · intro first
          split
          · exact mergeLoMemoryEventFree_succeed _
          · split
            · exact mergeLoMemoryEventFree_copyB _
            · exact mergeLoMemoryEventFree_loop _ _ _
  · exact mergeLoMemoryEventFree_failure

/-- A raw directional `merge_lo` emits no top-level merge-memory event.  The
single call-boundary event is therefore owned by the `merge_at` wrapper. -/
theorem mergeLoTraced_memoryEvents_empty
    (state : MergeState κ ν) (ssa ssb : Int) (na nb : Nat) :
    (mergeLoTraced? state ssa ssb na nb).trace.memoryEvents = [] :=
  (mergeLoTraced_topLevelEvents_empty state ssa ssb na nb).1

/-- A raw directional `merge_lo` emits no merge-policy event.  Its enclosing
`merge_at` invocation owns the unique logical merge event, recorded before
the trimming gallops. -/
theorem mergeLoTraced_policyEvents_empty
    (state : MergeState κ ν) (ssa ssb : Int) (na nb : Nat) :
    (mergeLoTraced? state ssa ssb na nb).trace.policyEvents = [] :=
  (mergeLoTraced_topLevelEvents_empty state ssa ssb na nb).2

/-! ## Local exact erasure -/

@[simp]
theorem erase_mergeLoFuelFailureTraced (machine : MergeLoMachine κ ν) :
    (mergeLoFuelFailureTraced machine).erase =
      mergeLoGallopFuelFailure machine := by
  rfl

@[simp]
theorem erase_mergeLoCopyAIncrTraced (machine : MergeLoMachine κ ν) :
    (mergeLoCopyAIncrTraced? machine).erase =
      mergeLoCopyAIncr? machine := by
  rw [mergeLoCopyAIncrTraced?, TraceResult.erase_map,
    erase_tempToMainCellTraced]
  unfold tempToMainCell? mergeLoCopyAIncr?
  rw [mergeTempRead_ofNat]
  cases hread : mergeLoTempRead? machine.state.a machine.aPos with
  | none => simp
  | some entry =>
      cases hwrite : machine.state.data.write? machine.dest entry <;>
        simp [hwrite]

@[simp]
theorem erase_mergeLoCopyBIncrTraced (machine : MergeLoMachine κ ν) :
    (mergeLoCopyBIncrTraced? machine).erase =
      mergeLoCopyBIncr? machine := by
  rw [mergeLoCopyBIncrTraced?, TraceResult.erase_map,
    erase_mainDataMemmoveTraced]
  unfold mainDataMemmove? SortSlice.memmove? mergeLoCopyBIncr?
  split <;>
    simp [SortSlice.memmoveForward?, SortSlice.memmoveBackward?,
      SortSlice.copy?, SortSlice.copyFrom?, Option.bind_assoc]

@[simp]
theorem erase_mergeLoSucceedTraced (machine : MergeLoMachine κ ν) :
    (mergeLoSucceedTraced? machine).erase = mergeLoSucceed? machine := by
  rw [mergeLoSucceedTraced?, TraceResult.erase_map,
    erase_tempToMainMemcpyTraced,
    tempToMainMemcpy_eq_mergeLo .finalTempToData rfl]
  cases hcopy : mergeLoMemcpyTempToData? .finalTempToData rfl machine.na
      machine.state machine.dest machine.aPos <;>
    simp [mergeLoSucceed?, hcopy]

@[simp]
theorem erase_mergeLoCopyBTraced (machine : MergeLoMachine κ ν) :
    (mergeLoCopyBTraced? machine).erase = mergeLoCopyB? machine := by
  unfold mergeLoCopyBTraced? mergeLoCopyB?
  simp only [mergeDataMemmove_eq]
  split
  · rw [TraceResult.erase_bind, erase_mainDataMemmoveTraced]
    unfold mainDataMemmove?
    cases hmove : machine.state.data.memmove? machine.dest machine.bPos
        machine.nb with
    | none => simp
    | some data =>
        simp only [bind, Option.bind, pure]
        rw [TraceResult.erase_map, erase_tempToMainCellTraced]
        unfold tempToMainCell?
        rw [mergeTempRead_ofNat]
        cases hread : mergeLoTempRead? machine.state.a machine.aPos with
        | none => simp
        | some entry =>
            simp only [bind, Option.bind, pure]
            cases hwrite : data.write?
                (machine.dest + Int.ofNat machine.nb) entry with
            | none => rfl
            | some updated => rfl
  · rfl

/-! ## Public safety vocabulary -/

/-- State fields that `merge_lo` is not allowed to mutate.  `min_gallop` is
intentionally absent; it is the merge's adaptive output. -/
structure MergeLoStableFrame (before after : MergeState κ ν) : Prop where
  listlen : after.listlen = before.listlen
  basekeys : after.basekeys = before.basekeys
  dataSize : after.data.entries.size = before.data.entries.size
  tempValuesMode : after.a.hasValues = before.a.hasValues
  pending : after.pending = before.pending
  comparator : after.key_compare = before.key_compare
  mrCurrent : after.mr_current = before.mr_current
  mrE : after.mr_e = before.mr_e
  mrMask : after.mr_mask = before.mr_mask

namespace MergeLoStableFrame

theorem refl (state : MergeState κ ν) : MergeLoStableFrame state state := by
  constructor <;> rfl

theorem trans {first second third : MergeState κ ν}
    (hfirst : MergeLoStableFrame first second)
    (hsecond : MergeLoStableFrame second third) :
    MergeLoStableFrame first third := by
  constructor
  · exact hsecond.listlen.trans hfirst.listlen
  · exact hsecond.basekeys.trans hfirst.basekeys
  · exact hsecond.dataSize.trans hfirst.dataSize
  · exact hsecond.tempValuesMode.trans hfirst.tempValuesMode
  · exact hsecond.pending.trans hfirst.pending
  · exact hsecond.comparator.trans hfirst.comparator
  · exact hsecond.mrCurrent.trans hfirst.mrCurrent
  · exact hsecond.mrE.trans hfirst.mrE
  · exact hsecond.mrMask.trans hfirst.mrMask

theorem of_movement {before after : MergeState κ ν}
    (hframe : MergeMovementFrame before after) :
    MergeLoStableFrame before after := by
  exact
    { listlen := hframe.listlen
      basekeys := hframe.basekeys
      dataSize := hframe.dataSize
      tempValuesMode := hframe.tempValuesMode
      pending := hframe.pending
      comparator := hframe.comparator
      mrCurrent := hframe.mrCurrent
      mrE := hframe.mrE
      mrMask := hframe.mrMask }

theorem of_getmem (before : MergeState κ ν) (need : PySSize)
    (post : MergeGetmemStoragePost before need (mergeGetmem before need)) :
    MergeLoStableFrame before (mergeGetmem before need).state := by
  rcases post.minrun_eq with ⟨hmrCurrent, hmrE, hmrMask⟩
  exact
    { listlen := post.listlen_eq
      basekeys := post.basekeys_eq
      dataSize := by rw [post.data_eq]
      tempValuesMode := post.valuesMode
      pending := post.pending_eq
      comparator := post.keyCompare_eq
      mrCurrent := hmrCurrent
      mrE := hmrE
      mrMask := hmrMask }

end MergeLoStableFrame

/-- Exact temporary-storage metadata preserved after `merge_getmem` has
selected the backing used by `merge_lo`.  Payload cells may change during the
initial main-to-temporary copy, so this frame deliberately records their
extent rather than their contents. -/
structure MergeLoStorageFrame (before after : MergeState κ ν) : Prop where
  cellsSize : after.a.cells.size = before.a.cells.size
  backing : after.a.backing = before.a.backing
  hasValues : after.a.hasValues = before.a.hasValues
  alloced : after.alloced = before.alloced

namespace MergeLoStorageFrame

theorem refl (state : MergeState κ ν) : MergeLoStorageFrame state state := by
  constructor <;> rfl

theorem trans {first second third : MergeState κ ν}
    (hfirst : MergeLoStorageFrame first second)
    (hsecond : MergeLoStorageFrame second third) :
    MergeLoStorageFrame first third := by
  exact
    { cellsSize := hsecond.cellsSize.trans hfirst.cellsSize
      backing := hsecond.backing.trans hfirst.backing
      hasValues := hsecond.hasValues.trans hfirst.hasValues
      alloced := hsecond.alloced.trans hfirst.alloced }

theorem of_movement {before after : MergeState κ ν}
    (hframe : MergeMovementFrame before after) :
    MergeLoStorageFrame before after :=
  { cellsSize := hframe.tempSize
    backing := hframe.tempBacking
    hasValues := hframe.tempValuesMode
    alloced := hframe.alloced }

/-- Physical pointer-slot accounting is exactly framed by the four exported
metadata equalities. -/
theorem physicalSlots_eq {before after : MergeState κ ν}
    (hframe : MergeLoStorageFrame before after) :
    after.a.physicalSlots = before.a.physicalSlots := by
  simp only [TempStorage.physicalSlots, TempStorage.multiplier]
  rw [hframe.cellsSize, hframe.hasValues]

end MergeLoStorageFrame

/-- Inductive invariant for every live left-to-right merge machine.  The three
cursor equalities are the exact arithmetic preserved by cell and block moves. -/
structure MergeLoMachineInvariant (origin : MergeState κ ν)
    (tempTotal : Nat) (endIndex : Int) (machine : MergeLoMachine κ ν) : Prop where
  destNonnegative : 0 ≤ machine.dest
  tempAccounting : machine.aPos + machine.na = tempTotal
  adjacency : machine.dest + Int.ofNat machine.na = machine.bPos
  rightAccounting : machine.bPos + Int.ofNat machine.nb = endIndex
  mainEnd : endIndex ≤ Int.ofNat machine.state.data.entries.size
  leftWordBound : machine.na ≤ PY_LIST_MAX
  rightWordBound : machine.nb ≤ PY_LIST_MAX
  tempCapacity : tempTotal ≤ machine.state.a.cells.size
  tempValuesMode : TempRangeValuesMode machine.state.a 0 tempTotal
  tempInvariant : TempStorageInv machine.state.a machine.state.alloced
  tempLive : machine.state.a.Live
  valuesMode :
    SortSlice.ValuesModeInvariant machine.state.a.hasValues machine.state.data
  stableFrame : MergeLoStableFrame origin machine.state
  storageFrame : MergeLoStorageFrame origin machine.state

/-- The loop fuel stays strictly ahead of the number of unmerged cells. -/
def MergeLoFuelInvariant (fuel : Nat) (machine : MergeLoMachine κ ν) : Prop :=
  machine.na + machine.nb < fuel

namespace MergeLoMachineInvariant

theorem aPosInBounds {origin : MergeState κ ν} {tempTotal : Nat}
    {endIndex : Int} {machine : MergeLoMachine κ ν}
    (h : MergeLoMachineInvariant origin tempTotal endIndex machine)
    (hna : 0 < machine.na) :
    TempIndexInBounds machine.state.a (Int.ofNat machine.aPos) := by
  constructor
  · exact Int.natCast_nonneg _
  · apply Int.ofNat_lt.mpr
    have haccounting := h.tempAccounting
    have hcapacity := h.tempCapacity
    omega

theorem tempReadable {origin : MergeState κ ν} {tempTotal : Nat}
    {endIndex : Int} {machine : MergeLoMachine κ ν}
    (h : MergeLoMachineInvariant origin tempTotal endIndex machine)
    (hna : 0 < machine.na) :
    ∃ entry, mergeTempRead? machine.state.a (Int.ofNat machine.aPos) = some entry := by
  have haPos : machine.aPos < tempTotal := by
    have haccounting := h.tempAccounting
    omega
  rcases h.tempValuesMode machine.aPos haPos with ⟨entry, hread, _⟩
  refine ⟨entry, ?_⟩
  rw [erase_mergeTempRead] at hread
  simpa only [zero_add] using hread

theorem tempActiveInBounds {origin : MergeState κ ν} {tempTotal : Nat}
    {endIndex : Int} {machine : MergeLoMachine κ ν}
    (h : MergeLoMachineInvariant origin tempTotal endIndex machine) :
    TempRangeInBounds machine.state.a (Int.ofNat machine.aPos) machine.na := by
  constructor
  · exact Int.natCast_nonneg _
  · have hbound : machine.aPos + machine.na ≤
        machine.state.a.cells.size := by
      have haccounting := h.tempAccounting
      have hcapacity := h.tempCapacity
      omega
    simpa only [Int.ofNat_eq_natCast, Nat.cast_add] using Int.ofNat_le.mpr hbound

theorem tempActiveValuesMode {origin : MergeState κ ν} {tempTotal : Nat}
    {endIndex : Int} {machine : MergeLoMachine κ ν}
    (h : MergeLoMachineInvariant origin tempTotal endIndex machine) :
    TempRangeValuesMode machine.state.a (Int.ofNat machine.aPos) machine.na := by
  intro offset hoffset
  have hfull : machine.aPos + offset < tempTotal := by
    have haccounting := h.tempAccounting
    omega
  rcases h.tempValuesMode (machine.aPos + offset) hfull with
    ⟨entry, hread, hentryMode⟩
  refine ⟨entry, ?_, hentryMode⟩
  simpa only [zero_add, Int.ofNat_eq_natCast, Nat.cast_add] using hread

theorem temporaryValidRange {origin : MergeState κ ν} {tempTotal : Nat}
    {endIndex : Int} {machine : MergeLoMachine κ ν}
    (h : MergeLoMachineInvariant origin tempTotal endIndex machine) :
    (GallopKeySource.temporary machine.state.a
      (Int.ofNat machine.aPos)).ValidRange machine.na :=
  mergeLoTemporary_validRange machine.state.a machine.aPos machine.na
    (by
      have haccounting := h.tempAccounting
      have hcapacity := h.tempCapacity
      omega) (by
      intro i hi
      rcases h.tempActiveValuesMode i hi with ⟨entry, hread, _⟩
      refine ⟨entry, ?_⟩
      rw [erase_mergeTempRead] at hread
      have hsum : Int.ofNat machine.aPos + Int.ofNat i =
          Int.ofNat (machine.aPos + i) := by
        simp only [Int.ofNat_eq_natCast, Nat.cast_add]
      rw [hsum, mergeTempRead_ofNat] at hread
      exact hread)

theorem bPosInBounds {origin : MergeState κ ν} {tempTotal : Nat}
    {endIndex : Int} {machine : MergeLoMachine κ ν}
    (h : MergeLoMachineInvariant origin tempTotal endIndex machine)
    (hnb : 0 < machine.nb) :
    SortSlice.IndexInBounds machine.state.data machine.bPos := by
  have hadjacent := h.adjacency
  have hdest := h.destNonnegative
  have hright := h.rightAccounting
  have hend := h.mainEnd
  rw [SortSlice.IndexInBounds]
  simp only [Int.ofNat_eq_natCast] at hadjacent hright hend ⊢
  constructor <;> omega

theorem destInBounds {origin : MergeState κ ν} {tempTotal : Nat}
    {endIndex : Int} {machine : MergeLoMachine κ ν}
    (h : MergeLoMachineInvariant origin tempTotal endIndex machine)
    (hactive : 0 < machine.na + machine.nb) :
    SortSlice.IndexInBounds machine.state.data machine.dest := by
  have hadjacent := h.adjacency
  have hright := h.rightAccounting
  have hend := h.mainEnd
  rw [SortSlice.IndexInBounds]
  simp only [Int.ofNat_eq_natCast] at hadjacent hright hend ⊢
  constructor
  · exact h.destNonnegative
  · omega

theorem rightValidRange {origin : MergeState κ ν} {tempTotal : Nat}
    {endIndex : Int} {machine : MergeLoMachine κ ν}
    (h : MergeLoMachineInvariant origin tempTotal endIndex machine) :
    (GallopKeySource.main machine.state.data machine.bPos).ValidRange machine.nb := by
  have hadjacent := h.adjacency
  have hright := h.rightAccounting
  have hend := h.mainEnd
  have hdest := h.destNonnegative
  simp only [Int.ofNat_eq_natCast] at hadjacent hright hend
  refine ⟨by
    simp only [GallopKeySource.base]
    omega, ?_, ?_⟩
  · simp only [GallopKeySource.base, GallopKeySource.extent]
    exact hright.trans_le hend
  · intro offset hoffset
    have hindex : SortSlice.IndexInBounds machine.state.data
        (machine.bPos + Int.ofNat offset) := by
      rw [SortSlice.IndexInBounds]
      constructor
      · exact add_nonneg (by omega) (Int.natCast_nonneg _)
      · calc
          machine.bPos + Int.ofNat offset <
              machine.bPos + Int.ofNat machine.nb := by
                simpa [add_comm] using
                  (add_lt_add_left (Int.ofNat_lt.mpr hoffset) machine.bPos)
          _ = endIndex := h.rightAccounting
          _ ≤ Int.ofNat machine.state.data.entries.size := h.mainEnd
    rcases SortSlice.read_eq_some_of_indexInBounds machine.state.data _ hindex with
      ⟨entry, hentry⟩
    exact ⟨entry, by
      simpa only [GallopKeySource.read?, GallopKeySource.base] using hentry⟩

theorem destRange {origin : MergeState κ ν} {tempTotal : Nat}
    {endIndex : Int} {machine : MergeLoMachine κ ν}
    (h : MergeLoMachineInvariant origin tempTotal endIndex machine)
    (count : Nat) (hcount : count ≤ machine.na) :
    SortSlice.RangeInBounds machine.state.data machine.dest count := by
  constructor
  · exact h.destNonnegative
  · have hadj := h.adjacency
    have hright := h.rightAccounting
    have hend := h.mainEnd
    simp only [Int.ofNat_eq_natCast] at hadj hright hend ⊢
    have hcast : (count : Int) ≤ (machine.na : Int) := by exact_mod_cast hcount
    omega

theorem destTotalRange {origin : MergeState κ ν} {tempTotal : Nat}
    {endIndex : Int} {machine : MergeLoMachine κ ν}
    (h : MergeLoMachineInvariant origin tempTotal endIndex machine)
    (count : Nat) (hcount : count ≤ machine.na + machine.nb) :
    SortSlice.RangeInBounds machine.state.data machine.dest count := by
  constructor
  · exact h.destNonnegative
  · have hadj := h.adjacency
    have hright := h.rightAccounting
    have hend := h.mainEnd
    simp only [Int.ofNat_eq_natCast] at hadj hright hend ⊢
    have hcast : (count : Int) ≤ (machine.na + machine.nb : Nat) := by
      exact_mod_cast hcount
    omega

theorem rightRange {origin : MergeState κ ν} {tempTotal : Nat}
    {endIndex : Int} {machine : MergeLoMachine κ ν}
    (h : MergeLoMachineInvariant origin tempTotal endIndex machine)
    (count : Nat) (hcount : count ≤ machine.nb) :
    SortSlice.RangeInBounds machine.state.data machine.bPos count := by
  constructor
  · have hadj := h.adjacency
    simp only [Int.ofNat_eq_natCast] at hadj
    exact hadj ▸ add_nonneg h.destNonnegative (Int.natCast_nonneg _)
  · have hright := h.rightAccounting
    have hend := h.mainEnd
    simp only [Int.ofNat_eq_natCast] at hright hend ⊢
    have hcast : (count : Int) ≤ (machine.nb : Int) := by exact_mod_cast hcount
    omega

theorem tempPrefixInBounds {origin : MergeState κ ν} {tempTotal : Nat}
    {endIndex : Int} {machine : MergeLoMachine κ ν}
    (h : MergeLoMachineInvariant origin tempTotal endIndex machine)
    (count : Nat) (hcount : count ≤ machine.na) :
    TempRangeInBounds machine.state.a (Int.ofNat machine.aPos) count := by
  constructor
  · exact Int.natCast_nonneg _
  · have haccount := h.tempAccounting
    have hcapacity := h.tempCapacity
    simp only [Int.ofNat_eq_natCast] at ⊢
    have hcast : (count : Int) ≤ (machine.na : Int) := by exact_mod_cast hcount
    exact_mod_cast (show machine.aPos + count ≤ machine.state.a.cells.size by
      omega)

theorem tempPrefixValuesMode {origin : MergeState κ ν} {tempTotal : Nat}
    {endIndex : Int} {machine : MergeLoMachine κ ν}
    (h : MergeLoMachineInvariant origin tempTotal endIndex machine)
    (count : Nat) (hcount : count ≤ machine.na) :
    TempRangeValuesMode machine.state.a (Int.ofNat machine.aPos) count := by
  intro offset hoffset
  exact h.tempActiveValuesMode offset (by omega)

theorem replaceState {origin : MergeState κ ν} {tempTotal : Nat}
    {endIndex : Int} {machine : MergeLoMachine κ ν}
    (h : MergeLoMachineInvariant origin tempTotal endIndex machine)
    (after : MergeState κ ν) (hframe : MergeMovementFrame machine.state after)
    (htemp : after.a = machine.state.a)
    (hmode : SortSlice.ValuesModeInvariant after.a.hasValues after.data) :
    MergeLoMachineInvariant origin tempTotal endIndex
      { machine with state := after } := by
  exact
    { destNonnegative := h.destNonnegative
      tempAccounting := h.tempAccounting
      adjacency := h.adjacency
      rightAccounting := h.rightAccounting
      mainEnd := by simpa only [hframe.dataSize] using h.mainEnd
      leftWordBound := h.leftWordBound
      rightWordBound := h.rightWordBound
      tempCapacity := by simpa only [htemp] using h.tempCapacity
      tempValuesMode := by simpa only [htemp] using h.tempValuesMode
      tempInvariant := hframe.tempStorageInv h.tempInvariant
      tempLive := hframe.live h.tempLive
      valuesMode := hmode
      stableFrame := h.stableFrame.trans (.of_movement hframe)
      storageFrame := h.storageFrame.trans (.of_movement hframe) }

theorem setMinGallop {origin : MergeState κ ν} {tempTotal : Nat}
    {endIndex : Int} {machine : MergeLoMachine κ ν}
    (h : MergeLoMachineInvariant origin tempTotal endIndex machine)
    (minGallop : PySSize) :
    MergeLoMachineInvariant origin tempTotal endIndex
      { machine with
        state := { machine.state with min_gallop := minGallop }
        minGallop := minGallop } := by
  exact
    { destNonnegative := h.destNonnegative
      tempAccounting := h.tempAccounting
      adjacency := h.adjacency
      rightAccounting := h.rightAccounting
      mainEnd := h.mainEnd
      leftWordBound := h.leftWordBound
      rightWordBound := h.rightWordBound
      tempCapacity := h.tempCapacity
      tempValuesMode := h.tempValuesMode
      tempInvariant := h.tempInvariant
      tempLive := h.tempLive
      valuesMode := h.valuesMode
      stableFrame :=
        { listlen := h.stableFrame.listlen
          basekeys := h.stableFrame.basekeys
          dataSize := h.stableFrame.dataSize
          tempValuesMode := h.stableFrame.tempValuesMode
          pending := h.stableFrame.pending
          comparator := h.stableFrame.comparator
          mrCurrent := h.stableFrame.mrCurrent
          mrE := h.stableFrame.mrE
          mrMask := h.stableFrame.mrMask }
      storageFrame :=
        { cellsSize := h.storageFrame.cellsSize
          backing := h.storageFrame.backing
          hasValues := h.storageFrame.hasValues
          alloced := h.storageFrame.alloced } }

theorem setMachineMinGallop {origin : MergeState κ ν} {tempTotal : Nat}
    {endIndex : Int} {machine : MergeLoMachine κ ν}
    (h : MergeLoMachineInvariant origin tempTotal endIndex machine)
    (minGallop : PySSize) :
    MergeLoMachineInvariant origin tempTotal endIndex
      { machine with minGallop := minGallop } := by
  exact
    { destNonnegative := h.destNonnegative
      tempAccounting := h.tempAccounting
      adjacency := h.adjacency
      rightAccounting := h.rightAccounting
      mainEnd := h.mainEnd
      leftWordBound := h.leftWordBound
      rightWordBound := h.rightWordBound
      tempCapacity := h.tempCapacity
      tempValuesMode := h.tempValuesMode
      tempInvariant := h.tempInvariant
      tempLive := h.tempLive
      valuesMode := h.valuesMode
      stableFrame := h.stableFrame
      storageFrame := h.storageFrame }

theorem copyA {origin : MergeState κ ν} {tempTotal : Nat}
    {endIndex : Int} {machine : MergeLoMachine κ ν}
    (h : MergeLoMachineInvariant origin tempTotal endIndex machine)
    (after : MergeState κ ν) (hframe : MergeMovementFrame machine.state after)
    (htemp : after.a = machine.state.a)
    (hmode : SortSlice.ValuesModeInvariant after.a.hasValues after.data)
    (hna : 0 < machine.na) :
    MergeLoMachineInvariant origin tempTotal endIndex
      { machine with
        state := after
        dest := machine.dest + 1
        aPos := machine.aPos + 1
        na := machine.na - 1 } := by
  have hs := h.replaceState after hframe htemp hmode
  exact
    { destNonnegative := by
        change 0 ≤ machine.dest + 1
        exact add_nonneg h.destNonnegative (by omega)
      tempAccounting := by
        change machine.aPos + 1 + (machine.na - 1) = tempTotal
        have := h.tempAccounting
        omega
      adjacency := by
        have hadjacent := h.adjacency
        simp only [Int.ofNat_eq_natCast, Nat.cast_sub hna] at hadjacent ⊢
        omega
      rightAccounting := h.rightAccounting
      mainEnd := hs.mainEnd
      leftWordBound := by
        change machine.na - 1 ≤ PY_LIST_MAX
        exact (Nat.sub_le machine.na 1).trans h.leftWordBound
      rightWordBound := h.rightWordBound
      tempCapacity := hs.tempCapacity
      tempValuesMode := hs.tempValuesMode
      tempInvariant := hs.tempInvariant
      tempLive := hs.tempLive
      valuesMode := hs.valuesMode
      stableFrame := hs.stableFrame
      storageFrame := hs.storageFrame }

theorem copyB {origin : MergeState κ ν} {tempTotal : Nat}
    {endIndex : Int} {machine : MergeLoMachine κ ν}
    (h : MergeLoMachineInvariant origin tempTotal endIndex machine)
    (after : MergeState κ ν) (hframe : MergeMovementFrame machine.state after)
    (htemp : after.a = machine.state.a)
    (hmode : SortSlice.ValuesModeInvariant after.a.hasValues after.data)
    (hnb : 0 < machine.nb) :
    MergeLoMachineInvariant origin tempTotal endIndex
      { machine with
        state := after
        dest := machine.dest + 1
        bPos := machine.bPos + 1
        nb := machine.nb - 1 } := by
  have hs := h.replaceState after hframe htemp hmode
  exact
    { destNonnegative := by
        change 0 ≤ machine.dest + 1
        exact add_nonneg h.destNonnegative (by omega)
      tempAccounting := h.tempAccounting
      adjacency := by
        have hadjacent := h.adjacency
        simp only [Int.ofNat_eq_natCast] at hadjacent ⊢
        omega
      rightAccounting := by
        have hright := h.rightAccounting
        simp only [Int.ofNat_eq_natCast, Nat.cast_sub hnb] at hright ⊢
        omega
      mainEnd := hs.mainEnd
      leftWordBound := h.leftWordBound
      rightWordBound := by
        change machine.nb - 1 ≤ PY_LIST_MAX
        exact (Nat.sub_le machine.nb 1).trans h.rightWordBound
      tempCapacity := hs.tempCapacity
      tempValuesMode := hs.tempValuesMode
      tempInvariant := hs.tempInvariant
      tempLive := hs.tempLive
      valuesMode := hs.valuesMode
      stableFrame := hs.stableFrame
      storageFrame := hs.storageFrame }

theorem copyABlock {origin : MergeState κ ν} {tempTotal : Nat}
    {endIndex : Int} {machine : MergeLoMachine κ ν}
    (h : MergeLoMachineInvariant origin tempTotal endIndex machine)
    (count : Nat) (hcount : count ≤ machine.na)
    (after : MergeState κ ν) (hframe : MergeMovementFrame machine.state after)
    (htemp : after.a = machine.state.a)
    (hmode : SortSlice.ValuesModeInvariant after.a.hasValues after.data) :
    MergeLoMachineInvariant origin tempTotal endIndex
      { machine with
        state := after
        dest := machine.dest + Int.ofNat count
        aPos := machine.aPos + count
        na := machine.na - count } := by
  have hs := h.replaceState after hframe htemp hmode
  exact
    { destNonnegative := add_nonneg h.destNonnegative (Int.natCast_nonneg _)
      tempAccounting := by
        change machine.aPos + count + (machine.na - count) = tempTotal
        have := h.tempAccounting
        omega
      adjacency := by
        have hadjacent := h.adjacency
        simp only [Int.ofNat_eq_natCast, Nat.cast_sub hcount]
          at hadjacent ⊢
        omega
      rightAccounting := h.rightAccounting
      mainEnd := hs.mainEnd
      leftWordBound := by
        change machine.na - count ≤ PY_LIST_MAX
        exact (Nat.sub_le machine.na count).trans h.leftWordBound
      rightWordBound := h.rightWordBound
      tempCapacity := hs.tempCapacity
      tempValuesMode := hs.tempValuesMode
      tempInvariant := hs.tempInvariant
      tempLive := hs.tempLive
      valuesMode := hs.valuesMode
      stableFrame := hs.stableFrame
      storageFrame := hs.storageFrame }

theorem copyBBlock {origin : MergeState κ ν} {tempTotal : Nat}
    {endIndex : Int} {machine : MergeLoMachine κ ν}
    (h : MergeLoMachineInvariant origin tempTotal endIndex machine)
    (count : Nat) (hcount : count ≤ machine.nb)
    (after : MergeState κ ν) (hframe : MergeMovementFrame machine.state after)
    (htemp : after.a = machine.state.a)
    (hmode : SortSlice.ValuesModeInvariant after.a.hasValues after.data) :
    MergeLoMachineInvariant origin tempTotal endIndex
      { machine with
        state := after
        dest := machine.dest + Int.ofNat count
        bPos := machine.bPos + Int.ofNat count
        nb := machine.nb - count } := by
  have hs := h.replaceState after hframe htemp hmode
  exact
    { destNonnegative := add_nonneg h.destNonnegative (Int.natCast_nonneg _)
      tempAccounting := h.tempAccounting
      adjacency := by
        have hadjacent := h.adjacency
        simp only [Int.ofNat_eq_natCast] at hadjacent ⊢
        omega
      rightAccounting := by
        have hright := h.rightAccounting
        simp only [Int.ofNat_eq_natCast, Nat.cast_sub hcount] at hright ⊢
        omega
      mainEnd := hs.mainEnd
      leftWordBound := h.leftWordBound
      rightWordBound := by
        change machine.nb - count ≤ PY_LIST_MAX
        exact (Nat.sub_le machine.nb count).trans h.rightWordBound
      tempCapacity := hs.tempCapacity
      tempValuesMode := hs.tempValuesMode
      tempInvariant := hs.tempInvariant
      tempLive := hs.tempLive
      valuesMode := hs.valuesMode
      stableFrame := hs.stableFrame
      storageFrame := hs.storageFrame }

end MergeLoMachineInvariant

/-! ## Concrete adversarial-comparator hedge fixtures -/

/-- The concrete non-irreflexive-comparator machine used by
`mergeLo_inconsistentComparator_naZero_succeed_regression` satisfies the full
assembly invariant, not merely the cursor arithmetic visible in the
transcription fixture. -/
theorem mergeLoNaZeroHedgeRegressionMachine_invariant :
    MergeLoMachineInvariant mergeLoNaZeroHedgeRegressionState 2 3
      mergeLoNaZeroHedgeRegressionMachine := by
  refine
    { destNonnegative := by decide
      tempAccounting := by decide
      adjacency := by decide
      rightAccounting := by decide
      mainEnd := by decide
      leftWordBound := by decide
      rightWordBound := by decide
      tempCapacity := by decide
      tempValuesMode := ?_
      tempInvariant := by
        have hcapacity : 4 ≤ MERGESTATE_TEMP_SIZE := by decide
        simpa [mergeLoNaZeroHedgeRegressionMachine,
          mergeLoNaZeroHedgeRegressionState, TempStorageInv,
          TempStorage.multiplier] using hcapacity
      tempLive := by
        simp [mergeLoNaZeroHedgeRegressionMachine,
          mergeLoNaZeroHedgeRegressionState, TempStorage.Live]
      valuesMode := ?_
      stableFrame := ?_
      storageFrame := ?_ }
  · intro index hindex
    have hindex' : index < 2 := by
      simpa [mergeLoNaZeroHedgeRegressionMachine,
        mergeLoNaZeroHedgeRegressionState] using hindex
    interval_cases index <;>
      simp [mergeLoNaZeroHedgeRegressionMachine,
        mergeLoNaZeroHedgeRegressionState,
        SortSlice.EntryMatchesValuesMode]
  · intro index hindex
    have hindex' : index < 3 := by
      simpa [mergeLoNaZeroHedgeRegressionMachine,
        mergeLoNaZeroHedgeRegressionState] using hindex
    interval_cases index <;>
      simp [mergeLoNaZeroHedgeRegressionMachine,
        mergeLoNaZeroHedgeRegressionState,
        SortSlice.EntryMatchesValuesMode]
  · simpa [mergeLoNaZeroHedgeRegressionMachine] using
      MergeLoStableFrame.refl mergeLoNaZeroHedgeRegressionState
  · simpa [mergeLoNaZeroHedgeRegressionMachine] using
      MergeLoStorageFrame.refl mergeLoNaZeroHedgeRegressionState

/-- Changing only the comparator to strict `<` preserves the full assembly
invariant of the `merge_lo` hedge-regression geometry. -/
theorem mergeLoNaZeroHedgeStrictControlMachine_invariant :
    MergeLoMachineInvariant mergeLoNaZeroHedgeStrictControlState 2 3
      mergeLoNaZeroHedgeStrictControlMachine := by
  refine
    { destNonnegative := by decide
      tempAccounting := by decide
      adjacency := by decide
      rightAccounting := by decide
      mainEnd := by decide
      leftWordBound := by decide
      rightWordBound := by decide
      tempCapacity := by decide
      tempValuesMode := ?_
      tempInvariant := by
        have hcapacity : 4 ≤ MERGESTATE_TEMP_SIZE := by decide
        simpa [mergeLoNaZeroHedgeStrictControlMachine,
          mergeLoNaZeroHedgeStrictControlState,
          mergeLoNaZeroHedgeRegressionMachine,
          mergeLoNaZeroHedgeRegressionState, TempStorageInv,
          TempStorage.multiplier] using hcapacity
      tempLive := by
        simp [mergeLoNaZeroHedgeStrictControlMachine,
          mergeLoNaZeroHedgeStrictControlState,
          mergeLoNaZeroHedgeRegressionMachine,
          mergeLoNaZeroHedgeRegressionState, TempStorage.Live]
      valuesMode := ?_
      stableFrame := ?_
      storageFrame := ?_ }
  · intro index hindex
    have hindex' : index < 2 := by
      simpa [mergeLoNaZeroHedgeStrictControlMachine,
        mergeLoNaZeroHedgeStrictControlState,
        mergeLoNaZeroHedgeRegressionMachine,
        mergeLoNaZeroHedgeRegressionState] using hindex
    interval_cases index <;>
      simp [mergeLoNaZeroHedgeStrictControlMachine,
        mergeLoNaZeroHedgeStrictControlState,
        mergeLoNaZeroHedgeRegressionMachine,
        mergeLoNaZeroHedgeRegressionState,
        SortSlice.EntryMatchesValuesMode]
  · intro index hindex
    have hindex' : index < 3 := by
      simpa [mergeLoNaZeroHedgeStrictControlMachine,
        mergeLoNaZeroHedgeStrictControlState,
        mergeLoNaZeroHedgeRegressionMachine,
        mergeLoNaZeroHedgeRegressionState] using hindex
    interval_cases index <;>
      simp [mergeLoNaZeroHedgeStrictControlMachine,
        mergeLoNaZeroHedgeStrictControlState,
        mergeLoNaZeroHedgeRegressionMachine,
        mergeLoNaZeroHedgeRegressionState,
        SortSlice.EntryMatchesValuesMode]
  · simpa [mergeLoNaZeroHedgeStrictControlMachine] using
      MergeLoStableFrame.refl mergeLoNaZeroHedgeStrictControlState
  · simpa [mergeLoNaZeroHedgeStrictControlMachine] using
      MergeLoStorageFrame.refl mergeLoNaZeroHedgeStrictControlState

/-! ## Internal lockstep postconditions -/

/-- Postcondition threaded through the terminal helpers and the recursive
driver.  Its reference argument is the exact reviewed fragment represented by
the traced execution. -/
structure MergeLoCorePost
    (origin : MergeState κ ν) (tempTotal : Nat)
    (execution : TraceResult (MergeLoResult κ ν))
    (reference : Option (MergeLoResult κ ν))
    (result : MergeLoResult κ ν) : Prop where
  resultEq : execution.result = some result
  returnCode : result.returnCode = 0
  resultFuel : result.fuelExhausted = false
  traceSafe : MovementTraceSafe execution
  exactErasure : execution.erase = reference
  tempCapacity : tempTotal ≤ result.state.a.cells.size
  tempInvariant : TempStorageInv result.state.a result.state.alloced
  tempLive : result.state.a.Live
  valuesMode :
    SortSlice.ValuesModeInvariant result.state.a.hasValues result.state.data
  stableFrame : MergeLoStableFrame origin result.state
  storageFrame : MergeLoStorageFrame origin result.state

private theorem mainDataMemmoveTraced_temp_eq_of_result
    (state result : MergeState κ ν) (dst src : Int) (count : Nat)
    (hresult : (mainDataMemmoveTraced? state dst src count).result =
      some result) :
    result.a = state.a := by
  unfold mainDataMemmoveTraced? at hresult
  cases hdata : (SortSlice.memmoveTraced? state.a.hasValues state.data dst src
      count).result with
  | none => simp [TraceResult.map, hdata] at hresult
  | some data =>
      simp [TraceResult.map, hdata] at hresult
      subst result
      rfl

namespace MergeLoCorePost

private theorem reference_eq
    (origin : MergeState κ ν) (tempTotal : Nat)
    (execution : TraceResult (MergeLoResult κ ν))
    (first second : Option (MergeLoResult κ ν))
    (result : MergeLoResult κ ν) (heq : first = second)
    (h : MergeLoCorePost origin tempTotal execution first result) :
    MergeLoCorePost origin tempTotal execution second result := by
  subst second
  exact h

/-- Prefix a successful, safe traced primitive to an already-proved
continuation.  The reference computation is prefixed by the erased primitive
in exactly the same way. -/
private theorem prepend
    (origin : MergeState κ ν) (tempTotal : Nat)
    (current : TraceResult α) (next : α → TraceResult (MergeLoResult κ ν))
    (reference : α → Option (MergeLoResult κ ν))
    (value : α) (result : MergeLoResult κ ν)
    (hcurrent : current.result = some value)
    (hcurrentSafe : MovementTraceSafe current)
    (hnext : MergeLoCorePost origin tempTotal (next value)
      (reference value) result) :
    MergeLoCorePost origin tempTotal (current.bind next)
      (current.erase.bind reference) result := by
  exact
    { resultEq := by
        simp [TraceResult.bind, hcurrent, hnext.resultEq]
      returnCode := hnext.returnCode
      resultFuel := hnext.resultFuel
      traceSafe := MovementTraceSafe.bind current next value hcurrent
        hcurrentSafe hnext.traceSafe
      exactErasure := by
        have herase : current.erase = some value := hcurrent
        rw [TraceResult.erase_bind, herase]
        exact hnext.exactErasure
      tempCapacity := hnext.tempCapacity
      tempInvariant := hnext.tempInvariant
      tempLive := hnext.tempLive
      valuesMode := hnext.valuesMode
      stableFrame := hnext.stableFrame
      storageFrame := hnext.storageFrame }

end MergeLoCorePost

private theorem mergeLoTempReadTraced_safe (storage : TempStorage κ ν)
    (index : Int) (hindex : TempIndexInBounds storage index)
    (hlive : storage.Live) :
    MovementTraceSafe (TraceResult.tempPayloadRead? storage index) := by
  constructor
  · simp [TraceResult.trace_tempPayloadRead, AccessTrace.singletonAccess]
  · simp [TraceResult.trace_tempPayloadRead, AccessTrace.singletonAccess]
  · rw [TraceResult.trace_tempPayloadRead]
    simpa [AccessTrace.allAccessesInBounds, AccessTrace.singletonAccess,
      AccessEvent.InBounds, TempIndexInBounds] using hindex
  · rw [TraceResult.trace_tempPayloadRead]
    simpa [AccessTrace.tempPayloadAccessesLive, AccessTrace.singletonAccess,
      AccessEvent.TempPayloadLive, TempStorage.Live] using hlive

private theorem mergeLoMainKeyReadTraced_safe (slice : SortSlice κ ν)
    (index : Int) (hindex : SortSlice.IndexInBounds slice index) :
    MovementTraceSafe (TraceResult.sortSliceKeysRead? slice index) := by
  constructor
  · simp [TraceResult.trace_sortSliceKeysRead, AccessTrace.singletonAccess]
  · simp [TraceResult.trace_sortSliceKeysRead, AccessTrace.singletonAccess]
  · rw [TraceResult.trace_sortSliceKeysRead]
    simpa [AccessTrace.allAccessesInBounds, AccessTrace.singletonAccess,
      AccessEvent.InBounds, SortSlice.IndexInBounds] using hindex
  · simp [TraceResult.trace_sortSliceKeysRead,
      AccessTrace.tempPayloadAccessesLive, AccessTrace.singletonAccess,
      AccessEvent.TempPayloadLive]

/-- A single main-data incrementing copy has the full movement contract needed
by the merge invariant. -/
theorem mergeLoCopyBIncrTraced_safe
    (origin : MergeState κ ν) (tempTotal : Nat) (endIndex : Int)
    (machine : MergeLoMachine κ ν)
    (hinvariant : MergeLoMachineInvariant origin tempTotal endIndex machine)
    (hna : 0 < machine.na) (hnb : 0 < machine.nb) :
    ∃ next,
      (mergeLoCopyBIncrTraced? machine).result = some next ∧
      MovementTraceSafe (mergeLoCopyBIncrTraced? machine) ∧
      MergeLoMachineInvariant origin tempTotal endIndex next ∧
      next.na = machine.na ∧ next.nb = machine.nb - 1 := by
  have hdestIndex := hinvariant.destInBounds (by omega)
  have hsourceIndex := hinvariant.bPosInBounds hnb
  have hdest : SortSlice.RangeInBounds machine.state.data machine.dest 1 := by
    rw [SortSlice.IndexInBounds] at hdestIndex
    simp only [Int.ofNat_eq_natCast] at hdestIndex ⊢
    constructor
    · exact hdestIndex.1
    · have hle : machine.dest + 1 ≤
          (machine.state.data.entries.size : Int) := by omega
      simpa [Int.ofNat_eq_natCast] using hle
  have hsource : SortSlice.RangeInBounds machine.state.data machine.bPos 1 := by
    rw [SortSlice.IndexInBounds] at hsourceIndex
    simp only [Int.ofNat_eq_natCast] at hsourceIndex ⊢
    constructor
    · exact hsourceIndex.1
    · have hle : machine.bPos + 1 ≤
          (machine.state.data.entries.size : Int) := by omega
      simpa [Int.ofNat_eq_natCast] using hle
  rcases mainDataMemmoveTraced_safe machine.state machine.dest machine.bPos 1
      hinvariant.tempInvariant hinvariant.tempLive hinvariant.valuesMode
      hdest hsource with ⟨state, hpost⟩
  let next : MergeLoMachine κ ν :=
    { machine with
      state := state
      dest := machine.dest + 1
      bPos := machine.bPos + 1
      nb := machine.nb - 1 }
  have htempEq := mainDataMemmoveTraced_temp_eq_of_result machine.state state
    machine.dest machine.bPos 1 hpost.success
  have hnextInv : MergeLoMachineInvariant origin tempTotal endIndex next := by
    exact hinvariant.copyB state hpost.frame htempEq hpost.valuesMode hnb
  refine ⟨next, ?_, ?_, hnextInv, rfl, rfl⟩
  · simp [mergeLoCopyBIncrTraced?, TraceResult.map, hpost.success, next]
  · exact MovementTraceSafe.map _ _ hpost.traceSafe

/-- A single temporary-to-main incrementing copy has the full movement
contract needed by the merge invariant. -/
theorem mergeLoCopyAIncrTraced_safe
    (origin : MergeState κ ν) (tempTotal : Nat) (endIndex : Int)
    (machine : MergeLoMachine κ ν)
    (hinvariant : MergeLoMachineInvariant origin tempTotal endIndex machine)
    (hna : 0 < machine.na) :
    ∃ next,
      (mergeLoCopyAIncrTraced? machine).result = some next ∧
      MovementTraceSafe (mergeLoCopyAIncrTraced? machine) ∧
      MergeLoMachineInvariant origin tempTotal endIndex next ∧
      next.na = machine.na - 1 ∧ next.nb = machine.nb := by
  have hdest := hinvariant.destInBounds (by omega)
  have htemp := hinvariant.aPosInBounds hna
  have hreadable := hinvariant.tempReadable hna
  rcases tempToMainCellTraced_safe machine.state machine.dest
      (Int.ofNat machine.aPos) hdest htemp hinvariant.tempLive hreadable with
    ⟨state, hstate, htraceSafe, hframe⟩
  have hcore : tempToMainCell? machine.state machine.dest
      (Int.ofNat machine.aPos) = some state := by
    rw [← erase_tempToMainCellTraced]
    exact hstate
  have htempEq := tempToMainCell_temp_eq_of_eq_some machine.state state
    machine.dest (Int.ofNat machine.aPos) hcore
  have hentryMode : ∀ entry,
      mergeTempRead? machine.state.a (Int.ofNat machine.aPos) = some entry →
        SortSlice.EntryMatchesValuesMode machine.state.a.hasValues entry := by
    intro entry hentry
    have haPos : machine.aPos < tempTotal := by
      have := hinvariant.tempAccounting
      omega
    rcases hinvariant.tempValuesMode machine.aPos haPos with
      ⟨stored, hstored, hstoredMode⟩
    rw [erase_mergeTempRead] at hstored
    simp only [zero_add] at hstored
    have : stored = entry := by
      apply Option.some.inj
      exact hstored.symm.trans hentry
    simpa [this] using hstoredMode
  have hmode := tempToMainCell_valuesMode_of_eq_some machine.state state
    machine.dest (Int.ofNat machine.aPos) hinvariant.valuesMode hentryMode hcore
  let next : MergeLoMachine κ ν :=
    { machine with
      state := state
      dest := machine.dest + 1
      aPos := machine.aPos + 1
      na := machine.na - 1 }
  have hnextInv : MergeLoMachineInvariant origin tempTotal endIndex next := by
    exact hinvariant.copyA state hframe htempEq hmode hna
  refine ⟨next, ?_, ?_, hnextInv, rfl, rfl⟩
  · simp only [mergeLoCopyAIncrTraced?, TraceResult.map]
    rw [hstate]
    rfl
  · exact MovementTraceSafe.map _ _ htraceSafe

/-- The successful copyback tail is total and safe under the machine
invariant, including the zero-count adversarial-comparator hedge. -/
theorem mergeLoSucceedTraced_safe
    (origin : MergeState κ ν) (tempTotal : Nat) (endIndex : Int)
    (machine : MergeLoMachine κ ν)
    (hinvariant : MergeLoMachineInvariant origin tempTotal endIndex machine) :
    ∃ result, MergeLoCorePost origin tempTotal
      (mergeLoSucceedTraced? machine) (mergeLoSucceed? machine) result := by
  have hmain : SortSlice.RangeInBounds machine.state.data machine.dest
      machine.na := by
    constructor
    · exact hinvariant.destNonnegative
    · calc
        machine.dest + Int.ofNat machine.na = machine.bPos :=
          hinvariant.adjacency
        _ ≤ machine.bPos + Int.ofNat machine.nb :=
          le_add_of_nonneg_right (Int.natCast_nonneg _)
        _ = endIndex := hinvariant.rightAccounting
        _ ≤ Int.ofNat machine.state.data.entries.size := hinvariant.mainEnd
  rcases tempToMainMemcpyTraced_post (.lo .finalTempToData)
      mergeLoFinalTempToDataPermit machine.na machine.state machine.dest
      (Int.ofNat machine.aPos) hmain hinvariant.tempActiveInBounds
      hinvariant.tempActiveValuesMode hinvariant.tempInvariant
      hinvariant.tempLive hinvariant.valuesMode with ⟨state, hpost⟩
  let result : MergeLoResult κ ν := mergeLoSuccess state
  refine ⟨result, ?_⟩
  refine
    { resultEq := ?_
      returnCode := rfl
      resultFuel := rfl
      traceSafe := MovementTraceSafe.map _ _ hpost.traceSafe
      exactErasure := erase_mergeLoSucceedTraced machine
      tempCapacity := by
        change tempTotal ≤ state.a.cells.size
        rw [hpost.frame.tempSize]
        exact hinvariant.tempCapacity
      tempInvariant := hpost.tempInvariant
      tempLive := hpost.tempLive
      valuesMode := hpost.valuesMode
      stableFrame := hinvariant.stableFrame.trans
        (MergeLoStableFrame.of_movement hpost.frame)
      storageFrame := hinvariant.storageFrame.trans
        (MergeLoStorageFrame.of_movement hpost.frame) }
  simp only [mergeLoSucceedTraced?, TraceResult.map]
  rw [hpost.success]
  rfl

/-- The `CopyB` terminal is total and safe when its source precondition is
met. -/
theorem mergeLoCopyBTraced_safe
    (origin : MergeState κ ν) (tempTotal : Nat) (endIndex : Int)
    (machine : MergeLoMachine κ ν)
    (hinvariant : MergeLoMachineInvariant origin tempTotal endIndex machine)
    (hna : machine.na = 1) (hnb : 0 < machine.nb) :
    ∃ result, MergeLoCorePost origin tempTotal
      (mergeLoCopyBTraced? machine) (mergeLoCopyB? machine) result := by
  have hsrc : SortSlice.RangeInBounds machine.state.data machine.bPos
      machine.nb := by
    constructor
    · have := hinvariant.adjacency
      have hd := hinvariant.destNonnegative
      simp only [hna, Int.ofNat_eq_natCast] at this
      omega
    · exact hinvariant.rightAccounting.trans_le hinvariant.mainEnd
  have hdst : SortSlice.RangeInBounds machine.state.data machine.dest
      machine.nb := by
    constructor
    · exact hinvariant.destNonnegative
    · have hadj := hinvariant.adjacency
      have hright := hinvariant.rightAccounting
      have hend := hinvariant.mainEnd
      simp only [hna, Int.ofNat_eq_natCast] at hadj hright hend ⊢
      omega
  rcases mainDataMemmoveTraced_safe machine.state machine.dest machine.bPos
      machine.nb hinvariant.tempInvariant hinvariant.tempLive
      hinvariant.valuesMode hdst hsrc with ⟨moved, hmove⟩
  have hmovedTemp := mainDataMemmoveTraced_temp_eq_of_result machine.state moved
    machine.dest machine.bPos machine.nb hmove.success
  have hmovedInv := hinvariant.replaceState moved hmove.frame hmovedTemp
    hmove.valuesMode
  have hfinalIndex : SortSlice.IndexInBounds moved.data
      (machine.dest + Int.ofNat machine.nb) := by
    rw [SortSlice.IndexInBounds]
    constructor
    · exact add_nonneg hinvariant.destNonnegative (Int.natCast_nonneg _)
    · have hright := hinvariant.rightAccounting
      have hend := hinvariant.mainEnd
      have hsize := hmove.frame.dataSize
      have hadj := hinvariant.adjacency
      simp only [hna, Int.ofNat_eq_natCast] at hright hend hadj ⊢
      rw [hsize]
      omega
  have htemp := hmovedInv.aPosInBounds (by simp [hna])
  have hreadable := hmovedInv.tempReadable (by simp [hna])
  rcases tempToMainCellTraced_safe moved
      (machine.dest + Int.ofNat machine.nb) (Int.ofNat machine.aPos)
      hfinalIndex htemp hmovedInv.tempLive hreadable with
    ⟨state, hstate, hcellSafe, hcellFrame⟩
  have hcellCore : tempToMainCell? moved
      (machine.dest + Int.ofNat machine.nb) (Int.ofNat machine.aPos) =
        some state := by
    rw [← erase_tempToMainCellTraced]
    exact hstate
  have hentryMode : ∀ entry,
      mergeTempRead? moved.a (Int.ofNat machine.aPos) = some entry →
        SortSlice.EntryMatchesValuesMode moved.a.hasValues entry := by
    intro entry hentry
    have haPos : machine.aPos < tempTotal := by
      have := hinvariant.tempAccounting
      omega
    rcases hmovedInv.tempValuesMode machine.aPos haPos with
      ⟨stored, hstored, hstoredMode⟩
    rw [erase_mergeTempRead] at hstored
    simp only [zero_add] at hstored
    have heq : stored = entry := Option.some.inj (hstored.symm.trans hentry)
    simpa [heq] using hstoredMode
  have hmode := tempToMainCell_valuesMode_of_eq_some moved state
    (machine.dest + Int.ofNat machine.nb) (Int.ofNat machine.aPos)
    hmove.valuesMode hentryMode hcellCore
  let result : MergeLoResult κ ν := mergeLoSuccess state
  refine ⟨result, ?_⟩
  refine
    { resultEq := ?_
      returnCode := rfl
      resultFuel := rfl
      traceSafe := ?_
      exactErasure := erase_mergeLoCopyBTraced machine
      tempCapacity := by
        change tempTotal ≤ state.a.cells.size
        rw [hcellFrame.tempSize, hmove.frame.tempSize]
        exact hinvariant.tempCapacity
      tempInvariant := hcellFrame.tempStorageInv hmove.tempInvariant
      tempLive := hcellFrame.live hmove.tempLive
      valuesMode := hmode
      stableFrame := hinvariant.stableFrame.trans
        (MergeLoStableFrame.of_movement (hmove.frame.trans hcellFrame))
      storageFrame := hinvariant.storageFrame.trans
        (MergeLoStorageFrame.of_movement (hmove.frame.trans hcellFrame)) }
  · rw [mergeLoCopyBTraced?, if_pos ⟨hna, hnb⟩]
    simp only [TraceResult.bind, TraceResult.map]
    rw [hmove.success]
    change Option.map mergeLoSuccess
      (tempToMainCellTraced? moved
        (machine.dest + Int.ofNat machine.nb)
        (Int.ofNat machine.aPos)).result = some result
    rw [hstate]
    rfl
  · rw [mergeLoCopyBTraced?, if_pos ⟨hna, hnb⟩]
    exact MovementTraceSafe.bind _ _ moved hmove.success hmove.traceSafe
      (MovementTraceSafe.map _ _ hcellSafe)

/-- Ordinary-mode induction step, parameterized by the smaller-fuel driver
contract so the galloping step can share the same structural induction. -/
private theorem mergeLoOrdinaryTraced_safe
    (origin : MergeState κ ν) (tempTotal : Nat) (endIndex : Int)
    (fuel : Nat) (machine : MergeLoMachine κ ν) (aCount bCount : Nat)
    (hinvariant : MergeLoMachineInvariant origin tempTotal endIndex machine)
    (hfuel : MergeLoFuelInvariant (fuel + 1) machine)
    (hna : 1 < machine.na) (hnb : 0 < machine.nb)
    (ih : ∀ (next : MergeLoMachine κ ν) (phase : MergeLoPhase),
      MergeLoMachineInvariant origin tempTotal endIndex next →
      MergeLoFuelInvariant fuel next → 1 < next.na → 0 < next.nb →
      ∃ result, MergeLoCorePost origin tempTotal
        (mergeLoLoopTraced? fuel next phase)
        (mergeLoLoop? fuel next phase) result) :
    ∃ result, MergeLoCorePost origin tempTotal
      (mergeLoLoopTraced? (fuel + 1) machine (.ordinary aCount bCount))
      (mergeLoLoop? (fuel + 1) machine (.ordinary aCount bCount)) result := by
  have hguard : ¬ (machine.na ≤ 1 ∨ machine.nb = 0) := by omega
  rcases hinvariant.tempReadable (by omega) with ⟨firstA, hfirstA⟩
  have hfirstAResult :
      (TraceResult.tempPayloadRead? machine.state.a
        (Int.ofNat machine.aPos)).result = some firstA := by
    change (TraceResult.tempPayloadRead? machine.state.a
      (Int.ofNat machine.aPos)).erase = some firstA
    rw [TraceResult.erase_tempPayloadRead]
    exact hfirstA
  have hfirstASafe := mergeLoTempReadTraced_safe machine.state.a
    (Int.ofNat machine.aPos) (hinvariant.aPosInBounds (by omega))
    hinvariant.tempLive
  rcases SortSlice.read_eq_some_of_indexInBounds machine.state.data machine.bPos
      (hinvariant.bPosInBounds hnb) with ⟨firstB, hfirstB⟩
  have hfirstBResult :
      (TraceResult.sortSliceKeysRead? machine.state.data machine.bPos).result =
        some firstB := by
    change machine.state.data.read? machine.bPos = some firstB
    exact hfirstB
  have hfirstBSafe := mergeLoMainKeyReadTraced_safe machine.state.data
    machine.bPos (hinvariant.bPosInBounds hnb)
  let tracedAfterReads := fun (left right : SortSliceEntry κ ν) =>
    if iflt machine.state.key_compare right.key left.key then
      (mergeLoCopyBIncrTraced? machine).bind fun moved =>
        let count := bCount + 1
        if moved.nb = 0 then
          mergeLoSucceedTraced? moved
        else if mergeLoCountAtLeastWord count moved.minGallop then
          mergeLoLoopTraced? fuel
            { moved with minGallop := moved.minGallop + 1 } .galloping
        else
          mergeLoLoopTraced? fuel moved (.ordinary 0 count)
    else
      (mergeLoCopyAIncrTraced? machine).bind fun moved =>
        let count := aCount + 1
        if moved.na = 1 then
          mergeLoCopyBTraced? moved
        else if mergeLoCountAtLeastWord count moved.minGallop then
          mergeLoLoopTraced? fuel
            { moved with minGallop := moved.minGallop + 1 } .galloping
        else
          mergeLoLoopTraced? fuel moved (.ordinary count 0)
  let referenceAfterReads := fun (left right : SortSliceEntry κ ν) =>
    if iflt machine.state.key_compare right.key left.key then
      (mergeLoCopyBIncr? machine).bind fun moved =>
        let count := bCount + 1
        if moved.nb = 0 then
          mergeLoSucceed? moved
        else if mergeLoCountAtLeastWord count moved.minGallop then
          mergeLoLoop? fuel
            { moved with minGallop := moved.minGallop + 1 } .galloping
        else
          mergeLoLoop? fuel moved (.ordinary 0 count)
    else
      (mergeLoCopyAIncr? machine).bind fun moved =>
        let count := aCount + 1
        if moved.na = 1 then
          mergeLoCopyB? moved
        else if mergeLoCountAtLeastWord count moved.minGallop then
          mergeLoLoop? fuel
            { moved with minGallop := moved.minGallop + 1 } .galloping
        else
          mergeLoLoop? fuel moved (.ordinary count 0)
  cases hcompare : iflt machine.state.key_compare firstB.key firstA.key with
  | false =>
      have hcompare' :
          machine.state.key_compare firstB.key firstA.key = false := by
        simpa [iflt] using hcompare
      rcases mergeLoCopyAIncrTraced_safe origin tempTotal endIndex machine
          hinvariant (by omega) with
        ⟨next, hnextResult, hnextSafe, hnextInv, hnextNa, hnextNb⟩
      let nextACount := aCount + 1
      let tracedTail : MergeLoMachine κ ν → TraceResult (MergeLoResult κ ν) :=
        fun moved =>
          if moved.na = 1 then
            mergeLoCopyBTraced? moved
          else if mergeLoCountAtLeastWord nextACount moved.minGallop then
            mergeLoLoopTraced? fuel
              { moved with minGallop := moved.minGallop + 1 } .galloping
          else
            mergeLoLoopTraced? fuel moved (.ordinary nextACount 0)
      let referenceTail : MergeLoMachine κ ν → Option (MergeLoResult κ ν) :=
        fun moved =>
          if moved.na = 1 then
            mergeLoCopyB? moved
          else if mergeLoCountAtLeastWord nextACount moved.minGallop then
            mergeLoLoop? fuel
              { moved with minGallop := moved.minGallop + 1 } .galloping
          else
            mergeLoLoop? fuel moved (.ordinary nextACount 0)
      have hnextFuel : MergeLoFuelInvariant fuel next := by
        unfold MergeLoFuelInvariant at hfuel ⊢
        omega
      have htail : ∃ result, MergeLoCorePost origin tempTotal
          (tracedTail next) (referenceTail next) result := by
        by_cases hterminal : next.na = 1
        · have hnextNb : 0 < next.nb := by simpa [hnextNb] using hnb
          simpa [tracedTail, referenceTail, hterminal] using
            mergeLoCopyBTraced_safe origin tempTotal endIndex next hnextInv
              hterminal hnextNb
        · have hnextNaPositive : 1 < next.na := by
            have : 0 < next.na := by
              unfold MergeLoFuelInvariant at hnextFuel
              omega
            omega
          have hnextNbPositive : 0 < next.nb := by simpa [hnextNb] using hnb
          by_cases hgallop :
              mergeLoCountAtLeastWord nextACount next.minGallop
          · have hraisedInv : MergeLoMachineInvariant origin tempTotal endIndex
                { next with minGallop := next.minGallop + 1 } := by
              exact hnextInv.setMachineMinGallop _
            have hraisedFuel : MergeLoFuelInvariant fuel
                { next with minGallop := next.minGallop + 1 } := by
              exact hnextFuel
            simpa [tracedTail, referenceTail, hterminal, hgallop] using
              ih { next with minGallop := next.minGallop + 1 } .galloping
                hraisedInv hraisedFuel (by simpa using hnextNaPositive)
                (by simpa using hnextNbPositive)
          · simpa [tracedTail, referenceTail, hterminal, hgallop] using
              ih next (.ordinary nextACount 0) hnextInv hnextFuel
                hnextNaPositive hnextNbPositive
      rcases htail with ⟨result, htail⟩
      have hcopy := MergeLoCorePost.prepend origin tempTotal
        (mergeLoCopyAIncrTraced? machine) tracedTail referenceTail next result
        hnextResult hnextSafe htail
      have hreadB := MergeLoCorePost.prepend origin tempTotal
        (TraceResult.sortSliceKeysRead? machine.state.data machine.bPos)
        (tracedAfterReads firstA) (referenceAfterReads firstA)
        firstB result hfirstBResult hfirstBSafe (by
          simpa [tracedAfterReads, referenceAfterReads, hcompare, hcompare',
            tracedTail, referenceTail, nextACount,
            erase_mergeLoCopyAIncrTraced] using hcopy)
      have hreadA := MergeLoCorePost.prepend origin tempTotal
        (TraceResult.tempPayloadRead? machine.state.a
          (Int.ofNat machine.aPos))
        (fun left =>
          (TraceResult.sortSliceKeysRead? machine.state.data machine.bPos).bind
            (tracedAfterReads left))
        (fun left => machine.state.data.read? machine.bPos |>.bind
          (referenceAfterReads left))
        firstA result hfirstAResult hfirstASafe hreadB
      refine ⟨result, ?_⟩
      simpa [mergeLoLoopTraced?, mergeLoLoop?, hguard, tracedAfterReads,
        referenceAfterReads, mergeTempRead_ofNat, mergeLoTempRead?] using hreadA
  | true =>
      have hcompare' :
          machine.state.key_compare firstB.key firstA.key = true := by
        simpa [iflt] using hcompare
      rcases mergeLoCopyBIncrTraced_safe origin tempTotal endIndex machine
          hinvariant (by omega) hnb with
        ⟨next, hnextResult, hnextSafe, hnextInv, hnextNa, hnextNb⟩
      let nextBCount := bCount + 1
      let tracedTail : MergeLoMachine κ ν → TraceResult (MergeLoResult κ ν) :=
        fun moved =>
          if moved.nb = 0 then
            mergeLoSucceedTraced? moved
          else if mergeLoCountAtLeastWord nextBCount moved.minGallop then
            mergeLoLoopTraced? fuel
              { moved with minGallop := moved.minGallop + 1 } .galloping
          else
            mergeLoLoopTraced? fuel moved (.ordinary 0 nextBCount)
      let referenceTail : MergeLoMachine κ ν → Option (MergeLoResult κ ν) :=
        fun moved =>
          if moved.nb = 0 then
            mergeLoSucceed? moved
          else if mergeLoCountAtLeastWord nextBCount moved.minGallop then
            mergeLoLoop? fuel
              { moved with minGallop := moved.minGallop + 1 } .galloping
          else
            mergeLoLoop? fuel moved (.ordinary 0 nextBCount)
      have hnextFuel : MergeLoFuelInvariant fuel next := by
        unfold MergeLoFuelInvariant at hfuel ⊢
        omega
      have htail : ∃ result, MergeLoCorePost origin tempTotal
          (tracedTail next) (referenceTail next) result := by
        by_cases hterminal : next.nb = 0
        · simpa [tracedTail, referenceTail, hterminal] using
            mergeLoSucceedTraced_safe origin tempTotal endIndex next hnextInv
        · have hnextNbPositive : 0 < next.nb := Nat.pos_of_ne_zero hterminal
          have hnextNaPositive : 1 < next.na := by simpa [hnextNa] using hna
          by_cases hgallop :
              mergeLoCountAtLeastWord nextBCount next.minGallop
          · have hraisedInv : MergeLoMachineInvariant origin tempTotal endIndex
                { next with minGallop := next.minGallop + 1 } := by
              exact hnextInv.setMachineMinGallop _
            have hraisedFuel : MergeLoFuelInvariant fuel
                { next with minGallop := next.minGallop + 1 } := by
              exact hnextFuel
            simpa [tracedTail, referenceTail, hterminal, hgallop] using
              ih { next with minGallop := next.minGallop + 1 } .galloping
                hraisedInv hraisedFuel (by simpa using hnextNaPositive)
                (by simpa using hnextNbPositive)
          · simpa [tracedTail, referenceTail, hterminal, hgallop] using
              ih next (.ordinary 0 nextBCount) hnextInv hnextFuel
                hnextNaPositive hnextNbPositive
      rcases htail with ⟨result, htail⟩
      have hcopy := MergeLoCorePost.prepend origin tempTotal
        (mergeLoCopyBIncrTraced? machine) tracedTail referenceTail next result
        hnextResult hnextSafe htail
      have hreadB := MergeLoCorePost.prepend origin tempTotal
        (TraceResult.sortSliceKeysRead? machine.state.data machine.bPos)
        (tracedAfterReads firstA) (referenceAfterReads firstA)
        firstB result hfirstBResult hfirstBSafe (by
          simpa [tracedAfterReads, referenceAfterReads, hcompare, hcompare',
            tracedTail, referenceTail, nextBCount,
            erase_mergeLoCopyBIncrTraced] using hcopy)
      have hreadA := MergeLoCorePost.prepend origin tempTotal
        (TraceResult.tempPayloadRead? machine.state.a
          (Int.ofNat machine.aPos))
        (fun left =>
          (TraceResult.sortSliceKeysRead? machine.state.data machine.bPos).bind
            (tracedAfterReads left))
        (fun left => machine.state.data.read? machine.bPos |>.bind
          (referenceAfterReads left))
        firstA result hfirstAResult hfirstASafe hreadB
      refine ⟨result, ?_⟩
      simpa [mergeLoLoopTraced?, mergeLoLoop?, hguard, tracedAfterReads,
        referenceAfterReads, mergeTempRead_ofNat, mergeLoTempRead?] using hreadA

/-- Suffix of one galloping round after the A-side block has been copied.
The weak budget is intentional: the mandatory B and A cell moves establish
the strict smaller-fuel invariant before the only recursive continuation. -/
private theorem mergeLoGallopSuffixTraced_safe
    (origin : MergeState κ ν) (tempTotal : Nat) (endIndex : Int)
    (fuel aCount : Nat) (machine : MergeLoMachine κ ν)
    (hinvariant : MergeLoMachineInvariant origin tempTotal endIndex machine)
    (hbudget : machine.na + machine.nb ≤ fuel)
    (hnb : 0 < machine.nb)
    (ih : ∀ (next : MergeLoMachine κ ν) (phase : MergeLoPhase),
      MergeLoMachineInvariant origin tempTotal endIndex next →
      MergeLoFuelInvariant fuel next → 1 < next.na → 0 < next.nb →
      ∃ result, MergeLoCorePost origin tempTotal
        (mergeLoLoopTraced? fuel next phase)
        (mergeLoLoop? fuel next phase) result) :
    let traced :=
      if machine.na = 0 then
        mergeLoSucceedTraced? machine
      else if machine.na = 1 then
        mergeLoCopyBTraced? machine
      else
        (mergeLoCopyBIncrTraced? machine).bind fun moved =>
          if moved.nb = 0 then
            mergeLoSucceedTraced? moved
          else
            (TraceResult.tempPayloadRead? moved.state.a
              (Int.ofNat moved.aPos)).bind fun firstA =>
              (gallopLeftTraced? moved.state
                (.main moved.state.data moved.bPos)
                firstA.key moved.nb 0).bind fun gallopB =>
                if gallopB.fuelExhausted then
                  mergeLoFuelFailureTraced moved
                else
                  let bCount := gallopB.index
                  if bCount > moved.nb then
                    TraceResult.failure
                  else
                    (mainDataMemmoveTraced? moved.state moved.dest moved.bPos
                      bCount).bind fun state =>
                      let moved : MergeLoMachine κ ν :=
                        { moved with
                          state := state
                          dest := moved.dest + Int.ofNat bCount
                          bPos := moved.bPos + Int.ofNat bCount
                          nb := moved.nb - bCount }
                      if moved.nb = 0 then
                        mergeLoSucceedTraced? moved
                      else
                        (mergeLoCopyAIncrTraced? moved).bind fun moved =>
                          if moved.na = 1 then
                            mergeLoCopyBTraced? moved
                          else if MIN_GALLOP.toNat ≤ aCount ∨
                              MIN_GALLOP.toNat ≤ bCount then
                            mergeLoLoopTraced? fuel moved .galloping
                          else
                            let minGallop := moved.minGallop + 1
                            let state :=
                              { moved.state with min_gallop := minGallop }
                            mergeLoLoopTraced? fuel
                              { moved with state := state, minGallop := minGallop }
                              (.ordinary 0 0)
    let reference :=
      if machine.na = 0 then
        mergeLoSucceed? machine
      else if machine.na = 1 then
        mergeLoCopyB? machine
      else do
        let moved ← mergeLoCopyBIncr? machine
        if moved.nb = 0 then
          mergeLoSucceed? moved
        else
          let firstA ← mergeLoTempRead? moved.state.a moved.aPos
          mergeLoBindOptionAcross
              (gallopLeft? moved.state moved.state.data moved.bPos
                firstA.key moved.nb 0) fun gallopB =>
            if gallopB.fuelExhausted then
              mergeLoGallopFuelFailure moved
            else
              let bCount := gallopB.index
              if bCount > moved.nb then
                none
              else do
                let data ← moved.state.data.memmove?
                  moved.dest moved.bPos bCount
                let moved : MergeLoMachine κ ν :=
                  { moved with
                    state := { moved.state with data := data }
                    dest := moved.dest + Int.ofNat bCount
                    bPos := moved.bPos + Int.ofNat bCount
                    nb := moved.nb - bCount }
                if moved.nb = 0 then
                  mergeLoSucceed? moved
                else do
                  let moved ← mergeLoCopyAIncr? moved
                  if moved.na = 1 then
                    mergeLoCopyB? moved
                  else if MIN_GALLOP.toNat ≤ aCount ∨
                      MIN_GALLOP.toNat ≤ bCount then
                    mergeLoLoop? fuel moved .galloping
                  else
                    let minGallop := moved.minGallop + 1
                    let state := { moved.state with min_gallop := minGallop }
                    mergeLoLoop? fuel
                      { moved with state := state, minGallop := minGallop }
                      (.ordinary 0 0)
    ∃ result, MergeLoCorePost origin tempTotal traced reference result := by
  dsimp only
  by_cases hnaZero : machine.na = 0
  · simpa [hnaZero] using
      mergeLoSucceedTraced_safe origin tempTotal endIndex machine hinvariant
  · by_cases hnaOne : machine.na = 1
    · simpa [hnaZero, hnaOne] using
        mergeLoCopyBTraced_safe origin tempTotal endIndex machine hinvariant
          hnaOne hnb
    · have hna : 1 < machine.na := by omega
      rcases mergeLoCopyBIncrTraced_safe origin tempTotal endIndex machine
          hinvariant (by omega) hnb with
        ⟨afterB, hafterBResult, hafterBSafe, hafterBInv, hafterBNa,
          hafterBNb⟩
      let tracedAfterB := fun (moved : MergeLoMachine κ ν) =>
        if moved.nb = 0 then
          mergeLoSucceedTraced? moved
        else
          (TraceResult.tempPayloadRead? moved.state.a
            (Int.ofNat moved.aPos)).bind fun firstA =>
            (gallopLeftTraced? moved.state
              (.main moved.state.data moved.bPos)
              firstA.key moved.nb 0).bind fun gallopB =>
              if gallopB.fuelExhausted then
                mergeLoFuelFailureTraced moved
              else
                let bCount := gallopB.index
                if bCount > moved.nb then
                  TraceResult.failure
                else
                  (mainDataMemmoveTraced? moved.state moved.dest moved.bPos
                    bCount).bind fun state =>
                    let moved : MergeLoMachine κ ν :=
                      { moved with
                        state := state
                        dest := moved.dest + Int.ofNat bCount
                        bPos := moved.bPos + Int.ofNat bCount
                        nb := moved.nb - bCount }
                    if moved.nb = 0 then
                      mergeLoSucceedTraced? moved
                    else
                      (mergeLoCopyAIncrTraced? moved).bind fun moved =>
                        if moved.na = 1 then
                          mergeLoCopyBTraced? moved
                        else if MIN_GALLOP.toNat ≤ aCount ∨
                            MIN_GALLOP.toNat ≤ bCount then
                          mergeLoLoopTraced? fuel moved .galloping
                        else
                          let minGallop := moved.minGallop + 1
                          let state :=
                            { moved.state with min_gallop := minGallop }
                          mergeLoLoopTraced? fuel
                            { moved with state := state, minGallop := minGallop }
                            (.ordinary 0 0)
      let referenceAfterB := fun (moved : MergeLoMachine κ ν) =>
        if moved.nb = 0 then
          mergeLoSucceed? moved
        else do
          let firstA ← mergeLoTempRead? moved.state.a moved.aPos
          mergeLoBindOptionAcross
              (gallopLeft? moved.state moved.state.data moved.bPos
                firstA.key moved.nb 0) fun gallopB =>
            if gallopB.fuelExhausted then
              mergeLoGallopFuelFailure moved
            else
              let bCount := gallopB.index
              if bCount > moved.nb then
                none
              else do
                let data ← moved.state.data.memmove?
                  moved.dest moved.bPos bCount
                let moved : MergeLoMachine κ ν :=
                  { moved with
                    state := { moved.state with data := data }
                    dest := moved.dest + Int.ofNat bCount
                    bPos := moved.bPos + Int.ofNat bCount
                    nb := moved.nb - bCount }
                if moved.nb = 0 then
                  mergeLoSucceed? moved
                else do
                  let moved ← mergeLoCopyAIncr? moved
                  if moved.na = 1 then
                    mergeLoCopyB? moved
                  else if MIN_GALLOP.toNat ≤ aCount ∨
                      MIN_GALLOP.toNat ≤ bCount then
                    mergeLoLoop? fuel moved .galloping
                  else
                    let minGallop := moved.minGallop + 1
                    let state := { moved.state with min_gallop := minGallop }
                    mergeLoLoop? fuel
                      { moved with state := state, minGallop := minGallop }
                      (.ordinary 0 0)
      have hafterBBudget : afterB.na + afterB.nb < fuel := by
        omega
      have htail : ∃ result, MergeLoCorePost origin tempTotal
          (tracedAfterB afterB) (referenceAfterB afterB) result := by
        by_cases hterminalB : afterB.nb = 0
        · simpa [tracedAfterB, referenceAfterB, hterminalB] using
            mergeLoSucceedTraced_safe origin tempTotal endIndex afterB
              hafterBInv
        · have hafterBNbPositive : 0 < afterB.nb :=
            Nat.pos_of_ne_zero hterminalB
          rcases hafterBInv.tempReadable (by omega) with
            ⟨firstA, hfirstA⟩
          have hfirstAResult :
              (TraceResult.tempPayloadRead? afterB.state.a
                (Int.ofNat afterB.aPos)).result = some firstA := by
            change (TraceResult.tempPayloadRead? afterB.state.a
              (Int.ofNat afterB.aPos)).erase = some firstA
            rw [TraceResult.erase_tempPayloadRead]
            exact hfirstA
          have hfirstASafe := mergeLoTempReadTraced_safe afterB.state.a
            (Int.ofNat afterB.aPos)
            (hafterBInv.aPosInBounds (by omega)) hafterBInv.tempLive
          rcases mergeLoTempRun_exists_of_initialized afterB.state.a
              afterB.aPos afterB.na (by
                intro offset hoffset
                rcases hafterBInv.tempActiveValuesMode offset hoffset with
                  ⟨entry, hentry, _⟩
                refine ⟨entry, ?_⟩
                rw [erase_mergeTempRead] at hentry
                have hsum : Int.ofNat afterB.aPos + Int.ofNat offset =
                    Int.ofNat (afterB.aPos + offset) := by
                  simp only [Int.ofNat_eq_natCast, Nat.cast_add]
                rw [hsum, mergeTempRead_ofNat] at hentry
                exact hentry) with ⟨_activeA, _hactiveA⟩
          rcases gallopLeft_main_safe afterB.state afterB.state.data
              afterB.bPos firstA.key afterB.nb 0
              hafterBInv.rightValidRange hafterBNbPositive (by omega)
              hafterBInv.rightWordBound with
            ⟨gallopB, hgallopBResult, hgallopBFuel, hbCount,
              hgallopBTraceFuel, hgallopBNoPush, hgallopBBounds,
              hgallopBLive, hgallopBErase⟩
          have hgallopBSafe : MovementTraceSafe
              (gallopLeftTraced? afterB.state
                (.main afterB.state.data afterB.bPos)
                firstA.key afterB.nb 0) :=
            ⟨hgallopBTraceFuel, hgallopBNoPush, hgallopBBounds,
              hgallopBLive⟩
          let bCount := gallopB.index
          have hbNotGreater : ¬ afterB.nb < bCount := by
            dsimp [bCount]
            omega
          rcases mainDataMemmoveTraced_safe afterB.state afterB.dest
              afterB.bPos bCount hafterBInv.tempInvariant
              hafterBInv.tempLive hafterBInv.valuesMode
              (hafterBInv.destTotalRange bCount (by omega))
              (hafterBInv.rightRange bCount hbCount) with ⟨movedState, hmove⟩
          let moved : MergeLoMachine κ ν :=
            { afterB with
              state := movedState
              dest := afterB.dest + Int.ofNat bCount
              bPos := afterB.bPos + Int.ofNat bCount
              nb := afterB.nb - bCount }
          have hmovedTemp := mainDataMemmoveTraced_temp_eq_of_result
            afterB.state movedState afterB.dest afterB.bPos bCount hmove.success
          have hmovedInv : MergeLoMachineInvariant origin tempTotal endIndex moved :=
            hafterBInv.copyBBlock bCount hbCount movedState hmove.frame
              hmovedTemp hmove.valuesMode
          have hmovedNa : moved.na = afterB.na := rfl
          have hmovedNbEq : moved.nb = afterB.nb - bCount := rfl
          let tracedAfterMove := fun (count : Nat)
              (current : MergeLoMachine κ ν) =>
            if current.nb = 0 then
              mergeLoSucceedTraced? current
            else
              (mergeLoCopyAIncrTraced? current).bind fun next =>
                if next.na = 1 then
                  mergeLoCopyBTraced? next
                else if MIN_GALLOP.toNat ≤ aCount ∨
                    MIN_GALLOP.toNat ≤ count then
                  mergeLoLoopTraced? fuel next .galloping
                else
                  let minGallop := next.minGallop + 1
                  let state := { next.state with min_gallop := minGallop }
                  mergeLoLoopTraced? fuel
                    { next with state := state, minGallop := minGallop }
                    (.ordinary 0 0)
          let referenceAfterMove := fun (count : Nat)
              (current : MergeLoMachine κ ν) =>
            if current.nb = 0 then
              mergeLoSucceed? current
            else do
              let next ← mergeLoCopyAIncr? current
              if next.na = 1 then
                mergeLoCopyB? next
              else if MIN_GALLOP.toNat ≤ aCount ∨
                  MIN_GALLOP.toNat ≤ count then
                mergeLoLoop? fuel next .galloping
              else
                let minGallop := next.minGallop + 1
                let state := { next.state with min_gallop := minGallop }
                mergeLoLoop? fuel
                  { next with state := state, minGallop := minGallop }
                  (.ordinary 0 0)
          have hafterMove : ∃ result, MergeLoCorePost origin tempTotal
              (tracedAfterMove bCount moved)
              (referenceAfterMove bCount moved) result := by
            by_cases hterminal : moved.nb = 0
            · simpa [tracedAfterMove, referenceAfterMove, hterminal] using
                mergeLoSucceedTraced_safe origin tempTotal endIndex moved
                  hmovedInv
            · have hmovedNbPositive : 0 < moved.nb :=
                Nat.pos_of_ne_zero hterminal
              rcases mergeLoCopyAIncrTraced_safe origin tempTotal endIndex
                  moved hmovedInv (by
                    rw [hmovedNa, hafterBNa]
                    exact Nat.zero_lt_of_lt hna) with
                ⟨afterA, hafterAResult, hafterASafe, hafterAInv,
                  hafterANa, hafterANb⟩
              let tracedFinal := fun (next : MergeLoMachine κ ν) =>
                if next.na = 1 then
                  mergeLoCopyBTraced? next
                else if MIN_GALLOP.toNat ≤ aCount ∨
                    MIN_GALLOP.toNat ≤ bCount then
                  mergeLoLoopTraced? fuel next .galloping
                else
                  let minGallop := next.minGallop + 1
                  let state := { next.state with min_gallop := minGallop }
                  mergeLoLoopTraced? fuel
                    { next with state := state, minGallop := minGallop }
                    (.ordinary 0 0)
              let referenceFinal := fun (next : MergeLoMachine κ ν) =>
                if next.na = 1 then
                  mergeLoCopyB? next
                else if MIN_GALLOP.toNat ≤ aCount ∨
                    MIN_GALLOP.toNat ≤ bCount then
                  mergeLoLoop? fuel next .galloping
                else
                  let minGallop := next.minGallop + 1
                  let state := { next.state with min_gallop := minGallop }
                  mergeLoLoop? fuel
                    { next with state := state, minGallop := minGallop }
                    (.ordinary 0 0)
              have hfinal : ∃ result, MergeLoCorePost origin tempTotal
                  (tracedFinal afterA) (referenceFinal afterA) result := by
                by_cases hterminalA : afterA.na = 1
                · have hafterANbPositive : 0 < afterA.nb := by
                    simpa [hafterANb] using hmovedNbPositive
                  simpa [tracedFinal, referenceFinal, hterminalA] using
                    mergeLoCopyBTraced_safe origin tempTotal endIndex afterA
                      hafterAInv hterminalA hafterANbPositive
                · have hafterANaPositive : 1 < afterA.na := by
                    have : 0 < afterA.na := by
                      rw [hafterANa, hmovedNa]
                      omega
                    omega
                  have hafterANbPositive : 0 < afterA.nb := by
                    simpa [hafterANb] using hmovedNbPositive
                  have hafterAFuel : MergeLoFuelInvariant fuel afterA := by
                    unfold MergeLoFuelInvariant
                    rw [hafterANa, hafterANb, hmovedNa, hmovedNbEq]
                    omega
                  by_cases hstay : MIN_GALLOP.toNat ≤ aCount ∨
                      MIN_GALLOP.toNat ≤ bCount
                  · simpa [tracedFinal, referenceFinal, hterminalA, hstay]
                      using ih afterA .galloping hafterAInv hafterAFuel
                        hafterANaPositive hafterANbPositive
                  · let minGallop := afterA.minGallop + 1
                    let adjusted : MergeLoMachine κ ν :=
                      { afterA with
                        state := { afterA.state with min_gallop := minGallop }
                        minGallop := minGallop }
                    have hadjustedInv : MergeLoMachineInvariant origin tempTotal
                        endIndex adjusted := by
                      exact hafterAInv.setMinGallop minGallop
                    have hadjustedFuel : MergeLoFuelInvariant fuel adjusted := by
                      exact hafterAFuel
                    simpa [tracedFinal, referenceFinal, hterminalA, hstay,
                      adjusted, minGallop] using
                      ih adjusted (.ordinary 0 0) hadjustedInv hadjustedFuel
                        (by simpa [adjusted] using hafterANaPositive)
                        (by simpa [adjusted] using hafterANbPositive)
              rcases hfinal with ⟨result, hfinal⟩
              exact ⟨result, by
                simpa [tracedAfterMove, referenceAfterMove, hterminal,
                  tracedFinal, referenceFinal] using
                  MergeLoCorePost.prepend origin tempTotal
                    (mergeLoCopyAIncrTraced? moved) tracedFinal referenceFinal
                    afterA result hafterAResult hafterASafe hfinal⟩
          rcases hafterMove with ⟨result, hafterMove⟩
          have hmovePost := MergeLoCorePost.prepend origin tempTotal
            (mainDataMemmoveTraced? afterB.state afterB.dest afterB.bPos bCount)
            (fun state => tracedAfterMove bCount
              { afterB with
                state := state
                dest := afterB.dest + Int.ofNat bCount
                bPos := afterB.bPos + Int.ofNat bCount
                nb := afterB.nb - bCount })
            (fun state => referenceAfterMove bCount
              { afterB with
                state := state
                dest := afterB.dest + Int.ofNat bCount
                bPos := afterB.bPos + Int.ofNat bCount
                nb := afterB.nb - bCount })
            movedState result hmove.success hmove.traceSafe hafterMove
          let tracedAfterGallop := fun (g : GallopResult) =>
            if g.fuelExhausted then
              mergeLoFuelFailureTraced afterB
            else
              let count := g.index
              if count > afterB.nb then
                TraceResult.failure
              else
                (mainDataMemmoveTraced? afterB.state afterB.dest afterB.bPos
                  count).bind fun state =>
                    tracedAfterMove count
                      { afterB with
                        state := state
                        dest := afterB.dest + Int.ofNat count
                        bPos := afterB.bPos + Int.ofNat count
                        nb := afterB.nb - count }
          let referenceAfterGallop := fun (g : GallopResult) =>
            if g.fuelExhausted then
              mergeLoGallopFuelFailure afterB
            else
              let count := g.index
              if count > afterB.nb then
                none
              else do
                let data ← afterB.state.data.memmove?
                  afterB.dest afterB.bPos count
                referenceAfterMove count
                  { afterB with
                    state := { afterB.state with data := data }
                    dest := afterB.dest + Int.ofNat count
                    bPos := afterB.bPos + Int.ofNat count
                    nb := afterB.nb - count }
          have hgallopPost := MergeLoCorePost.prepend origin tempTotal
            (gallopLeftTraced? afterB.state
              (.main afterB.state.data afterB.bPos)
              firstA.key afterB.nb 0)
            tracedAfterGallop referenceAfterGallop gallopB result
            hgallopBResult hgallopBSafe (by
              simpa [tracedAfterGallop, referenceAfterGallop, hgallopBFuel,
                bCount, hbCount, hbNotGreater, mainDataMemmove?,
                erase_mainDataMemmoveTraced, Option.bind_assoc] using hmovePost)
          have hreadPost := MergeLoCorePost.prepend origin tempTotal
            (TraceResult.tempPayloadRead? afterB.state.a
              (Int.ofNat afterB.aPos))
            (fun entry =>
              (gallopLeftTraced? afterB.state
                (.main afterB.state.data afterB.bPos)
                entry.key afterB.nb 0).bind tracedAfterGallop)
            (fun entry =>
              mergeLoBindOptionAcross
                (gallopLeft? afterB.state afterB.state.data afterB.bPos
                  entry.key afterB.nb 0) referenceAfterGallop)
            firstA result hfirstAResult hfirstASafe (by
              have hbind :
                  (gallopLeft? afterB.state afterB.state.data afterB.bPos
                    firstA.key afterB.nb 0).bind referenceAfterGallop =
                    mergeLoBindOptionAcross
                      (gallopLeft? afterB.state afterB.state.data afterB.bPos
                        firstA.key afterB.nb 0) referenceAfterGallop := by
                cases gallopLeft? afterB.state afterB.state.data afterB.bPos
                  firstA.key afterB.nb 0 <;> rfl
              simpa [hgallopBErase, hbind] using hgallopPost)
          exact ⟨result, by
            simpa [tracedAfterB, referenceAfterB, hterminalB,
              tracedAfterGallop, referenceAfterGallop, tracedAfterMove,
              referenceAfterMove, mergeLoTempRead?, mergeTempRead_ofNat]
              using hreadPost⟩
      rcases htail with ⟨result, htail⟩
      exact ⟨result, by
        simpa [hnaZero, hnaOne, tracedAfterB, referenceAfterB,
          erase_mergeLoCopyBIncrTraced] using
          MergeLoCorePost.prepend origin tempTotal
            (mergeLoCopyBIncrTraced? machine) tracedAfterB referenceAfterB
            afterB result hafterBResult hafterBSafe htail⟩

/-- Galloping-mode induction step.  The adaptive `minGallop` machine field is
allowed to differ briefly from `state.min_gallop`: the straight-to-gallop
transition increments only the local field, exactly as in the reviewed
transcription, and this step immediately writes the decreased threshold back
to the state. -/
private theorem mergeLoGallopingTraced_safe
    (origin : MergeState κ ν) (tempTotal : Nat) (endIndex : Int)
    (fuel : Nat) (machine : MergeLoMachine κ ν)
    (hinvariant : MergeLoMachineInvariant origin tempTotal endIndex machine)
    (hfuel : MergeLoFuelInvariant (fuel + 1) machine)
    (hna : 1 < machine.na) (hnb : 0 < machine.nb)
    (ih : ∀ (next : MergeLoMachine κ ν) (phase : MergeLoPhase),
      MergeLoMachineInvariant origin tempTotal endIndex next →
      MergeLoFuelInvariant fuel next → 1 < next.na → 0 < next.nb →
      ∃ result, MergeLoCorePost origin tempTotal
        (mergeLoLoopTraced? fuel next phase)
        (mergeLoLoop? fuel next phase) result) :
    ∃ result, MergeLoCorePost origin tempTotal
      (mergeLoLoopTraced? (fuel + 1) machine .galloping)
      (mergeLoLoop? (fuel + 1) machine .galloping) result := by
  have hguard : ¬ (machine.na ≤ 1 ∨ machine.nb = 0) := by omega
  let minGallop :=
    if (1 : PySSize).slt machine.minGallop then
      machine.minGallop - 1
    else machine.minGallop
  let adjusted : MergeLoMachine κ ν :=
    { machine with
      state := { machine.state with min_gallop := minGallop }
      minGallop := minGallop }
  have hadjustedInv : MergeLoMachineInvariant origin tempTotal endIndex adjusted :=
    hinvariant.setMinGallop minGallop
  have hadjustedNa : adjusted.na = machine.na := rfl
  have hadjustedNb : adjusted.nb = machine.nb := rfl
  rcases SortSlice.read_eq_some_of_indexInBounds adjusted.state.data adjusted.bPos
      (hadjustedInv.bPosInBounds (by simpa [hadjustedNb] using hnb)) with
    ⟨firstB, hfirstB⟩
  have hfirstBResult :
      (TraceResult.sortSliceKeysRead? adjusted.state.data adjusted.bPos).result =
        some firstB := by
    change adjusted.state.data.read? adjusted.bPos = some firstB
    exact hfirstB
  have hfirstBSafe := mergeLoMainKeyReadTraced_safe adjusted.state.data
    adjusted.bPos (hadjustedInv.bPosInBounds (by simpa [hadjustedNb] using hnb))
  have hinitialized : MergeLoTempRangeInitialized adjusted.state.a
      adjusted.aPos adjusted.na := by
    intro offset hoffset
    rcases hadjustedInv.tempActiveValuesMode offset hoffset with
      ⟨entry, hentry, _⟩
    refine ⟨entry, ?_⟩
    rw [erase_mergeTempRead] at hentry
    have hsum : Int.ofNat adjusted.aPos + Int.ofNat offset =
        Int.ofNat (adjusted.aPos + offset) := by
      simp only [Int.ofNat_eq_natCast, Nat.cast_add]
    rw [hsum, mergeTempRead_ofNat] at hentry
    exact hentry
  rcases mergeLoTempRun_exists_of_initialized adjusted.state.a adjusted.aPos
      adjusted.na hinitialized with ⟨activeA, hactiveA⟩
  have hactiveResult :
      (mergeLoTraceOption
        (mergeLoTempRun? adjusted.state.a adjusted.aPos adjusted.na)).result =
        some activeA := by
    simp [mergeLoTraceOption, hactiveA, TraceResult.pure]
  have hactiveSafe : MovementTraceSafe
      (mergeLoTraceOption
        (mergeLoTempRun? adjusted.state.a adjusted.aPos adjusted.na)) := by
    simpa [mergeLoTraceOption, hactiveA] using
      (MovementTraceSafe.pure activeA)
  rcases gallopRight_safe adjusted.state
      (.temporary adjusted.state.a (Int.ofNat adjusted.aPos)) activeA 0
      firstB.key adjusted.na 0 hadjustedInv.temporaryValidRange
      hadjustedInv.tempLive
      (tempRun_agreesWithSlice_of_eq_some adjusted.state.a adjusted.aPos
        adjusted.na activeA hactiveA)
      (by rw [hadjustedNa]; omega) (by omega)
      hadjustedInv.leftWordBound with
    ⟨gallopA, hgallopAResult, hgallopAFuel, haCount,
      hgallopATraceFuel, hgallopANoPush, hgallopABounds,
      hgallopALive, hgallopAErase⟩
  have hgallopASafe : MovementTraceSafe
      (gallopRightTraced? adjusted.state
        (.temporary adjusted.state.a (Int.ofNat adjusted.aPos))
        firstB.key adjusted.na 0) :=
    ⟨hgallopATraceFuel, hgallopANoPush, hgallopABounds, hgallopALive⟩
  let aCount := gallopA.index
  have haNotGreater : ¬ adjusted.na < aCount := by
    dsimp [aCount]
    omega
  rcases tempToMainMemcpyTraced_post (.lo .gallopTempToData)
      mergeLoGallopTempToDataPermit aCount adjusted.state adjusted.dest
      (Int.ofNat adjusted.aPos) (hadjustedInv.destRange aCount haCount)
      (hadjustedInv.tempPrefixInBounds aCount haCount)
      (hadjustedInv.tempPrefixValuesMode aCount haCount)
      hadjustedInv.tempInvariant hadjustedInv.tempLive
      hadjustedInv.valuesMode with ⟨copiedState, hcopy⟩
  let afterA : MergeLoMachine κ ν :=
    { adjusted with
      state := copiedState
      dest := adjusted.dest + Int.ofNat aCount
      aPos := adjusted.aPos + aCount
      na := adjusted.na - aCount }
  have hcopyCore : tempToMainMemcpy? aCount adjusted.state adjusted.dest
      (Int.ofNat adjusted.aPos) = some copiedState := by
    rw [← hcopy.exactErasure]
    exact hcopy.success
  have hcopyTemp := tempToMainMemcpy_temp_eq_of_eq_some aCount adjusted.state
    copiedState adjusted.dest (Int.ofNat adjusted.aPos) hcopyCore
  have hafterAInv : MergeLoMachineInvariant origin tempTotal endIndex afterA :=
    hadjustedInv.copyABlock aCount haCount copiedState hcopy.frame hcopyTemp
      hcopy.valuesMode
  have hafterABudget : afterA.na + afterA.nb ≤ fuel := by
    unfold MergeLoFuelInvariant at hfuel
    dsimp [afterA, adjusted]
    omega
  have hafterANb : 0 < afterA.nb := by
    dsimp [afterA, adjusted]
    exact hnb
  let tracedAfterCopy := fun (count : Nat) (current : MergeLoMachine κ ν) =>
    if current.na = 0 then
      mergeLoSucceedTraced? current
    else if current.na = 1 then
      mergeLoCopyBTraced? current
    else
      (mergeLoCopyBIncrTraced? current).bind fun moved =>
        if moved.nb = 0 then
          mergeLoSucceedTraced? moved
        else
          (TraceResult.tempPayloadRead? moved.state.a
            (Int.ofNat moved.aPos)).bind fun firstA =>
            (gallopLeftTraced? moved.state
              (.main moved.state.data moved.bPos)
              firstA.key moved.nb 0).bind fun gallopB =>
              if gallopB.fuelExhausted then
                mergeLoFuelFailureTraced moved
              else
                let bCount := gallopB.index
                if bCount > moved.nb then
                  TraceResult.failure
                else
                  (mainDataMemmoveTraced? moved.state moved.dest moved.bPos
                    bCount).bind fun state =>
                    let moved : MergeLoMachine κ ν :=
                      { moved with
                        state := state
                        dest := moved.dest + Int.ofNat bCount
                        bPos := moved.bPos + Int.ofNat bCount
                        nb := moved.nb - bCount }
                    if moved.nb = 0 then
                      mergeLoSucceedTraced? moved
                    else
                      (mergeLoCopyAIncrTraced? moved).bind fun moved =>
                        if moved.na = 1 then
                          mergeLoCopyBTraced? moved
                        else if MIN_GALLOP.toNat ≤ count ∨
                            MIN_GALLOP.toNat ≤ bCount then
                          mergeLoLoopTraced? fuel moved .galloping
                        else
                          let threshold := moved.minGallop + 1
                          let state :=
                            { moved.state with min_gallop := threshold }
                          mergeLoLoopTraced? fuel
                            { moved with state := state, minGallop := threshold }
                            (.ordinary 0 0)
  let referenceAfterCopy := fun (count : Nat)
      (current : MergeLoMachine κ ν) =>
    if current.na = 0 then
      mergeLoSucceed? current
    else if current.na = 1 then
      mergeLoCopyB? current
    else do
      let moved ← mergeLoCopyBIncr? current
      if moved.nb = 0 then
        mergeLoSucceed? moved
      else
        let firstA ← mergeLoTempRead? moved.state.a moved.aPos
        mergeLoBindOptionAcross
            (gallopLeft? moved.state moved.state.data moved.bPos
              firstA.key moved.nb 0) fun gallopB =>
          if gallopB.fuelExhausted then
            mergeLoGallopFuelFailure moved
          else
            let bCount := gallopB.index
            if bCount > moved.nb then
              none
            else do
              let data ← moved.state.data.memmove?
                moved.dest moved.bPos bCount
              let moved : MergeLoMachine κ ν :=
                { moved with
                  state := { moved.state with data := data }
                  dest := moved.dest + Int.ofNat bCount
                  bPos := moved.bPos + Int.ofNat bCount
                  nb := moved.nb - bCount }
              if moved.nb = 0 then
                mergeLoSucceed? moved
              else do
                let moved ← mergeLoCopyAIncr? moved
                if moved.na = 1 then
                  mergeLoCopyB? moved
                else if MIN_GALLOP.toNat ≤ count ∨
                    MIN_GALLOP.toNat ≤ bCount then
                  mergeLoLoop? fuel moved .galloping
                else
                  let threshold := moved.minGallop + 1
                  let state := { moved.state with min_gallop := threshold }
                  mergeLoLoop? fuel
                    { moved with state := state, minGallop := threshold }
                    (.ordinary 0 0)
  rcases mergeLoGallopSuffixTraced_safe origin tempTotal endIndex fuel aCount
      afterA hafterAInv hafterABudget hafterANb ih with ⟨result, hsuffix⟩
  have hcopyPost := MergeLoCorePost.prepend origin tempTotal
    (tempToMainMemcpyTraced? (.lo .gallopTempToData)
      mergeLoGallopTempToDataPermit aCount adjusted.state adjusted.dest
      (Int.ofNat adjusted.aPos))
    (fun state => tracedAfterCopy aCount
      { adjusted with
        state := state
        dest := adjusted.dest + Int.ofNat aCount
        aPos := adjusted.aPos + aCount
        na := adjusted.na - aCount })
    (fun state => referenceAfterCopy aCount
      { adjusted with
        state := state
        dest := adjusted.dest + Int.ofNat aCount
        aPos := adjusted.aPos + aCount
        na := adjusted.na - aCount })
    copiedState result hcopy.success hcopy.traceSafe (by
      simpa [tracedAfterCopy, referenceAfterCopy, afterA] using hsuffix)
  let tracedAfterGallop := fun (g : GallopResult) =>
    if g.fuelExhausted then
      mergeLoFuelFailureTraced adjusted
    else
      let count := g.index
      if count > adjusted.na then
        TraceResult.failure
      else
        (tempToMainMemcpyTraced? (.lo .gallopTempToData)
          mergeLoGallopTempToDataPermit count adjusted.state adjusted.dest
          (Int.ofNat adjusted.aPos)).bind fun state =>
            tracedAfterCopy count
              { adjusted with
                state := state
                dest := adjusted.dest + Int.ofNat count
                aPos := adjusted.aPos + count
                na := adjusted.na - count }
  let referenceAfterGallop := fun (g : GallopResult) =>
    if g.fuelExhausted then
      mergeLoGallopFuelFailure adjusted
    else
      let count := g.index
      if count > adjusted.na then
        none
      else do
        let state ← mergeLoMemcpyTempToData? .gallopTempToData rfl count
          adjusted.state adjusted.dest adjusted.aPos
        referenceAfterCopy count
          { adjusted with
            state := state
            dest := adjusted.dest + Int.ofNat count
            aPos := adjusted.aPos + count
            na := adjusted.na - count }
  have hgallopPost := MergeLoCorePost.prepend origin tempTotal
    (gallopRightTraced? adjusted.state
      (.temporary adjusted.state.a (Int.ofNat adjusted.aPos))
      firstB.key adjusted.na 0)
    tracedAfterGallop referenceAfterGallop gallopA result
    hgallopAResult hgallopASafe (by
      let continuation := fun state => referenceAfterCopy aCount
        { adjusted with
          state := state
          dest := adjusted.dest + Int.ofNat aCount
          aPos := adjusted.aPos + aCount
          na := adjusted.na - aCount }
      have href :
          (tempToMainMemcpyTraced? (.lo .gallopTempToData)
              mergeLoGallopTempToDataPermit aCount adjusted.state
              adjusted.dest (Int.ofNat adjusted.aPos)).erase.bind continuation =
            (mergeLoMemcpyTempToData? .gallopTempToData rfl aCount
              adjusted.state adjusted.dest adjusted.aPos).bind continuation :=
        calc
          _ = (tempToMainMemcpy? aCount adjusted.state adjusted.dest
                (Int.ofNat adjusted.aPos)).bind continuation :=
            congrArg (fun option => option.bind continuation)
              (erase_tempToMainMemcpyTraced (.lo .gallopTempToData)
                mergeLoGallopTempToDataPermit aCount adjusted.state
                adjusted.dest (Int.ofNat adjusted.aPos))
          _ = _ := congrArg (fun option => option.bind continuation)
            (tempToMainMemcpy_eq_mergeLo .gallopTempToData rfl aCount
              adjusted.state adjusted.dest adjusted.aPos)
      have htagged := MergeLoCorePost.reference_eq origin tempTotal _ _ _
        result href hcopyPost
      simpa [tracedAfterGallop, referenceAfterGallop, hgallopAFuel,
        haNotGreater, aCount, continuation] using htagged)
  let tracedAfterSlice := fun (_ : SortSlice κ ν) =>
    (gallopRightTraced? adjusted.state
      (.temporary adjusted.state.a (Int.ofNat adjusted.aPos))
      firstB.key adjusted.na 0).bind tracedAfterGallop
  let referenceAfterSlice := fun (slice : SortSlice κ ν) =>
    mergeLoBindOptionAcross
      (gallopRight? adjusted.state slice 0 firstB.key adjusted.na 0)
      referenceAfterGallop
  have hslicePost := MergeLoCorePost.prepend origin tempTotal
    (mergeLoTraceOption
      (mergeLoTempRun? adjusted.state.a adjusted.aPos adjusted.na))
    tracedAfterSlice referenceAfterSlice activeA result hactiveResult hactiveSafe
    (by
      have hbind :
          (gallopRight? adjusted.state activeA 0 firstB.key adjusted.na 0).bind
              referenceAfterGallop =
            mergeLoBindOptionAcross
              (gallopRight? adjusted.state activeA 0 firstB.key adjusted.na 0)
              referenceAfterGallop := by
        cases gallopRight? adjusted.state activeA 0 firstB.key adjusted.na 0 <;>
          rfl
      have href :
          (gallopRightTraced? adjusted.state
              (.temporary adjusted.state.a (Int.ofNat adjusted.aPos))
              firstB.key adjusted.na 0).erase.bind referenceAfterGallop =
            mergeLoBindOptionAcross
              (gallopRight? adjusted.state activeA 0 firstB.key adjusted.na 0)
              referenceAfterGallop := by
        calc
          _ = (gallopRight? adjusted.state activeA 0 firstB.key adjusted.na 0).bind
                referenceAfterGallop :=
            congrArg (fun option => option.bind referenceAfterGallop)
              hgallopAErase
          _ = _ := hbind
      exact MergeLoCorePost.reference_eq origin tempTotal _ _ _ result href
        hgallopPost)
  let tracedAfterFirstB := fun (entry : SortSliceEntry κ ν) =>
    (mergeLoTraceOption
      (mergeLoTempRun? adjusted.state.a adjusted.aPos adjusted.na)).bind
        fun _ =>
          (gallopRightTraced? adjusted.state
            (.temporary adjusted.state.a (Int.ofNat adjusted.aPos))
            entry.key adjusted.na 0).bind tracedAfterGallop
  let referenceAfterFirstB := fun (entry : SortSliceEntry κ ν) =>
    (mergeLoTempRun? adjusted.state.a adjusted.aPos adjusted.na).bind fun slice =>
      mergeLoBindOptionAcross
        (gallopRight? adjusted.state slice 0 entry.key adjusted.na 0)
        referenceAfterGallop
  have hfirstBPost := MergeLoCorePost.prepend origin tempTotal
    (TraceResult.sortSliceKeysRead? adjusted.state.data adjusted.bPos)
    tracedAfterFirstB referenceAfterFirstB firstB result hfirstBResult hfirstBSafe
    (by simpa [tracedAfterFirstB, referenceAfterFirstB, tracedAfterSlice,
      referenceAfterSlice, mergeLoTraceOption_erase] using hslicePost)
  refine ⟨result, ?_⟩
  simpa [mergeLoLoopTraced?, mergeLoLoop?, mergeLoGallopRoundTraced?,
    mergeLoGallopRound?, hguard, minGallop, adjusted, tracedAfterFirstB,
    referenceAfterFirstB, tracedAfterSlice, referenceAfterSlice,
    tracedAfterGallop, referenceAfterGallop, tracedAfterCopy,
    referenceAfterCopy, mergeLoBindOptionAcross] using hfirstBPost

/-- Complete recursive driver contract.  Strict fuel slack rules out the
zero-fuel marker and is decreased only after at least one real merge move. -/
private theorem mergeLoLoopTraced_safe
    (origin : MergeState κ ν) (tempTotal : Nat) (endIndex : Int)
    (fuel : Nat) (machine : MergeLoMachine κ ν) (phase : MergeLoPhase)
    (hinvariant : MergeLoMachineInvariant origin tempTotal endIndex machine)
    (hfuel : MergeLoFuelInvariant fuel machine)
    (hna : 1 < machine.na) (hnb : 0 < machine.nb) :
    ∃ result, MergeLoCorePost origin tempTotal
      (mergeLoLoopTraced? fuel machine phase)
      (mergeLoLoop? fuel machine phase) result := by
  induction fuel generalizing machine phase with
  | zero =>
      unfold MergeLoFuelInvariant at hfuel
      omega
  | succ fuel ih =>
      cases phase with
      | ordinary aCount bCount =>
          exact mergeLoOrdinaryTraced_safe origin tempTotal endIndex fuel machine
            aCount bCount hinvariant hfuel hna hnb ih
      | galloping =>
          exact mergeLoGallopingTraced_safe origin tempTotal endIndex fuel machine
            hinvariant hfuel hna hnb ih

/-! ## Trace-witness composition -/

private theorem hasAccess_bind_left
    (current : TraceResult α) (next : α → TraceResult β)
    (kind : AccessKind) (region : AccessRegion)
    (hcurrent : current.trace.HasAccess kind region) :
    (current.bind next).trace.HasAccess kind region := by
  rw [TraceResult.trace_bind]
  cases current.result with
  | none => exact hcurrent
  | some value => exact hcurrent.compose_left

private theorem hasAccess_bind_right
    (current : TraceResult α) (next : α → TraceResult β)
    (value : α) (kind : AccessKind) (region : AccessRegion)
    (hresult : current.result = some value)
    (hnext : (next value).trace.HasAccess kind region) :
    (current.bind next).trace.HasAccess kind region := by
  rw [TraceResult.trace_bind, hresult]
  exact hnext.compose_right

private theorem hasTempAccess_bind_left
    (current : TraceResult α) (next : α → TraceResult β)
    (kind : AccessKind) (hcurrent : current.trace.HasTempAccess kind) :
    (current.bind next).trace.HasTempAccess kind := by
  rcases hcurrent with ⟨backing, hcurrent⟩
  exact ⟨backing, hasAccess_bind_left current next kind
    (.tempPayload backing) hcurrent⟩

private theorem hasTempAccess_bind_right
    (current : TraceResult α) (next : α → TraceResult β)
    (value : α) (kind : AccessKind)
    (hresult : current.result = some value)
    (hnext : (next value).trace.HasTempAccess kind) :
    (current.bind next).trace.HasTempAccess kind := by
  rcases hnext with ⟨backing, hnext⟩
  exact ⟨backing, hasAccess_bind_right current next value kind
    (.tempPayload backing) hresult hnext⟩

private theorem tempPayloadRead_hasTempAccess
    (storage : TempStorage κ ν) (index : Int) :
    (TraceResult.tempPayloadRead? storage index).trace.HasTempAccess .read := by
  refine ⟨storage.backing, ?_⟩
  refine ⟨AccessEvent.mk .read (.tempPayload storage.backing) index
    storage.cells.size, ?_, rfl, rfl⟩
  simp [TraceResult.trace_tempPayloadRead, AccessTrace.singletonAccess]

private theorem tempToMainCellTraced_hasTempRead
    (state : MergeState κ ν) (mainDst tempSrc : Int) :
    (tempToMainCellTraced? state mainDst tempSrc).trace.HasTempAccess .read := by
  have hkey : (tempToMainKeyTraced? state mainDst tempSrc).trace.HasTempAccess
      .read := by
    unfold tempToMainKeyTraced?
    exact hasTempAccess_bind_left _ _ .read
      (tempPayloadRead_hasTempAccess state.a tempSrc)
  unfold tempToMainCellTraced?
  exact hasTempAccess_bind_left _ _ .read hkey

private theorem mergeLoSucceedTraced_hasTempRead
    (origin : MergeState κ ν) (tempTotal : Nat) (endIndex : Int)
    (machine : MergeLoMachine κ ν)
    (hinvariant : MergeLoMachineInvariant origin tempTotal endIndex machine)
    (hna : 0 < machine.na) :
    (mergeLoSucceedTraced? machine).trace.HasTempAccess .read := by
  have hmain := hinvariant.destRange machine.na le_rfl
  rcases tempToMainMemcpyTraced_post (.lo .finalTempToData)
      mergeLoFinalTempToDataPermit machine.na machine.state machine.dest
      (Int.ofNat machine.aPos) hmain hinvariant.tempActiveInBounds
      hinvariant.tempActiveValuesMode hinvariant.tempInvariant
      hinvariant.tempLive hinvariant.valuesMode with ⟨_, hpost⟩
  change (tempToMainMemcpyTraced? (.lo .finalTempToData)
    mergeLoFinalTempToDataPermit machine.na machine.state machine.dest
    (Int.ofNat machine.aPos)).trace.HasTempAccess .read
  exact hpost.tempReadEvent hna

private theorem mergeLoCopyBTraced_hasTempRead
    (origin : MergeState κ ν) (tempTotal : Nat) (endIndex : Int)
    (machine : MergeLoMachine κ ν)
    (hinvariant : MergeLoMachineInvariant origin tempTotal endIndex machine)
    (hna : machine.na = 1) (hnb : 0 < machine.nb) :
    (mergeLoCopyBTraced? machine).trace.HasTempAccess .read := by
  have hsrc := hinvariant.rightRange machine.nb le_rfl
  have hdst := hinvariant.destTotalRange machine.nb (by omega)
  rcases mainDataMemmoveTraced_safe machine.state machine.dest machine.bPos
      machine.nb hinvariant.tempInvariant hinvariant.tempLive
      hinvariant.valuesMode hdst hsrc with ⟨moved, hmove⟩
  rw [mergeLoCopyBTraced?, if_pos ⟨hna, hnb⟩]
  exact hasTempAccess_bind_right _ _ moved .read hmove.success
    (by
      change (tempToMainCellTraced? moved
        (machine.dest + Int.ofNat machine.nb)
        (Int.ofNat machine.aPos)).trace.HasTempAccess .read
      exact tempToMainCellTraced_hasTempRead moved
        (machine.dest + Int.ofNat machine.nb) (Int.ofNat machine.aPos))

private theorem mergeLoOrdinaryLoopTraced_hasTempRead
    (fuel : Nat) (machine : MergeLoMachine κ ν)
    (hna : 1 < machine.na) (hnb : 0 < machine.nb) :
    (mergeLoLoopTraced? (fuel + 1) machine (.ordinary 0 0)).trace.HasTempAccess
      .read := by
  have hguard : ¬ (machine.na ≤ 1 ∨ machine.nb = 0) := by omega
  rw [mergeLoLoopTraced?, if_neg hguard]
  exact hasTempAccess_bind_left _ _ .read
    (tempPayloadRead_hasTempAccess machine.state.a (Int.ofNat machine.aPos))

/-- The allocation selected by the concrete `merge_lo` call site.  Naming it
once keeps the preparation, core-execution, and final trace-witness stages in
lockstep without repeating the `merge_getmem` expression. -/
def mergeLoAllocated (call : MergeAtCall κ ν) :
    MergeGetmemResult κ ν :=
  mergeGetmem call.state (BitVec.ofNat 64 call.na)

/-- Full externally consumable postcondition for one actual `merge_at`
`merge_lo` continuation. -/
structure MergeLoSafetyPost
    (pre : MergeState κ ν) (scanned i : Nat) (call : MergeAtCall κ ν)
    (execution : TraceResult (MergeLoResult κ ν))
    (result : MergeLoResult κ ν) : Prop where
  resultEq : execution.result = some result
  returnCode : result.returnCode = 0
  resultFuel : result.fuelExhausted = false
  traceFuel : execution.trace.fuelExhausted = false
  accessesInBounds : execution.trace.allAccessesInBounds
  tempAccessesLive : execution.trace.tempPayloadAccessesLive
  noPushes : execution.trace.pushDepths = []
  noMemoryEvents : execution.trace.memoryEvents = []
  exactErasure : execution.erase =
    mergeLo? call.state call.ssa call.ssb call.na call.nb
  tempInvariant : TempStorageInv result.state.a result.state.alloced
  tempLive : result.state.a.Live
  logicalCapacity : result.state.a.cells.size = result.state.alloced.toNat
  requestFits : call.na ≤ result.state.alloced.toNat
  valuesMode :
    SortSlice.ValuesModeInvariant result.state.a.hasValues result.state.data
  stableFrame : MergeLoStableFrame call.state result.state
  geometry : MergeAtSafetyGeometry pre scanned i call
  requestFacts : MergeGetmemRequestBoundFacts pre scanned i call.na call
  inputTempInvariant : TempStorageInv call.state.a call.state.alloced
  inputTempLive : call.state.a.Live
  inputValuesMode :
    SortSlice.ValuesModeInvariant call.state.a.hasValues call.state.data
  /-- The exact `merge_getmem` certificate for the allocation consumed by
  this merge, including reuse/growth accounting and the intermediate free on
  growth. -/
  allocationPost : MergeGetmemStoragePost call.state
    (BitVec.ofNat 64 call.na) (mergeLoAllocated call)
  /-- Every item of temporary-storage metadata is unchanged from the
  successful allocation through the final merge state. -/
  postGetmemStorageFrame :
    MergeLoStorageFrame (mergeLoAllocated call).state result.state
  /-- Reuse preserves the incoming physical bound exactly; growth establishes
  it from the allocation guard.  The top-level lifecycle induction supplies
  the bound on the reuse input. -/
  physicalSlotsBound :
    call.state.a.physicalSlots ≤ PY_SSIZE_T_MAX / PY_OBJECT_PTR_BYTES →
      result.state.a.physicalSlots ≤ PY_SSIZE_T_MAX / PY_OBJECT_PTR_BYTES
  /-- Full provenance obligation inherited from the classified initial copy.
  Besides distinct backing at every merge call site, this exports the generic
  SortSlice admissibility theorem and the same-backing-overlap rejection
  regression consumed by downstream merge-memory safety. -/
  memcpyProvenance : MergeMemcpyCallsiteProvenanceContract κ ν
  inputKeyEvent : execution.trace.HasAccess .read .inputKeys
  tempWriteEvent : execution.trace.HasTempAccess .write
  tempReadEvent : execution.trace.HasTempAccess .read
  synchronizedValuesEvent : call.state.a.hasValues = true →
    execution.trace.HasAccess .read .synchronizedValues

/-! ## Staged public-proof assembly -/

/-- Initial machine installed after the left run has been copied to temporary
storage. -/
def mergeLoInitialMachine (call : MergeAtCall κ ν)
    (state : MergeState κ ν) : MergeLoMachine κ ν :=
  { state := state
    dest := call.ssa
    aPos := 0
    bPos := call.ssb
    na := call.na
    nb := call.nb
    minGallop := state.min_gallop }

/-- Exclusive end of the right input run, fixed throughout `merge_lo`. -/
def mergeLoEndIndex (call : MergeAtCall κ ν) : Int :=
  call.ssb + Int.ofNat call.nb

/-- The post-initial-move traced continuation. -/
private def mergeLoTracedTail (call : MergeAtCall κ ν)
    (machine : MergeLoMachine κ ν) : TraceResult (MergeLoResult κ ν) :=
  if machine.nb = 0 then
    mergeLoSucceedTraced? machine
  else if machine.na = 1 then
    mergeLoCopyBTraced? machine
  else
    mergeLoLoopTraced? (call.na + call.nb + 1) machine (.ordinary 0 0)

/-- Erased counterpart of `mergeLoTracedTail`. -/
private def mergeLoReferenceTail (call : MergeAtCall κ ν)
    (machine : MergeLoMachine κ ν) : Option (MergeLoResult κ ν) :=
  if machine.nb = 0 then
    mergeLoSucceed? machine
  else if machine.na = 1 then
    mergeLoCopyB? machine
  else
    mergeLoLoop? (call.na + call.nb + 1) machine (.ordinary 0 0)

/-- The full continuation after the initial main-to-temporary bulk copy. -/
private def mergeLoTracedAfterCopy (call : MergeAtCall κ ν)
    (state : MergeState κ ν) : TraceResult (MergeLoResult κ ν) :=
  (mergeLoCopyBIncrTraced? (mergeLoInitialMachine call state)).bind
    (mergeLoTracedTail call)

/-- Erased counterpart of `mergeLoTracedAfterCopy`. -/
private def mergeLoReferenceAfterCopy (call : MergeAtCall κ ν)
    (state : MergeState κ ν) : Option (MergeLoResult κ ν) :=
  (mergeLoCopyBIncr? (mergeLoInitialMachine call state)).bind
    (mergeLoReferenceTail call)

/-- Output of the call-site/allocation/initial-copy stage.  It packages the
facts later stages actually consume, including the invariant of the exact
machine installed by the transcription. -/
structure MergeLoInitialStage
    (pre : MergeState κ ν) (scanned i : Nat) (call : MergeAtCall κ ν)
    (copied : MergeState κ ν) : Prop where
  requestFacts : MergeGetmemRequestBoundFacts pre scanned i call.na call
  geometry : MergeAtSafetyGeometry pre scanned i call
  inputTempInvariant : TempStorageInv call.state.a call.state.alloced
  inputTempLive : call.state.a.Live
  inputValuesMode :
    SortSlice.ValuesModeInvariant call.state.a.hasValues call.state.data
  allocationPost : MergeGetmemStoragePost call.state
    (BitVec.ofNat 64 call.na) (mergeLoAllocated call)
  copyPost : MainToTempMemcpyPost (.lo .initialDataToTemp)
    mergeLoInitialDataToTempPermit call.na (mergeLoAllocated call).state copied
    0 call.ssa
  initialInvariant : MergeLoMachineInvariant (mergeLoAllocated call).state call.na
    (mergeLoEndIndex call) (mergeLoInitialMachine call copied)

/-- Establish allocation validity, copy the left run into temporary storage,
and construct the exact initial machine invariant. -/
theorem mergeLo_prepareInitial
    (pre : MergeState κ ν) (scanned i : Nat) (call : MergeAtCall κ ν)
    (hlayout : PendingLayout pre scanned)
    (hmax : pre.listlen.toNat ≤ PY_LIST_MAX)
    (hprepare : prepareMergeAt? pre i = some (.mergeLo call))
    (hInv : TempStorageInv pre.a pre.alloced)
    (hLive : pre.a.Live)
    (hMode : SortSlice.ValuesModeInvariant pre.a.hasValues pre.data) :
    ∃ copied, MergeLoInitialStage pre scanned i call copied := by
  have hrequest := mergeGetmem_lo_request_bound pre scanned i call hlayout hmax
    hprepare
  have hgeometry := mergeLo_callsite_safety_geometry pre scanned i call hlayout
    hmax hprepare
  have hevidence := hgeometry.evidence
  have hcallInv : TempStorageInv call.state.a call.state.alloced := by
    simpa only [hevidence.storage_eq, hevidence.alloced_eq] using hInv
  have hcallLive : call.state.a.Live := by
    simpa only [hevidence.storage_eq] using hLive
  have hcallMode :
      SortSlice.ValuesModeInvariant call.state.a.hasValues call.state.data := by
    simpa only [hevidence.hasValues_eq, hevidence.data_eq] using hMode
  have hallocPost : MergeGetmemStoragePost call.state
      (BitVec.ofNat 64 call.na) (mergeLoAllocated call) := by
    exact mergeGetmem_storage_valid call.state (BitVec.ofNat 64 call.na)
      hcallInv hcallLive hrequest.requestNonnegative
      (fun _ => hrequest.requestWithinLimit)
  have hallocatedMode :
      SortSlice.ValuesModeInvariant (mergeLoAllocated call).state.a.hasValues
        (mergeLoAllocated call).state.data := by
    simpa only [hallocPost.valuesMode, hallocPost.data_eq] using hcallMode
  have htempRange : TempRangeInBounds (mergeLoAllocated call).state.a 0
      call.na := by
    constructor
    · omega
    · simp only [zero_add]
      apply Int.ofNat_le.mpr
      rw [hallocPost.logicalCapacity]
      simpa only [hrequest.requestRoundtrip] using hallocPost.requestFits
  have hmainRange : SortSlice.RangeInBounds (mergeLoAllocated call).state.data
      call.ssa call.na := by
    constructor
    · exact hgeometry.ssaNonnegative
    · have hmerged := hgeometry.mergedRange
      rw [hallocPost.data_eq]
      simp only [Int.ofNat_eq_natCast, Nat.cast_add] at hmerged ⊢
      omega
  rcases mainToTempMemcpyTraced_post (.lo .initialDataToTemp)
      mergeLoInitialDataToTempPermit call.na (mergeLoAllocated call).state 0
      call.ssa htempRange hmainRange hallocPost.invariant hallocPost.live
      hallocatedMode with ⟨copied, hcopy⟩
  refine ⟨copied,
    { requestFacts := hrequest
      geometry := hgeometry
      inputTempInvariant := hcallInv
      inputTempLive := hcallLive
      inputValuesMode := hcallMode
      allocationPost := hallocPost
      copyPost := hcopy
      initialInvariant := ?_ }⟩
  refine
    { destNonnegative := ?_
      tempAccounting := ?_
      adjacency := ?_
      rightAccounting := ?_
      mainEnd := ?_
      leftWordBound := ?_
      rightWordBound := ?_
      tempCapacity := ?_
      tempValuesMode := ?_
      tempInvariant := hcopy.tempInvariant
      tempLive := hcopy.tempLive
      valuesMode := hcopy.valuesMode
      stableFrame := MergeLoStableFrame.of_movement hcopy.frame
      storageFrame := MergeLoStorageFrame.of_movement hcopy.frame }
  · exact hgeometry.ssaNonnegative
  · simp [mergeLoInitialMachine]
  · simpa [mergeLoInitialMachine] using hgeometry.adjacent
  · rfl
  · change mergeLoEndIndex call ≤ Int.ofNat copied.data.entries.size
    rw [hcopy.frame.dataSize, hallocPost.data_eq]
    exact hgeometry.rightRange
  · change call.na ≤ PY_LIST_MAX
    have hrun := hgeometry.runLengthBound
    omega
  · change call.nb ≤ PY_LIST_MAX
    have hrun := hgeometry.runLengthBound
    omega
  · change call.na ≤ copied.a.cells.size
    rw [hcopy.frame.tempSize, hallocPost.logicalCapacity]
    simpa only [hrequest.requestRoundtrip] using hallocPost.requestFits
  · simpa [mergeLoInitialMachine] using hcopy.tempValuesMode

/-- Output of the initial `B` move plus the complete lockstep tail. -/
private structure MergeLoCoreStage (call : MergeAtCall κ ν)
    (copied : MergeState κ ν) (result : MergeLoResult κ ν) : Prop where
  corePost : MergeLoCorePost (mergeLoAllocated call).state call.na
    (mergeLoTracedAfterCopy call copied)
    (mergeLoReferenceAfterCopy call copied) result
  tempRead : (mergeLoTracedAfterCopy call copied).trace.HasTempAccess .read

/-- Execute the mandatory first `B` move and discharge all three continuation
shapes: immediate success, `CopyB`, or the fuel-bounded lockstep loop. -/
private theorem mergeLo_runCore
    (pre : MergeState κ ν) (scanned i : Nat) (call : MergeAtCall κ ν)
    (copied : MergeState κ ν)
    (stage : MergeLoInitialStage pre scanned i call copied) :
    ∃ result, MergeLoCoreStage call copied result := by
  let initial := mergeLoInitialMachine call copied
  have hinitial : MergeLoMachineInvariant (mergeLoAllocated call).state call.na
      (mergeLoEndIndex call) initial := by
    simpa only [initial] using stage.initialInvariant
  rcases mergeLoCopyBIncrTraced_safe (mergeLoAllocated call).state call.na
      (mergeLoEndIndex call) initial hinitial stage.geometry.leftPositive
      stage.geometry.rightPositive with
    ⟨afterB, hafterBResult, hafterBSafe, hafterBInv, hafterBNa,
      hafterBNb⟩
  have htail : ∃ result,
      MergeLoCorePost (mergeLoAllocated call).state call.na
        (mergeLoTracedTail call afterB)
        (mergeLoReferenceTail call afterB) result ∧
      (mergeLoTracedTail call afterB).trace.HasTempAccess .read := by
    by_cases hnbZero : afterB.nb = 0
    · rcases mergeLoSucceedTraced_safe (mergeLoAllocated call).state call.na
        (mergeLoEndIndex call) afterB hafterBInv with ⟨result, hpost⟩
      refine ⟨result, ?_, ?_⟩
      · simpa [mergeLoTracedTail, mergeLoReferenceTail, hnbZero] using hpost
      · simpa [mergeLoTracedTail, hnbZero] using
          (mergeLoSucceedTraced_hasTempRead (mergeLoAllocated call).state call.na
            (mergeLoEndIndex call) afterB hafterBInv (by
              rw [hafterBNa]
              simpa [initial, mergeLoInitialMachine] using
                stage.geometry.leftPositive))
    · have hnbPositive : 0 < afterB.nb := Nat.pos_of_ne_zero hnbZero
      by_cases hnaOne : afterB.na = 1
      · rcases mergeLoCopyBTraced_safe (mergeLoAllocated call).state call.na
          (mergeLoEndIndex call) afterB hafterBInv hnaOne hnbPositive with
          ⟨result, hpost⟩
        refine ⟨result, ?_, ?_⟩
        · simpa [mergeLoTracedTail, mergeLoReferenceTail, hnbZero, hnaOne]
            using hpost
        · simpa [mergeLoTracedTail, hnbZero, hnaOne] using
            (mergeLoCopyBTraced_hasTempRead (mergeLoAllocated call).state call.na
              (mergeLoEndIndex call) afterB hafterBInv hnaOne hnbPositive)
      · have hnaPositive : 0 < afterB.na := by
          rw [hafterBNa]
          simpa [initial, mergeLoInitialMachine] using
            stage.geometry.leftPositive
        have hnaLarge : 1 < afterB.na := by omega
        have hfuel : MergeLoFuelInvariant (call.na + call.nb + 1) afterB := by
          unfold MergeLoFuelInvariant
          rw [hafterBNa, hafterBNb]
          simp only [initial, mergeLoInitialMachine]
          omega
        rcases mergeLoLoopTraced_safe (mergeLoAllocated call).state call.na
            (mergeLoEndIndex call) (call.na + call.nb + 1) afterB
            (.ordinary 0 0) hafterBInv hfuel hnaLarge hnbPositive with
          ⟨result, hpost⟩
        refine ⟨result, ?_, ?_⟩
        · simpa [mergeLoTracedTail, mergeLoReferenceTail, hnbZero, hnaOne]
            using hpost
        · simpa [mergeLoTracedTail, hnbZero, hnaOne, Nat.add_assoc] using
            (mergeLoOrdinaryLoopTraced_hasTempRead (call.na + call.nb) afterB
              hnaLarge hnbPositive)
  rcases htail with ⟨result, htailPost, htailRead⟩
  have hafterInitialRead :
      ((mergeLoCopyBIncrTraced? initial).bind
        (mergeLoTracedTail call)).trace.HasTempAccess .read :=
    hasTempAccess_bind_right (mergeLoCopyBIncrTraced? initial)
      (mergeLoTracedTail call) afterB .read hafterBResult htailRead
  have hafterInitial := MergeLoCorePost.prepend
    (mergeLoAllocated call).state call.na
    (mergeLoCopyBIncrTraced? initial) (mergeLoTracedTail call)
    (mergeLoReferenceTail call) afterB result hafterBResult hafterBSafe htailPost
  refine ⟨result, ?_⟩
  constructor
  · simpa [mergeLoTracedAfterCopy, mergeLoReferenceAfterCopy, initial] using
      hafterInitial
  · simpa [mergeLoTracedAfterCopy, initial] using hafterInitialRead

/-- Prefix the core execution with the initial classified copy and assemble
the externally consumable trace, erasure, frame, storage, and provenance
witnesses. -/
private theorem mergeLo_finish
    (pre : MergeState κ ν) (scanned i : Nat) (call : MergeAtCall κ ν)
    (copied : MergeState κ ν)
    (stage : MergeLoInitialStage pre scanned i call copied)
    (result : MergeLoResult κ ν)
    (core : MergeLoCoreStage call copied result) :
    MergeLoSafetyPost pre scanned i call
      (mergeLoTraced? call.state call.ssa call.ssb call.na call.nb) result := by
  have hwhole := MergeLoCorePost.prepend (mergeLoAllocated call).state call.na
    (mainToTempMemcpyTraced? (.lo .initialDataToTemp)
      mergeLoInitialDataToTempPermit call.na (mergeLoAllocated call).state 0
      call.ssa)
    (mergeLoTracedAfterCopy call) (mergeLoReferenceAfterCopy call)
    copied result stage.copyPost.success stage.copyPost.traceSafe
    core.corePost
  have hreference :
      (mainToTempMemcpyTraced? (.lo .initialDataToTemp)
          mergeLoInitialDataToTempPermit call.na (mergeLoAllocated call).state 0
          call.ssa).erase.bind (mergeLoReferenceAfterCopy call) =
        (mergeLoMemcpyDataToTemp? .initialDataToTemp rfl call.na
          (mergeLoAllocated call).state 0 call.ssa).bind
            (mergeLoReferenceAfterCopy call) := by
    calc
      _ = (mainToTempMemcpy? call.na (mergeLoAllocated call).state 0
            call.ssa).bind (mergeLoReferenceAfterCopy call) :=
        congrArg (fun option => option.bind (mergeLoReferenceAfterCopy call))
          stage.copyPost.exactErasure
      _ = _ := congrArg
        (fun option => option.bind (mergeLoReferenceAfterCopy call))
        (mainToTempMemcpy_eq_mergeLo .initialDataToTemp rfl call.na
          (mergeLoAllocated call).state 0 call.ssa)
  have hwholeTagged := MergeLoCorePost.reference_eq
    (mergeLoAllocated call).state call.na _ _ _ result hreference hwhole
  have hentryGuard :
      0 < call.na ∧ 0 < call.nb ∧ call.na ≤ PY_SSIZE_T_MAX ∧
        call.nb ≤ PY_SSIZE_T_MAX ∧
        call.ssa + Int.ofNat call.na = call.ssb :=
    ⟨stage.geometry.leftPositive, stage.geometry.rightPositive,
      stage.geometry.leftWordBound, stage.geometry.rightWordBound,
      stage.geometry.adjacent⟩
  have hcore : MergeLoCorePost (mergeLoAllocated call).state call.na
      (mergeLoTraced? call.state call.ssa call.ssb call.na call.nb)
      (mergeLo? call.state call.ssa call.ssb call.na call.nb) result := by
    rw [mergeLoTraced?, if_pos hentryGuard,
      if_neg stage.requestFacts.guardNotRejected]
    rw [mergeLo?, if_pos hentryGuard,
      if_neg stage.requestFacts.guardNotRejected]
    change MergeLoCorePost (mergeLoAllocated call).state call.na
      ((mainToTempMemcpyTraced? (.lo .initialDataToTemp)
        mergeLoInitialDataToTempPermit call.na (mergeLoAllocated call).state 0
        call.ssa).bind (mergeLoTracedAfterCopy call))
      ((mergeLoMemcpyDataToTemp? .initialDataToTemp rfl call.na
        (mergeLoAllocated call).state 0 call.ssa).bind
          (mergeLoReferenceAfterCopy call)) result
    exact hwholeTagged
  have hinputEvent :
      (mergeLoTraced? call.state call.ssa call.ssb call.na call.nb).trace.HasAccess
        .read .inputKeys := by
    have hprefixed := hasAccess_bind_left
      (mainToTempMemcpyTraced? (.lo .initialDataToTemp)
        mergeLoInitialDataToTempPermit call.na (mergeLoAllocated call).state 0
        call.ssa)
      (mergeLoTracedAfterCopy call) .read .inputKeys
      (stage.copyPost.inputKeyEvent stage.geometry.leftPositive)
    rw [mergeLoTraced?, if_pos hentryGuard,
      if_neg stage.requestFacts.guardNotRejected]
    change ((mainToTempMemcpyTraced? (.lo .initialDataToTemp)
      mergeLoInitialDataToTempPermit call.na (mergeLoAllocated call).state 0
      call.ssa).bind (mergeLoTracedAfterCopy call)).trace.HasAccess
        .read .inputKeys
    exact hprefixed
  have htempWriteEvent :
      (mergeLoTraced? call.state call.ssa call.ssb call.na call.nb).trace.HasTempAccess
        .write := by
    have hprefixed := hasTempAccess_bind_left
      (mainToTempMemcpyTraced? (.lo .initialDataToTemp)
        mergeLoInitialDataToTempPermit call.na (mergeLoAllocated call).state 0
        call.ssa)
      (mergeLoTracedAfterCopy call) .write
      (stage.copyPost.tempWriteEvent stage.geometry.leftPositive)
    rw [mergeLoTraced?, if_pos hentryGuard,
      if_neg stage.requestFacts.guardNotRejected]
    change ((mainToTempMemcpyTraced? (.lo .initialDataToTemp)
      mergeLoInitialDataToTempPermit call.na (mergeLoAllocated call).state 0
      call.ssa).bind (mergeLoTracedAfterCopy call)).trace.HasTempAccess .write
    exact hprefixed
  have htempReadEvent :
      (mergeLoTraced? call.state call.ssa call.ssb call.na call.nb).trace.HasTempAccess
        .read := by
    have hprefixed := hasTempAccess_bind_right
      (mainToTempMemcpyTraced? (.lo .initialDataToTemp)
        mergeLoInitialDataToTempPermit call.na (mergeLoAllocated call).state 0
        call.ssa)
      (mergeLoTracedAfterCopy call) copied .read
      stage.copyPost.success core.tempRead
    rw [mergeLoTraced?, if_pos hentryGuard,
      if_neg stage.requestFacts.guardNotRejected]
    change ((mainToTempMemcpyTraced? (.lo .initialDataToTemp)
      mergeLoInitialDataToTempPermit call.na (mergeLoAllocated call).state 0
      call.ssa).bind (mergeLoTracedAfterCopy call)).trace.HasTempAccess .read
    exact hprefixed
  have hlogical := TempStorageInv.cells_size_eq hcore.tempInvariant hcore.tempLive
  have hphysicalBound :
      call.state.a.physicalSlots ≤ PY_SSIZE_T_MAX / PY_OBJECT_PTR_BYTES →
        result.state.a.physicalSlots ≤
          PY_SSIZE_T_MAX / PY_OBJECT_PTR_BYTES := by
    intro hbefore
    rw [hcore.storageFrame.physicalSlots_eq]
    rcases stage.allocationPost.outcome with hreuse | hgrown
    · rw [stage.allocationPost.reuseAccounting hreuse]
      exact hbefore
    · exact (stage.allocationPost.growthAccounting hgrown).2.2.2.2
  refine
    { resultEq := hcore.resultEq
      returnCode := hcore.returnCode
      resultFuel := hcore.resultFuel
      traceFuel := hcore.traceSafe.fuel
      accessesInBounds := hcore.traceSafe.bounds
      tempAccessesLive := hcore.traceSafe.tempLive
      noPushes := hcore.traceSafe.noPushes
      noMemoryEvents := mergeLoTraced_memoryEvents_empty
        call.state call.ssa call.ssb call.na call.nb
      exactErasure := hcore.exactErasure
      tempInvariant := hcore.tempInvariant
      tempLive := hcore.tempLive
      logicalCapacity := hlogical
      requestFits := hcore.tempCapacity.trans_eq hlogical
      valuesMode := hcore.valuesMode
      stableFrame := (MergeLoStableFrame.of_getmem call.state
        (BitVec.ofNat 64 call.na) stage.allocationPost).trans hcore.stableFrame
      geometry := stage.geometry
      requestFacts := stage.requestFacts
      inputTempInvariant := stage.inputTempInvariant
      inputTempLive := stage.inputTempLive
      inputValuesMode := stage.inputValuesMode
      allocationPost := stage.allocationPost
      postGetmemStorageFrame := hcore.storageFrame
      physicalSlotsBound := hphysicalBound
      memcpyProvenance := stage.copyPost.provenanceContract
      inputKeyEvent := hinputEvent
      tempWriteEvent := htempWriteEvent
      tempReadEvent := htempReadEvent
      synchronizedValuesEvent := ?_ }
  intro hvalues
  have hallocatedValues : (mergeLoAllocated call).state.a.hasValues = true :=
    stage.allocationPost.valuesMode.trans hvalues
  have hprefixed := hasAccess_bind_left
    (mainToTempMemcpyTraced? (.lo .initialDataToTemp)
      mergeLoInitialDataToTempPermit call.na (mergeLoAllocated call).state 0
      call.ssa)
    (mergeLoTracedAfterCopy call) .read .synchronizedValues
    (stage.copyPost.synchronizedValuesEvent stage.geometry.leftPositive
      hallocatedValues)
  rw [mergeLoTraced?, if_pos hentryGuard,
    if_neg stage.requestFacts.guardNotRejected]
  change ((mainToTempMemcpyTraced? (.lo .initialDataToTemp)
    mergeLoInitialDataToTempPermit call.na (mergeLoAllocated call).state 0
    call.ssa).bind (mergeLoTracedAfterCopy call)).trace.HasAccess
      .read .synchronizedValues
  exact hprefixed

/-- Safety of the concrete `merge_lo` continuation selected by `merge_at`.
All cursor geometry, allocation admissibility, positivity, and word bounds are
derived from the pending-layout certificate and the actual preparation
equation; none are repeated as caller assumptions. -/
theorem mergeLo_safe
    (pre : MergeState κ ν) (scanned i : Nat) (call : MergeAtCall κ ν)
    (hlayout : PendingLayout pre scanned)
    (hmax : pre.listlen.toNat ≤ PY_LIST_MAX)
    (hprepare : prepareMergeAt? pre i = some (.mergeLo call))
    (hInv : TempStorageInv pre.a pre.alloced)
    (hLive : pre.a.Live)
    (hMode : SortSlice.ValuesModeInvariant pre.a.hasValues pre.data) :
    ∃ result, MergeLoSafetyPost pre scanned i call
      (mergeLoTraced? call.state call.ssa call.ssb call.na call.nb) result := by
  let stage := mergeLo_prepareInitial pre scanned i call hlayout hmax hprepare
    hInv hLive hMode
  rcases stage with ⟨copied, stage⟩
  rcases mergeLo_runCore pre scanned i call copied stage with ⟨result, core⟩
  exact ⟨result, mergeLo_finish pre scanned i call copied stage result core⟩

/-! ## Proof-only raw-erasure API

These bridges expose the tagged transcription calls behind the traced memcpy
primitives without carrying any of the safety theorem's domain premises. -/

/-- Erasing the traced A-side gallop copy gives the exact tagged raw helper. -/
theorem erase_mergeLoGallopTempToDataTraced
    (count : Nat) (state : MergeState κ ν) (destination : Int)
    (source : Nat) :
    (tempToMainMemcpyTraced? (.lo .gallopTempToData)
      mergeLoGallopTempToDataPermit count state destination
      (Int.ofNat source)).erase =
      mergeLoMemcpyTempToData? .gallopTempToData rfl count state destination
        source := by
  calc
    _ = tempToMainMemcpy? count state destination (Int.ofNat source) :=
      erase_tempToMainMemcpyTraced (.lo .gallopTempToData)
        mergeLoGallopTempToDataPermit count state destination
        (Int.ofNat source)
    _ = _ := tempToMainMemcpy_eq_mergeLo .gallopTempToData rfl count state
      destination source

/-- Erasing the traced initial copy gives the exact tagged raw helper. -/
theorem erase_mergeLoInitialDataToTempTraced
    (count : Nat) (state : MergeState κ ν) (destination : Nat)
    (source : Int) :
    (mainToTempMemcpyTraced? (.lo .initialDataToTemp)
      mergeLoInitialDataToTempPermit count state (Int.ofNat destination)
      source).erase =
      mergeLoMemcpyDataToTemp? .initialDataToTemp rfl count state destination
        source := by
  calc
    _ = mainToTempMemcpy? count state (Int.ofNat destination) source :=
      erase_mainToTempMemcpyTraced (.lo .initialDataToTemp)
        mergeLoInitialDataToTempPermit count state (Int.ofNat destination)
        source
    _ = _ := mainToTempMemcpy_eq_mergeLo .initialDataToTemp rfl count state
      destination source

/-- Pure erasure bridge for the direct temporary gallop used in `merge_lo`.
Unlike the safety theorem, it only uses the evaluator's signed-word guard. -/
theorem erase_mergeLoTemporaryGallopRightRaw
    (state : MergeState κ ν) (start count : Nat)
    (slice : SortSlice κ ν) (key : κ)
    (hslice : mergeLoTempRun? state.a start count = some slice) :
    (gallopRightTraced? state
      (.temporary state.a (Int.ofNat start)) key count 0).erase =
        gallopRight? state slice 0 key count 0 := by
  rw [erase_gallopRightTraced]
  by_cases hinput : 0 < count ∧ count ≤ PY_SSIZE_T_MAX
  · exact gallopRightFromSource_eq_slice_of_ssize state
      (.temporary state.a (Int.ofNat start)) slice 0 key count 0
      (tempRun_agreesWithSlice_of_eq_some state.a start count slice hslice)
      hinput.1 (by omega) hinput.2
  · unfold gallopRightFromSource? gallopRight?
    have hguard : ¬(0 < count ∧ 0 < count ∧ count ≤ PY_SSIZE_T_MAX) := by
      aesop
    simp only [hguard, if_false]

private theorem traceErase_bind_reachable
    {α β : Type*}
    (traced : TraceResult α) (raw : Option α)
    (nextTraced : α → TraceResult β) (next : α → Option β)
    (hsource : traced.erase = raw)
    (hnext : ∀ value, raw = some value →
      (nextTraced value).erase = next value) :
    (traced.bind nextTraced).erase = raw.bind next := by
  rw [TraceResult.erase_bind, hsource]
  cases hraw : raw with
  | none => simp
  | some value => simpa [hraw] using hnext value hraw

private theorem traceErase_bindAcross_reachable
    {α β : Type*}
    (traced : TraceResult α) (raw : Option α)
    (nextTraced : α → TraceResult β) (next : α → Option β)
    (hsource : traced.erase = raw)
    (hnext : ∀ value, raw = some value →
      (nextTraced value).erase = next value) :
    (traced.bind nextTraced).erase = mergeLoBindOptionAcross raw next := by
  unfold mergeLoBindOptionAcross
  rw [TraceResult.erase_bind, hsource]
  cases hraw : raw with
  | none => rfl
  | some value => simpa [hraw] using hnext value hraw

private theorem mainDataMemmove_bind_eq_raw
    (state : MergeState κ ν) (dst src : Int) (count : Nat)
    (next : MergeState κ ν → Option α) :
    (mainDataMemmove? state dst src count).bind next =
      (state.data.memmove? dst src count).bind fun data =>
        next { state with data := data } := by
  unfold mainDataMemmove?
  cases state.data.memmove? dst src count <;> rfl

/-- Erasure commutes with one complete `merge_lo` galloping round whenever it
commutes with the supplied continuation.  The bridge is unconditional: the
successful materialization equation carried by the raw bind is the only fact
needed to relate the physical temporary gallop to its reviewed slice form. -/
theorem erase_mergeLoGallopRoundTraced
    (machine : MergeLoMachine κ ν)
    (nextTraced : MergeLoMachine κ ν → Nat → Nat →
      TraceResult (MergeLoResult κ ν))
    (next : MergeLoMachine κ ν → Nat → Nat →
      Option (MergeLoResult κ ν))
    (hnext : ∀ machine aCount bCount,
      (nextTraced machine aCount bCount).erase =
        next machine aCount bCount) :
    (mergeLoGallopRoundTraced? machine nextTraced).erase =
      mergeLoGallopRound? machine next := by
  unfold mergeLoGallopRoundTraced? mergeLoGallopRound?
  split
  · rfl
  · let minGallop :=
      if (1 : PySSize).slt machine.minGallop then
        machine.minGallop - 1
      else machine.minGallop
    let adjustedState := { machine.state with min_gallop := minGallop }
    let adjusted : MergeLoMachine κ ν :=
      { machine with state := adjustedState, minGallop := minGallop }
    apply traceErase_bind_reachable
      (TraceResult.sortSliceKeysRead? adjusted.state.data adjusted.bPos)
      (adjusted.state.data.read? adjusted.bPos)
      _ _ (TraceResult.erase_sortSliceKeysRead _ _)
    intro firstB _
    apply traceErase_bind_reachable
      (mergeLoTraceOption
        (mergeLoTempRun? adjusted.state.a adjusted.aPos adjusted.na))
      (mergeLoTempRun? adjusted.state.a adjusted.aPos adjusted.na)
      _ _ (mergeLoTraceOption_erase _)
    intro activeA hactive
    dsimp [adjusted, adjustedState, minGallop] at hactive ⊢
    apply traceErase_bindAcross_reachable
      (gallopRightTraced?
        { machine.state with
          min_gallop := if (1 : PySSize).slt machine.minGallop then
            machine.minGallop - 1 else machine.minGallop }
        (.temporary machine.state.a (Int.ofNat machine.aPos))
        firstB.key machine.na 0)
      (gallopRight?
        { machine.state with
          min_gallop := if (1 : PySSize).slt machine.minGallop then
            machine.minGallop - 1 else machine.minGallop }
        activeA 0 firstB.key machine.na 0)
      _ _ (erase_mergeLoTemporaryGallopRightRaw
        { machine.state with
          min_gallop := if (1 : PySSize).slt machine.minGallop then
            machine.minGallop - 1 else machine.minGallop }
        machine.aPos machine.na activeA firstB.key hactive)
    intro gallopA _
    by_cases hfuel : gallopA.fuelExhausted = true
    · simp only [hfuel, if_true]
      exact erase_mergeLoFuelFailureTraced _
    · simp only [hfuel]
      by_cases hover : gallopA.index > machine.na
      · simp only [hover, if_true]
        rfl
      · simp only [hover, if_false]
        apply traceErase_bind_reachable
          (tempToMainMemcpyTraced? (.lo .gallopTempToData)
            mergeLoGallopTempToDataPermit gallopA.index
            { machine.state with
              min_gallop := if (1 : PySSize).slt machine.minGallop then
                machine.minGallop - 1 else machine.minGallop }
            machine.dest (Int.ofNat machine.aPos))
          (mergeLoMemcpyTempToData? .gallopTempToData rfl gallopA.index
            { machine.state with
              min_gallop := if (1 : PySSize).slt machine.minGallop then
                machine.minGallop - 1 else machine.minGallop }
            machine.dest machine.aPos)
          _ _ (erase_mergeLoGallopTempToDataTraced gallopA.index
            { machine.state with
              min_gallop := if (1 : PySSize).slt machine.minGallop then
                machine.minGallop - 1 else machine.minGallop }
            machine.dest machine.aPos)
        intro state _
        by_cases hna0 : machine.na - gallopA.index = 0
        · simp only [hna0, if_true]
          exact erase_mergeLoSucceedTraced _
        · simp only [hna0, if_false]
          by_cases hna1 : machine.na - gallopA.index = 1
          · simp only [hna1, if_true]
            exact erase_mergeLoCopyBTraced _
          · simp only [hna1, if_false]
            apply traceErase_bind_reachable
              (mergeLoCopyBIncrTraced? _)
              (mergeLoCopyBIncr? _)
              _ _ (erase_mergeLoCopyBIncrTraced _)
            intro afterB _
            by_cases hnb0 : afterB.nb = 0
            · simp only [hnb0, if_true]
              exact erase_mergeLoSucceedTraced _
            · simp only [hnb0, if_false]
              apply traceErase_bind_reachable
                (TraceResult.tempPayloadRead? afterB.state.a
                  (Int.ofNat afterB.aPos))
                (mergeLoTempRead? afterB.state.a afterB.aPos)
                _ _ ((TraceResult.erase_tempPayloadRead _ _).trans
                  (mergeTempRead_ofNat _ _))
              intro firstA _
              apply traceErase_bindAcross_reachable
                  (gallopLeftTraced? afterB.state
                    (.main afterB.state.data afterB.bPos)
                    firstA.key afterB.nb 0)
                  (gallopLeft? afterB.state afterB.state.data afterB.bPos
                    firstA.key afterB.nb 0)
                  _ _ (erase_gallopLeftTraced_main _ _ _ _ _ _)
              intro gallopB _
              by_cases hbfuel : gallopB.fuelExhausted = true
              · simp only [hbfuel, if_true]
                exact erase_mergeLoFuelFailureTraced _
              · simp only [hbfuel]
                by_cases hbindex : gallopB.index > afterB.nb
                · simp only [hbindex, if_true]
                  rfl
                · simp only [hbindex, if_false]
                  simp only [Bool.false_eq_true, if_false]
                  let rawAfterMove (movedB : MergeState κ ν) :
                      Option (MergeLoResult κ ν) :=
                    let nextMachine : MergeLoMachine κ ν :=
                      { afterB with
                        state := movedB
                        dest := afterB.dest + Int.ofNat gallopB.index
                        bPos := afterB.bPos + Int.ofNat gallopB.index
                        nb := afterB.nb - gallopB.index }
                    if nextMachine.nb = 0 then
                      mergeLoSucceed? nextMachine
                    else do
                      let nextMachine ← mergeLoCopyAIncr? nextMachine
                      if nextMachine.na = 1 then
                        mergeLoCopyB? nextMachine
                      else
                        next nextMachine gallopA.index gallopB.index
                  change _ =
                    (afterB.state.data.memmove? afterB.dest afterB.bPos
                      gallopB.index).bind fun data =>
                        rawAfterMove { afterB.state with data := data }
                  rw [← mainDataMemmove_bind_eq_raw
                    afterB.state afterB.dest afterB.bPos gallopB.index
                    rawAfterMove]
                  apply traceErase_bind_reachable
                    (mainDataMemmoveTraced? afterB.state afterB.dest afterB.bPos
                      gallopB.index)
                    (mainDataMemmove? afterB.state afterB.dest afterB.bPos
                      gallopB.index)
                    _ _ (erase_mainDataMemmoveTraced _ _ _ _)
                  intro movedB _
                  dsimp [rawAfterMove]
                  by_cases hnbDone : afterB.nb - gallopB.index = 0
                  · simp only [hnbDone, if_true]
                    exact erase_mergeLoSucceedTraced _
                  · simp only [hnbDone, if_false]
                    apply traceErase_bind_reachable
                      (mergeLoCopyAIncrTraced? _)
                      (mergeLoCopyAIncr? _)
                      _ _ (erase_mergeLoCopyAIncrTraced _)
                    intro afterA _
                    by_cases hnaDone : afterA.na = 1
                    · simp only [hnaDone, if_true]
                      exact erase_mergeLoCopyBTraced _
                    · simp only [hnaDone, if_false]
                      exact hnext _ _ _

end CPythonListsort
