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
# `merge_hi` traced execution and safety

This module instruments the right-to-left merge directly.  Its evaluator does
not run `mergeHi?` and attach a second, decorative trace: every state transition
is produced by the typed operation that emits its access events.  The three
`memcpy` paths retain their exact source call-site tag and distinct-backing
permit, main-data block movement uses the overlap-safe traced `memmove`, and
temporary gallops read their live storage through `GallopKeySource.temporary`.
-/

namespace CPythonListsort

universe u v

variable {κ : Type u} {ν : Type v}

/-! ## Provenance permits -/

/-- Provenance certificate consumed by the initial main-to-temporary copy. -/
theorem mergeHiInitialDataToTempPermit :
    (MergeMemcpySite.hi .initialDataToTemp).MainToTempPermit :=
  { direction := rfl
    distinctBacking := MergeMemcpySite.distinct _ }

/-- Provenance certificate consumed by a galloping temporary-to-main copy. -/
theorem mergeHiGallopTempToDataPermit :
    (MergeMemcpySite.hi .gallopTempToData).TempToMainPermit :=
  { direction := rfl
    distinctBacking := MergeMemcpySite.distinct _ }

/-- Provenance certificate consumed by the final temporary remainder copy. -/
theorem mergeHiFinalTempToDataPermit :
    (MergeMemcpySite.hi .finalTempToData).TempToMainPermit :=
  { direction := rfl
    distinctBacking := MergeMemcpySite.distinct _ }

/-! ## Traced atomic merge operations -/

/-- Lift the reviewed, access-free prefix materializer into the trace monad.
The resulting slice is a semantic bridge only: gallop accesses still target
the physical temporary backing below. -/
def mergeHiTraceOption : Option α → TraceResult α
  | none => TraceResult.failure
  | some value => TraceResult.pure value

@[simp]
theorem erase_mergeHiTraceOption (value : Option α) :
    (mergeHiTraceOption value).erase = value := by
  cases value <;> rfl

/-- One overlap-safe main-data copy followed by decrementing both cursors. -/
def mergeHiCopyDataDecrTraced? (state : MergeState κ ν) (dst src : Int) :
    TraceResult (MergeHiDataCursorResult κ ν) :=
  mainDataCopyDecrTraced? state dst src

/-- One temporary-to-main copy followed by decrementing both cursors. -/
def mergeHiCopyTempDecrTraced? (state : MergeState κ ν) (dst src : Int) :
    TraceResult (MergeHiDataCursorResult κ ν) :=
  (tempToMainCellTraced? state dst src).map fun copied =>
    { state := copied, dst := dst - 1, src := src - 1 }

/-- Consume a suffix of the active left run with overlap-safe main movement. -/
def mergeHiMoveABlockTraced? (cursor : MergeHiCursor κ ν) (count : Nat) :
    TraceResult (MergeHiCursor κ ν) :=
  if count = 0 then
    TraceResult.pure cursor
  else
    let dest := cursor.dest - Int.ofNat count
    let ssa := cursor.ssa - Int.ofNat count
    (mainDataMemmoveTraced? cursor.state (dest + 1) (ssa + 1) count).map
      fun state =>
        { cursor with
          state := state
          dest := dest
          ssa := ssa
          na := cursor.na - count }

/-- Consume a suffix of the active temporary right run.  The tagged permit is
part of the operation, so no same-backing `memcpy` interpretation is possible. -/
def mergeHiMoveBBlockTraced? (cursor : MergeHiCursor κ ν) (count : Nat) :
    TraceResult (MergeHiCursor κ ν) :=
  if count = 0 then
    TraceResult.pure cursor
  else
    let dest := cursor.dest - Int.ofNat count
    let ssb := cursor.ssb - Int.ofNat count
    (tempToMainMemcpyTraced? (.hi .gallopTempToData)
      mergeHiGallopTempToDataPermit count cursor.state
      (dest + 1) (ssb + 1)).map fun state =>
        { cursor with
          state := state
          dest := dest
          ssb := ssb
          nb := cursor.nb - count }

def mergeHiMoveABlock? (cursor : MergeHiCursor κ ν) (count : Nat) :
    Option (MergeHiCursor κ ν) :=
  if count = 0 then
    some cursor
  else
    let dest := cursor.dest - Int.ofNat count
    let ssa := cursor.ssa - Int.ofNat count
    do
      let state ← mainDataMemmove? cursor.state (dest + 1) (ssa + 1) count
      some
        { cursor with
          state := state
          dest := dest
          ssa := ssa
          na := cursor.na - count }

def mergeHiMoveBBlock? (cursor : MergeHiCursor κ ν) (count : Nat) :
    Option (MergeHiCursor κ ν) :=
  if count = 0 then
    some cursor
  else
    let dest := cursor.dest - Int.ofNat count
    let ssb := cursor.ssb - Int.ofNat count
    do
      let state ← mergeHiMemcpyTempToData? .gallopTempToData rfl count
        cursor.state (dest + 1) (ssb + 1)
      some
        { cursor with
          state := state
          dest := dest
          ssb := ssb
          nb := cursor.nb - count }

/-- Observable merge-fuel exhaustion also marks trace fuel exhaustion. -/
def mergeHiFuelExhaustedTraced (cursor : MergeHiCursor κ ν) :
    TraceResult (MergeHiResult κ ν) :=
  (TraceResult.pure (mergeHiFuelExhausted cursor)).markFuelExhausted

/-- The successful remainder-copy tail shared by the C `Succeed` and `Fail`
labels. -/
def mergeHiSucceedTraced? (cursor : MergeHiCursor κ ν) :
    TraceResult (MergeHiResult κ ν) :=
  let copied :=
    if cursor.nb = 0 then
      TraceResult.pure cursor.state
    else
      tempToMainMemcpyTraced? (.hi .finalTempToData)
        mergeHiFinalTempToDataPermit cursor.nb cursor.state
        (cursor.dest - Int.ofNat (cursor.nb - 1)) 0
  copied.map fun state =>
    { state := state, returnCode := 0, fuelExhausted := false }

/-- The `CopyA` tail with one temporary right-run entry remaining. -/
def mergeHiCopyATraced? (cursor : MergeHiCursor κ ν) :
    TraceResult (MergeHiResult κ ν) :=
  if cursor.nb = 1 ∧ 0 < cursor.na then
    let offset := 1 - Int.ofNat cursor.na
    (mainDataMemmoveTraced? cursor.state
      (cursor.dest + offset) (cursor.ssa + offset) cursor.na).bind fun state =>
        (tempToMainCellTraced? state
          (cursor.dest - Int.ofNat cursor.na) cursor.ssb).map fun state =>
            { state := state, returnCode := 0, fuelExhausted := false }
  else
    TraceResult.failure

/-! ## Traced galloping and driver -/

private def mergeHiGallopBFinishTraced? (afterB : MergeHiCursor κ ν)
    (aCount bCount : Nat) (movedB : MergeHiCursor κ ν)
    (next : MergeHiCursor κ ν → TraceResult (MergeHiResult κ ν)) :
    TraceResult (MergeHiResult κ ν) :=
  if movedB.nb = 0 ∨ movedB.nb = 1 then
    next movedB
  else
    (mergeHiCopyDataDecrTraced? movedB.state movedB.dest
      movedB.ssa).bind fun copiedA =>
        let afterA : MergeHiCursor κ ν :=
          { movedB with
            state := copiedA.state
            dest := copiedA.dst
            ssa := copiedA.src
            na := movedB.na - 1 }
        if afterA.na = 0 then
          next afterA
        else if mergeHiCountAtLeast aCount MIN_GALLOP ||
            mergeHiCountAtLeast bCount MIN_GALLOP then
          next { afterA with phase := .galloping aCount bCount }
        else
          let minGallop := afterB.minGallop + 1
          let state := { afterA.state with min_gallop := minGallop }
          next
            { afterA with
              state := state
              minGallop := minGallop
              phase := .straight 0 0 }

private def mergeHiGallopBFinish? (afterB : MergeHiCursor κ ν)
    (aCount bCount : Nat) (movedB : MergeHiCursor κ ν)
    (next : MergeHiCursor κ ν → Option (MergeHiResult κ ν)) :
    Option (MergeHiResult κ ν) :=
  if movedB.nb = 0 ∨ movedB.nb = 1 then
    next movedB
  else
    (mergeHiCopyDataDecr? movedB.state movedB.dest movedB.ssa).bind
      fun copiedA =>
        let afterA : MergeHiCursor κ ν :=
          { movedB with
            state := copiedA.state
            dest := copiedA.dst
            ssa := copiedA.src
            na := movedB.na - 1 }
        if afterA.na = 0 then
          next afterA
        else if mergeHiCountAtLeast aCount MIN_GALLOP ||
            mergeHiCountAtLeast bCount MIN_GALLOP then
          next { afterA with phase := .galloping aCount bCount }
        else
          let minGallop := afterB.minGallop + 1
          let state := { afterA.state with min_gallop := minGallop }
          next
            { afterA with
              state := state
              minGallop := minGallop
              phase := .straight 0 0 }

private def mergeHiGallopBAfterTraced? (afterB : MergeHiCursor κ ν)
    (aCount : Nat) (gallopB : GallopResult)
    (next : MergeHiCursor κ ν → TraceResult (MergeHiResult κ ν)) :
    TraceResult (MergeHiResult κ ν) :=
  if gallopB.fuelExhausted then
    mergeHiFuelExhaustedTraced afterB
  else
    let bCount := afterB.nb - gallopB.index
    (mergeHiMoveBBlockTraced? afterB bCount).bind fun movedB =>
      mergeHiGallopBFinishTraced? afterB aCount bCount movedB next

private def mergeHiGallopBAfter? (afterB : MergeHiCursor κ ν)
    (aCount : Nat) (gallopB : GallopResult)
    (next : MergeHiCursor κ ν → Option (MergeHiResult κ ν)) :
    Option (MergeHiResult κ ν) :=
  if gallopB.fuelExhausted then
    some (mergeHiFuelExhausted afterB)
  else
    let bCount := afterB.nb - gallopB.index
    (mergeHiMoveBBlock? afterB bCount).bind fun movedB =>
      mergeHiGallopBFinish? afterB aCount bCount movedB next

/-- Second half of a `merge_hi` galloping round.  The temporary gallop uses
the real temporary backing directly; no synthetic `SortSlice` access is
recorded. -/
def mergeHiGallopBTraced? (afterB : MergeHiCursor κ ν) (aCount : Nat)
    (next : MergeHiCursor κ ν → TraceResult (MergeHiResult κ ν)) :
    TraceResult (MergeHiResult κ ν) :=
  (TraceResult.sortSliceKeysRead? afterB.state.data afterB.ssa).bind fun left =>
    (mergeHiTraceOption
      (initializedTempPrefix? afterB.state.a afterB.nb)).bind fun _temp =>
      (gallopLeftTraced? afterB.state
        (.temporary afterB.state.a 0) left.key afterB.nb
        (afterB.nb - 1)).bind fun gallopB =>
        mergeHiGallopBAfterTraced? afterB aCount gallopB next

private def mergeHiGallopRoundFinishTraced? (movedA : MergeHiCursor κ ν)
    (aCount : Nat)
    (next : MergeHiCursor κ ν → TraceResult (MergeHiResult κ ν)) :
    TraceResult (MergeHiResult κ ν) :=
  if movedA.na = 0 then
    next movedA
  else
    (mergeHiCopyTempDecrTraced? movedA.state movedA.dest movedA.ssb).bind
      fun copiedB =>
        let afterB : MergeHiCursor κ ν :=
          { movedA with
            state := copiedB.state
            dest := copiedB.dst
            ssb := copiedB.src
            nb := movedA.nb - 1 }
        if afterB.nb = 1 then
          next afterB
        else
          mergeHiGallopBTraced? afterB aCount next

private def mergeHiGallopRoundFinish? (movedA : MergeHiCursor κ ν)
    (aCount : Nat)
    (next : MergeHiCursor κ ν → Option (MergeHiResult κ ν)) :
    Option (MergeHiResult κ ν) :=
  if movedA.na = 0 then
    next movedA
  else
    (mergeHiCopyTempDecr? movedA.state movedA.dest movedA.ssb).bind
      fun copiedB =>
        let afterB : MergeHiCursor κ ν :=
          { movedA with
            state := copiedB.state
            dest := copiedB.dst
            ssb := copiedB.src
            nb := movedA.nb - 1 }
        if afterB.nb = 1 then
          next afterB
        else
          mergeHiGallopB? afterB aCount next

private def mergeHiGallopRoundAfterTraced? (cursor : MergeHiCursor κ ν)
    (minGallop : PySSize) (state : MergeState κ ν) (gallopA : GallopResult)
    (next : MergeHiCursor κ ν → TraceResult (MergeHiResult κ ν)) :
    TraceResult (MergeHiResult κ ν) :=
  if gallopA.fuelExhausted then
    mergeHiFuelExhaustedTraced { cursor with state := state }
  else
    let aCount := cursor.na - gallopA.index
    (mergeHiMoveABlockTraced?
      { cursor with state := state, minGallop := minGallop } aCount).bind
      fun movedA => mergeHiGallopRoundFinishTraced? movedA aCount next

private def mergeHiGallopRoundAfter? (cursor : MergeHiCursor κ ν)
    (minGallop : PySSize) (state : MergeState κ ν) (gallopA : GallopResult)
    (next : MergeHiCursor κ ν → Option (MergeHiResult κ ν)) :
    Option (MergeHiResult κ ν) :=
  if gallopA.fuelExhausted then
    some (mergeHiFuelExhausted { cursor with state := state })
  else
    let aCount := cursor.na - gallopA.index
    (mergeHiMoveABlock?
      { cursor with state := state, minGallop := minGallop } aCount).bind
      fun movedA => mergeHiGallopRoundFinish? movedA aCount next

/-- One complete traced `merge_hi` galloping round. -/
def mergeHiGallopRoundTraced? (cursor : MergeHiCursor κ ν)
    (next : MergeHiCursor κ ν → TraceResult (MergeHiResult κ ν)) :
    TraceResult (MergeHiResult κ ν) :=
  let minGallop := mergeHiDecreaseMinGallop cursor.minGallop
  let state := { cursor.state with min_gallop := minGallop }
  (TraceResult.tempPayloadRead? state.a cursor.ssb).bind fun right =>
    (gallopRightTraced? state (.main state.data cursor.basea) right.key
      cursor.na (cursor.na - 1)).bind fun gallopA =>
        mergeHiGallopRoundAfterTraced? cursor minGallop state gallopA next

/-- Fuel-bounded traced phase machine.  A live nonterminal zero-fuel state
marks trace exhaustion instead of returning an access-free failure. -/
def mergeHiLoopTraced? :
    Nat → MergeHiCursor κ ν → TraceResult (MergeHiResult κ ν)
  | 0, cursor =>
      if cursor.na = 0 ∨ cursor.nb = 0 then
        mergeHiSucceedTraced? cursor
      else if cursor.nb = 1 then
        mergeHiCopyATraced? cursor
      else
        mergeHiFuelExhaustedTraced cursor
  | fuel + 1, cursor =>
      if cursor.na = 0 ∨ cursor.nb = 0 then
        mergeHiSucceedTraced? cursor
      else if cursor.nb = 1 then
        mergeHiCopyATraced? cursor
      else
        match cursor.phase with
        | .straight aCount bCount =>
            (TraceResult.tempPayloadRead? cursor.state.a cursor.ssb).bind
              fun right =>
                (TraceResult.sortSliceKeysRead? cursor.state.data cursor.ssa).bind
                  fun left =>
                    if iflt cursor.state.key_compare right.key left.key then
                      (mergeHiCopyDataDecrTraced? cursor.state cursor.dest
                        cursor.ssa).bind fun copied =>
                          let aCount := aCount + 1
                          let next : MergeHiCursor κ ν :=
                            { cursor with
                              state := copied.state
                              dest := copied.dst
                              ssa := copied.src
                              na := cursor.na - 1
                              phase :=
                                if mergeHiCountAtLeast aCount cursor.minGallop then
                                  .galloping aCount 0
                                else
                                  .straight aCount 0
                              minGallop :=
                                if mergeHiCountAtLeast aCount cursor.minGallop then
                                  cursor.minGallop + 1
                                else
                                  cursor.minGallop }
                          mergeHiLoopTraced? fuel next
                    else
                      (mergeHiCopyTempDecrTraced? cursor.state cursor.dest
                        cursor.ssb).bind fun copied =>
                          let bCount := bCount + 1
                          let next : MergeHiCursor κ ν :=
                            { cursor with
                              state := copied.state
                              dest := copied.dst
                              ssb := copied.src
                              nb := cursor.nb - 1
                              phase :=
                                if mergeHiCountAtLeast bCount cursor.minGallop then
                                  .galloping 0 bCount
                                else
                                  .straight 0 bCount
                              minGallop :=
                                if mergeHiCountAtLeast bCount cursor.minGallop then
                                  cursor.minGallop + 1
                                else
                                  cursor.minGallop }
                          mergeHiLoopTraced? fuel next
        | .galloping _ _ =>
            mergeHiGallopRoundTraced? cursor (mergeHiLoopTraced? fuel)

/-! ## Public evaluator -/

/-- Directly traced transcription of CPython's right-to-left merge. -/
def mergeHiTraced? (state : MergeState κ ν) (ssa ssb : Int) (na nb : Nat) :
    TraceResult (MergeHiResult κ ν) :=
  if 0 < na ∧ 0 < nb ∧ na ≤ PY_SSIZE_T_MAX ∧ nb ≤ PY_SSIZE_T_MAX ∧
      ssa + Int.ofNat na = ssb then
    let allocated := mergeGetmem state (BitVec.ofNat 64 nb)
    match allocated.outcome with
    | .guardRejected =>
        TraceResult.pure
          { state := allocated.state
            returnCode := -1
            fuelExhausted := false }
    | .reused | .grown =>
        (mainToTempMemcpyTraced? (.hi .initialDataToTemp)
          mergeHiInitialDataToTempPermit nb allocated.state 0 ssb).bind fun state =>
            let dest := ssb + Int.ofNat (nb - 1)
            let ssaCursor := ssa + Int.ofNat (na - 1)
            (mergeHiCopyDataDecrTraced? state dest ssaCursor).bind fun copied =>
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
              mergeHiLoopTraced? (na + nb) cursor
  else
    TraceResult.failure

/-! ## Absence of nested merge-memory and policy events -/

/-- A local trace fragment contains neither a top-level merge-memory boundary
nor a merge-policy event.  The shared structural induction below pins both
absence claims. -/
private def MergeHiMemoryEventFree (execution : TraceResult α) : Prop :=
  execution.trace.memoryEvents = [] ∧ execution.trace.policyEvents = []

private theorem mergeHiMemoryEventFree_pure (value : α) :
    MergeHiMemoryEventFree (TraceResult.pure value) := by
  exact ⟨rfl, rfl⟩

private theorem mergeHiMemoryEventFree_failure :
    MergeHiMemoryEventFree (TraceResult.failure : TraceResult α) := by
  exact ⟨rfl, rfl⟩

private theorem mergeHiMemoryEventFree_map (current : TraceResult α)
    (transform : α → β) (hcurrent : MergeHiMemoryEventFree current) :
    MergeHiMemoryEventFree (current.map transform) :=
  hcurrent

private theorem mergeHiMemoryEventFree_bind (current : TraceResult α)
    (next : α → TraceResult β) (hcurrent : MergeHiMemoryEventFree current)
    (hnext : ∀ value, MergeHiMemoryEventFree (next value)) :
    MergeHiMemoryEventFree (current.bind next) := by
  exact
    ⟨TraceResult.memoryEvents_bind_eq_nil current next hcurrent.1
        (fun value => (hnext value).1),
      TraceResult.policyEvents_bind_eq_nil current next hcurrent.2
        (fun value => (hnext value).2)⟩

private theorem mergeHiMemoryEventFree_markFuelExhausted
    (current : TraceResult α) (hcurrent : MergeHiMemoryEventFree current) :
    MergeHiMemoryEventFree current.markFuelExhausted := by
  simpa [MergeHiMemoryEventFree, TraceResult.markFuelExhausted,
    AccessTrace.compose, AccessTrace.exhausted] using hcurrent

private theorem mergeHiMemoryEventFree_sourceRead
    (source : GallopKeySource κ ν) (index : Int) :
    MergeHiMemoryEventFree (source.readTraced? index) := by
  simp [MergeHiMemoryEventFree, GallopKeySource.trace_readTraced,
    AccessTrace.singletonAccess]

private theorem mergeHiMemoryEventFree_tempRead
    (storage : TempStorage κ ν) (index : Int) :
    MergeHiMemoryEventFree (TraceResult.tempPayloadRead? storage index) := by
  unfold MergeHiMemoryEventFree
  rw [TraceResult.trace_tempPayloadRead]
  exact ⟨rfl, rfl⟩

private theorem mergeHiMemoryEventFree_tempWrite
    (storage : TempStorage κ ν) (index : Int)
    (entry : SortSliceEntry κ ν) :
    MergeHiMemoryEventFree
      (TraceResult.tempPayloadWrite? storage index entry) := by
  exact ⟨rfl, rfl⟩

private theorem mergeHiMemoryEventFree_keyRead
    (slice : SortSlice κ ν) (index : Int) :
    MergeHiMemoryEventFree (TraceResult.sortSliceKeysRead? slice index) := by
  exact ⟨rfl, rfl⟩

private theorem mergeHiMemoryEventFree_valueRead
    (slice : SortSlice κ ν) (index : Int) :
    MergeHiMemoryEventFree (TraceResult.sortSliceValuesRead? slice index) := by
  exact ⟨rfl, rfl⟩

private theorem mergeHiMemoryEventFree_keyWrite
    (slice : SortSlice κ ν) (index : Int) (entry : SortSliceEntry κ ν) :
    MergeHiMemoryEventFree
      (TraceResult.sortSliceKeysWrite? slice index entry) := by
  exact ⟨rfl, rfl⟩

private theorem mergeHiMemoryEventFree_valueWrite
    (slice : SortSlice κ ν) (index : Int) (entry : SortSliceEntry κ ν) :
    MergeHiMemoryEventFree
      (TraceResult.sortSliceValuesWrite? slice index entry) := by
  exact ⟨rfl, rfl⟩

private theorem mergeHiMemoryEventFree_copyKeys
    (destination source : SortSlice κ ν) (dst src : Int) :
    MergeHiMemoryEventFree
      (SortSlice.copyKeysFromTraced? destination source dst src) := by
  apply mergeHiMemoryEventFree_bind
  · exact mergeHiMemoryEventFree_keyRead _ _
  · intro entry
    exact mergeHiMemoryEventFree_keyWrite _ _ _

private theorem mergeHiMemoryEventFree_copyValues
    (destination source : SortSlice κ ν) (dst src : Int) :
    MergeHiMemoryEventFree
      (SortSlice.copyValuesFromTraced? destination source dst src) := by
  apply mergeHiMemoryEventFree_bind
  · exact mergeHiMemoryEventFree_valueRead _ _
  · intro entry
    exact mergeHiMemoryEventFree_valueWrite _ _ _

private theorem mergeHiMemoryEventFree_mainToTempKey
    (state : MergeState κ ν) (tempDst mainSrc : Int) :
    MergeHiMemoryEventFree (mainToTempKeyTraced? state tempDst mainSrc) := by
  unfold mainToTempKeyTraced?
  apply mergeHiMemoryEventFree_bind
  · exact mergeHiMemoryEventFree_keyRead _ _
  · intro entry
    apply mergeHiMemoryEventFree_map
    exact mergeHiMemoryEventFree_tempWrite _ _ _

private theorem mergeHiMemoryEventFree_mainToTempValues
    (state : MergeState κ ν) (tempDst mainSrc : Int) :
    MergeHiMemoryEventFree (mainToTempValuesTraced? state tempDst mainSrc) := by
  unfold mainToTempValuesTraced?
  apply mergeHiMemoryEventFree_bind
  · exact mergeHiMemoryEventFree_valueRead _ _
  · intro entry
    apply mergeHiMemoryEventFree_map
    exact mergeHiMemoryEventFree_tempWrite _ _ _

private theorem mergeHiMemoryEventFree_tempToMainKey
    (state : MergeState κ ν) (mainDst tempSrc : Int) :
    MergeHiMemoryEventFree (tempToMainKeyTraced? state mainDst tempSrc) := by
  unfold tempToMainKeyTraced?
  apply mergeHiMemoryEventFree_bind
  · exact mergeHiMemoryEventFree_tempRead _ _
  · intro entry
    apply mergeHiMemoryEventFree_map
    exact mergeHiMemoryEventFree_keyWrite _ _ _

private theorem mergeHiMemoryEventFree_tempToMainValues
    (state : MergeState κ ν) (mainDst tempSrc : Int) :
    MergeHiMemoryEventFree (tempToMainValuesTraced? state mainDst tempSrc) := by
  unfold tempToMainValuesTraced?
  apply mergeHiMemoryEventFree_bind
  · exact mergeHiMemoryEventFree_tempRead _ _
  · intro entry
    apply mergeHiMemoryEventFree_map
    exact mergeHiMemoryEventFree_valueWrite _ _ _

private theorem mergeHiMemoryEventFree_tempToMainCell
    (state : MergeState κ ν) (mainDst tempSrc : Int) :
    MergeHiMemoryEventFree (tempToMainCellTraced? state mainDst tempSrc) := by
  unfold tempToMainCellTraced?
  apply mergeHiMemoryEventFree_bind
  · exact mergeHiMemoryEventFree_tempToMainKey _ _ _
  · intro keyResult
    split
    · exact mergeHiMemoryEventFree_tempToMainValues _ _ _
    · exact mergeHiMemoryEventFree_pure _

private theorem mergeHiMemoryEventFree_mainToTempKeys
    (site : MergeMemcpySite) (permit : site.MainToTempPermit) (count : Nat)
    (state : MergeState κ ν) (tempDst mainSrc : Int) :
    MergeHiMemoryEventFree
      (mainToTempKeysTraced? site permit count state tempDst mainSrc) := by
  induction count generalizing state tempDst mainSrc with
  | zero => exact mergeHiMemoryEventFree_pure _
  | succ count ih =>
      simp only [mainToTempKeysTraced?]
      apply mergeHiMemoryEventFree_bind
      · exact mergeHiMemoryEventFree_mainToTempKey _ _ _
      · intro nextState
        exact ih _ _ _

private theorem mergeHiMemoryEventFree_mainToTempValuesPhase
    (site : MergeMemcpySite) (permit : site.MainToTempPermit) (count : Nat)
    (state : MergeState κ ν) (tempDst mainSrc : Int) :
    MergeHiMemoryEventFree
      (mainToTempValuesPhaseTraced? site permit count state tempDst mainSrc) := by
  induction count generalizing state tempDst mainSrc with
  | zero => exact mergeHiMemoryEventFree_pure _
  | succ count ih =>
      simp only [mainToTempValuesPhaseTraced?]
      apply mergeHiMemoryEventFree_bind
      · exact mergeHiMemoryEventFree_mainToTempValues _ _ _
      · intro nextState
        exact ih _ _ _

private theorem mergeHiMemoryEventFree_mainToTempMemcpy
    (site : MergeMemcpySite) (permit : site.MainToTempPermit) (count : Nat)
    (state : MergeState κ ν) (tempDst mainSrc : Int) :
    MergeHiMemoryEventFree
      (mainToTempMemcpyTraced? site permit count state tempDst mainSrc) := by
  unfold mainToTempMemcpyTraced?
  apply mergeHiMemoryEventFree_bind
  · exact mergeHiMemoryEventFree_mainToTempKeys _ _ _ _ _ _
  · intro keyResult
    split
    · exact mergeHiMemoryEventFree_mainToTempValuesPhase _ _ _ _ _ _
    · exact mergeHiMemoryEventFree_pure _

private theorem mergeHiMemoryEventFree_tempToMainKeys
    (site : MergeMemcpySite) (permit : site.TempToMainPermit) (count : Nat)
    (state : MergeState κ ν) (mainDst tempSrc : Int) :
    MergeHiMemoryEventFree
      (tempToMainKeysTraced? site permit count state mainDst tempSrc) := by
  induction count generalizing state mainDst tempSrc with
  | zero => exact mergeHiMemoryEventFree_pure _
  | succ count ih =>
      simp only [tempToMainKeysTraced?]
      apply mergeHiMemoryEventFree_bind
      · exact mergeHiMemoryEventFree_tempToMainKey _ _ _
      · intro nextState
        exact ih _ _ _

private theorem mergeHiMemoryEventFree_tempToMainValuesPhase
    (site : MergeMemcpySite) (permit : site.TempToMainPermit) (count : Nat)
    (state : MergeState κ ν) (mainDst tempSrc : Int) :
    MergeHiMemoryEventFree
      (tempToMainValuesPhaseTraced? site permit count state mainDst tempSrc) := by
  induction count generalizing state mainDst tempSrc with
  | zero => exact mergeHiMemoryEventFree_pure _
  | succ count ih =>
      simp only [tempToMainValuesPhaseTraced?]
      apply mergeHiMemoryEventFree_bind
      · exact mergeHiMemoryEventFree_tempToMainValues _ _ _
      · intro nextState
        exact ih _ _ _

private theorem mergeHiMemoryEventFree_tempToMainMemcpy
    (site : MergeMemcpySite) (permit : site.TempToMainPermit) (count : Nat)
    (state : MergeState κ ν) (mainDst tempSrc : Int) :
    MergeHiMemoryEventFree
      (tempToMainMemcpyTraced? site permit count state mainDst tempSrc) := by
  unfold tempToMainMemcpyTraced?
  apply mergeHiMemoryEventFree_bind
  · exact mergeHiMemoryEventFree_tempToMainKeys _ _ _ _ _ _
  · intro keyResult
    split
    · exact mergeHiMemoryEventFree_tempToMainValuesPhase _ _ _ _ _ _
    · exact mergeHiMemoryEventFree_pure _

private theorem mergeHiMemoryEventFree_memmoveForwardKeys
    (count : Nat) (slice : SortSlice κ ν) (dst src : Int) :
    MergeHiMemoryEventFree
      (SortSlice.memmoveForwardKeysTraced? count slice dst src) := by
  induction count generalizing slice dst src with
  | zero => exact mergeHiMemoryEventFree_pure _
  | succ count ih =>
      simp only [SortSlice.memmoveForwardKeysTraced?]
      apply mergeHiMemoryEventFree_bind
      · exact mergeHiMemoryEventFree_copyKeys _ _ _ _
      · intro updated
        exact ih _ _ _

private theorem mergeHiMemoryEventFree_memmoveForwardValues
    (count : Nat) (slice : SortSlice κ ν) (dst src : Int) :
    MergeHiMemoryEventFree
      (SortSlice.memmoveForwardValuesTraced? count slice dst src) := by
  induction count generalizing slice dst src with
  | zero => exact mergeHiMemoryEventFree_pure _
  | succ count ih =>
      simp only [SortSlice.memmoveForwardValuesTraced?]
      apply mergeHiMemoryEventFree_bind
      · exact mergeHiMemoryEventFree_copyValues _ _ _ _
      · intro updated
        exact ih _ _ _

private theorem mergeHiMemoryEventFree_memmoveBackwardKeys
    (count : Nat) (slice : SortSlice κ ν) (dst src : Int) :
    MergeHiMemoryEventFree
      (SortSlice.memmoveBackwardKeysTraced? count slice dst src) := by
  induction count generalizing slice dst src with
  | zero => exact mergeHiMemoryEventFree_pure _
  | succ count ih =>
      simp only [SortSlice.memmoveBackwardKeysTraced?]
      apply mergeHiMemoryEventFree_bind
      · exact mergeHiMemoryEventFree_copyKeys _ _ _ _
      · intro updated
        exact ih _ _ _

private theorem mergeHiMemoryEventFree_memmoveBackwardValues
    (count : Nat) (slice : SortSlice κ ν) (dst src : Int) :
    MergeHiMemoryEventFree
      (SortSlice.memmoveBackwardValuesTraced? count slice dst src) := by
  induction count generalizing slice dst src with
  | zero => exact mergeHiMemoryEventFree_pure _
  | succ count ih =>
      simp only [SortSlice.memmoveBackwardValuesTraced?]
      apply mergeHiMemoryEventFree_bind
      · exact mergeHiMemoryEventFree_copyValues _ _ _ _
      · intro updated
        exact ih _ _ _

private theorem mergeHiMemoryEventFree_memmove
    (valuesPresent : Bool) (slice : SortSlice κ ν)
    (dst src : Int) (count : Nat) :
    MergeHiMemoryEventFree
      (SortSlice.memmoveTraced? valuesPresent slice dst src count) := by
  unfold SortSlice.memmoveTraced?
  split
  · apply mergeHiMemoryEventFree_bind
    · exact mergeHiMemoryEventFree_memmoveForwardKeys _ _ _ _
    · intro keyResult
      split
      · exact mergeHiMemoryEventFree_memmoveForwardValues _ _ _ _
      · exact mergeHiMemoryEventFree_pure _
  · apply mergeHiMemoryEventFree_bind
    · exact mergeHiMemoryEventFree_memmoveBackwardKeys _ _ _ _
    · intro keyResult
      split
      · exact mergeHiMemoryEventFree_memmoveBackwardValues _ _ _ _
      · exact mergeHiMemoryEventFree_pure _

private theorem mergeHiMemoryEventFree_mainDataMemmove
    (state : MergeState κ ν) (dst src : Int) (count : Nat) :
    MergeHiMemoryEventFree (mainDataMemmoveTraced? state dst src count) := by
  unfold mainDataMemmoveTraced?
  apply mergeHiMemoryEventFree_map
  exact mergeHiMemoryEventFree_memmove _ _ _ _ _

set_option linter.flexible false in
private theorem mergeHiMemoryEventFree_leftRightExponential
    (fuel : Nat) (lt : BoolComparator κ) (source : GallopKeySource κ ν)
    (key : κ) (hint maxOffset lastOffset offset : Nat) :
    MergeHiMemoryEventFree
      (gallopLeftRightExponentialTraced? fuel lt source key hint maxOffset
        lastOffset offset) := by
  induction fuel generalizing lastOffset offset with
  | zero =>
      by_cases hfuel : offset < maxOffset <;>
        simp [gallopLeftRightExponentialTraced?, MergeHiMemoryEventFree,
          hfuel] <;> (constructor <;> rfl)
  | succ fuel ih =>
      simp only [gallopLeftRightExponentialTraced?]
      split
      · apply mergeHiMemoryEventFree_bind
        · exact mergeHiMemoryEventFree_sourceRead _ _
        · intro entry
          split
          · split
            · exact ih _ _
            · exact mergeHiMemoryEventFree_failure
          · exact mergeHiMemoryEventFree_pure _
      · exact mergeHiMemoryEventFree_pure _

set_option linter.flexible false in
private theorem mergeHiMemoryEventFree_leftLeftExponential
    (fuel : Nat) (lt : BoolComparator κ) (source : GallopKeySource κ ν)
    (key : κ) (hint maxOffset lastOffset offset : Nat) :
    MergeHiMemoryEventFree
      (gallopLeftLeftExponentialTraced? fuel lt source key hint maxOffset
        lastOffset offset) := by
  induction fuel generalizing lastOffset offset with
  | zero =>
      by_cases hfuel : offset < maxOffset <;>
        simp [gallopLeftLeftExponentialTraced?, MergeHiMemoryEventFree,
          hfuel] <;> (constructor <;> rfl)
  | succ fuel ih =>
      simp only [gallopLeftLeftExponentialTraced?]
      split
      · apply mergeHiMemoryEventFree_bind
        · exact mergeHiMemoryEventFree_sourceRead _ _
        · intro entry
          split
          · exact mergeHiMemoryEventFree_pure _
          · split
            · exact ih _ _
            · exact mergeHiMemoryEventFree_failure
      · exact mergeHiMemoryEventFree_pure _

set_option linter.flexible false in
private theorem mergeHiMemoryEventFree_rightLeftExponential
    (fuel : Nat) (lt : BoolComparator κ) (source : GallopKeySource κ ν)
    (key : κ) (hint maxOffset lastOffset offset : Nat) :
    MergeHiMemoryEventFree
      (gallopRightLeftExponentialTraced? fuel lt source key hint maxOffset
        lastOffset offset) := by
  induction fuel generalizing lastOffset offset with
  | zero =>
      by_cases hfuel : offset < maxOffset <;>
        simp [gallopRightLeftExponentialTraced?, MergeHiMemoryEventFree,
          hfuel] <;> (constructor <;> rfl)
  | succ fuel ih =>
      simp only [gallopRightLeftExponentialTraced?]
      split
      · apply mergeHiMemoryEventFree_bind
        · exact mergeHiMemoryEventFree_sourceRead _ _
        · intro entry
          split
          · split
            · exact ih _ _
            · exact mergeHiMemoryEventFree_failure
          · exact mergeHiMemoryEventFree_pure _
      · exact mergeHiMemoryEventFree_pure _

set_option linter.flexible false in
private theorem mergeHiMemoryEventFree_rightRightExponential
    (fuel : Nat) (lt : BoolComparator κ) (source : GallopKeySource κ ν)
    (key : κ) (hint maxOffset lastOffset offset : Nat) :
    MergeHiMemoryEventFree
      (gallopRightRightExponentialTraced? fuel lt source key hint maxOffset
        lastOffset offset) := by
  induction fuel generalizing lastOffset offset with
  | zero =>
      by_cases hfuel : offset < maxOffset <;>
        simp [gallopRightRightExponentialTraced?, MergeHiMemoryEventFree,
          hfuel] <;> (constructor <;> rfl)
  | succ fuel ih =>
      simp only [gallopRightRightExponentialTraced?]
      split
      · apply mergeHiMemoryEventFree_bind
        · exact mergeHiMemoryEventFree_sourceRead _ _
        · intro entry
          split
          · exact mergeHiMemoryEventFree_pure _
          · split
            · exact ih _ _
            · exact mergeHiMemoryEventFree_failure
      · exact mergeHiMemoryEventFree_pure _

set_option linter.flexible false in
private theorem mergeHiMemoryEventFree_leftBinary
    (fuel : Nat) (lt : BoolComparator κ) (source : GallopKeySource κ ν)
    (key : κ) (lower upper : Nat) :
    MergeHiMemoryEventFree
      (gallopLeftBinaryTraced? fuel lt source key lower upper) := by
  induction fuel generalizing lower upper with
  | zero =>
      by_cases hfuel : lower < upper <;>
        simp [gallopLeftBinaryTraced?, MergeHiMemoryEventFree, hfuel] <;>
          (constructor <;> rfl)
  | succ fuel ih =>
      simp only [gallopLeftBinaryTraced?]
      split
      · apply mergeHiMemoryEventFree_bind
        · exact mergeHiMemoryEventFree_sourceRead _ _
        · intro entry
          split
          · exact ih _ _
          · exact ih _ _
      · exact mergeHiMemoryEventFree_pure _

set_option linter.flexible false in
private theorem mergeHiMemoryEventFree_rightBinary
    (fuel : Nat) (lt : BoolComparator κ) (source : GallopKeySource κ ν)
    (key : κ) (lower upper : Nat) :
    MergeHiMemoryEventFree
      (gallopRightBinaryTraced? fuel lt source key lower upper) := by
  induction fuel generalizing lower upper with
  | zero =>
      by_cases hfuel : lower < upper <;>
        simp [gallopRightBinaryTraced?, MergeHiMemoryEventFree, hfuel] <;>
          (constructor <;> rfl)
  | succ fuel ih =>
      simp only [gallopRightBinaryTraced?]
      split
      · apply mergeHiMemoryEventFree_bind
        · exact mergeHiMemoryEventFree_sourceRead _ _
        · intro entry
          split
          · exact ih _ _
          · exact ih _ _
      · exact mergeHiMemoryEventFree_pure _

private theorem mergeHiMemoryEventFree_finishLeft
    (fuel : Nat) (lt : BoolComparator κ) (source : GallopKeySource κ ν)
    (key : κ) (n : Nat) (lastOffset upperOffset : Int)
    (exponentialFuelExhausted : Bool) :
    MergeHiMemoryEventFree
      (finishGallopLeftTraced? fuel lt source key n lastOffset upperOffset
        exponentialFuelExhausted) := by
  unfold finishGallopLeftTraced?
  split
  · dsimp only
    split
    · split
      · constructor <;> rfl
      · exact mergeHiMemoryEventFree_leftBinary _ _ _ _ _ _
    · exact mergeHiMemoryEventFree_failure
  · exact mergeHiMemoryEventFree_failure

private theorem mergeHiMemoryEventFree_finishRight
    (fuel : Nat) (lt : BoolComparator κ) (source : GallopKeySource κ ν)
    (key : κ) (n : Nat) (lastOffset upperOffset : Int)
    (exponentialFuelExhausted : Bool) :
    MergeHiMemoryEventFree
      (finishGallopRightTraced? fuel lt source key n lastOffset upperOffset
        exponentialFuelExhausted) := by
  unfold finishGallopRightTraced?
  split
  · dsimp only
    split
    · split
      · constructor <;> rfl
      · exact mergeHiMemoryEventFree_rightBinary _ _ _ _ _ _
    · exact mergeHiMemoryEventFree_failure
  · exact mergeHiMemoryEventFree_failure

private theorem mergeHiMemoryEventFree_gallopLeft
    (state : MergeState κ ν) (source : GallopKeySource κ ν)
    (key : κ) (n hint : Nat) :
    MergeHiMemoryEventFree (gallopLeftTraced? state source key n hint) := by
  unfold gallopLeftTraced?
  split
  · apply mergeHiMemoryEventFree_bind
    · exact mergeHiMemoryEventFree_sourceRead _ _
    · intro hinted
      split
      · apply mergeHiMemoryEventFree_bind
        · exact mergeHiMemoryEventFree_leftRightExponential _ _ _ _ _ _ _ _
        · intro exponential
          exact mergeHiMemoryEventFree_finishLeft _ _ _ _ _ _ _ _
      · apply mergeHiMemoryEventFree_bind
        · exact mergeHiMemoryEventFree_leftLeftExponential _ _ _ _ _ _ _ _
        · intro exponential
          exact mergeHiMemoryEventFree_finishLeft _ _ _ _ _ _ _ _
  · exact mergeHiMemoryEventFree_failure

private theorem mergeHiMemoryEventFree_gallopRight
    (state : MergeState κ ν) (source : GallopKeySource κ ν)
    (key : κ) (n hint : Nat) :
    MergeHiMemoryEventFree (gallopRightTraced? state source key n hint) := by
  unfold gallopRightTraced?
  split
  · apply mergeHiMemoryEventFree_bind
    · exact mergeHiMemoryEventFree_sourceRead _ _
    · intro hinted
      split
      · apply mergeHiMemoryEventFree_bind
        · exact mergeHiMemoryEventFree_rightLeftExponential _ _ _ _ _ _ _ _
        · intro exponential
          exact mergeHiMemoryEventFree_finishRight _ _ _ _ _ _ _ _
      · apply mergeHiMemoryEventFree_bind
        · exact mergeHiMemoryEventFree_rightRightExponential _ _ _ _ _ _ _ _
        · intro exponential
          exact mergeHiMemoryEventFree_finishRight _ _ _ _ _ _ _ _
  · exact mergeHiMemoryEventFree_failure

private theorem mergeHiMemoryEventFree_copyFrom
    (valuesPresent : Bool) (destination source : SortSlice κ ν)
    (dst src : Int) :
    MergeHiMemoryEventFree
      (SortSlice.copyFromTraced? valuesPresent destination source dst src) := by
  unfold SortSlice.copyFromTraced?
  apply mergeHiMemoryEventFree_bind
  · exact mergeHiMemoryEventFree_copyKeys _ _ _ _
  · intro keyResult
    split
    · exact mergeHiMemoryEventFree_copyValues _ _ _ _
    · exact mergeHiMemoryEventFree_pure _

private theorem mergeHiMemoryEventFree_mainDataCopyDecr
    (state : MergeState κ ν) (dst src : Int) :
    MergeHiMemoryEventFree (mainDataCopyDecrTraced? state dst src) := by
  unfold mainDataCopyDecrTraced? SortSlice.copyDecrTraced?
    SortSlice.copyFromDecrTraced?
  apply mergeHiMemoryEventFree_map
  exact mergeHiMemoryEventFree_copyFrom _ _ _ _ _

private theorem mergeHiMemoryEventFree_copyDataDecr
    (state : MergeState κ ν) (dst src : Int) :
    MergeHiMemoryEventFree (mergeHiCopyDataDecrTraced? state dst src) := by
  exact mergeHiMemoryEventFree_mainDataCopyDecr _ _ _

private theorem mergeHiMemoryEventFree_copyTempDecr
    (state : MergeState κ ν) (dst src : Int) :
    MergeHiMemoryEventFree (mergeHiCopyTempDecrTraced? state dst src) := by
  unfold mergeHiCopyTempDecrTraced?
  apply mergeHiMemoryEventFree_map
  exact mergeHiMemoryEventFree_tempToMainCell _ _ _

private theorem mergeHiMemoryEventFree_moveABlock
    (cursor : MergeHiCursor κ ν) (count : Nat) :
    MergeHiMemoryEventFree (mergeHiMoveABlockTraced? cursor count) := by
  unfold mergeHiMoveABlockTraced?
  split
  · exact mergeHiMemoryEventFree_pure _
  · dsimp only
    apply mergeHiMemoryEventFree_map
    exact mergeHiMemoryEventFree_mainDataMemmove _ _ _ _

private theorem mergeHiMemoryEventFree_moveBBlock
    (cursor : MergeHiCursor κ ν) (count : Nat) :
    MergeHiMemoryEventFree (mergeHiMoveBBlockTraced? cursor count) := by
  unfold mergeHiMoveBBlockTraced?
  split
  · exact mergeHiMemoryEventFree_pure _
  · dsimp only
    apply mergeHiMemoryEventFree_map
    exact mergeHiMemoryEventFree_tempToMainMemcpy _ _ _ _ _ _

private theorem mergeHiMemoryEventFree_fuelExhausted
    (cursor : MergeHiCursor κ ν) :
    MergeHiMemoryEventFree (mergeHiFuelExhaustedTraced cursor) := by
  apply mergeHiMemoryEventFree_markFuelExhausted
  exact mergeHiMemoryEventFree_pure _

private theorem mergeHiMemoryEventFree_succeed
    (cursor : MergeHiCursor κ ν) :
    MergeHiMemoryEventFree (mergeHiSucceedTraced? cursor) := by
  unfold mergeHiSucceedTraced?
  apply mergeHiMemoryEventFree_map
  split
  · exact mergeHiMemoryEventFree_pure _
  · exact mergeHiMemoryEventFree_tempToMainMemcpy _ _ _ _ _ _

private theorem mergeHiMemoryEventFree_copyA
    (cursor : MergeHiCursor κ ν) :
    MergeHiMemoryEventFree (mergeHiCopyATraced? cursor) := by
  unfold mergeHiCopyATraced?
  split
  · dsimp only
    apply mergeHiMemoryEventFree_bind
    · exact mergeHiMemoryEventFree_mainDataMemmove _ _ _ _
    · intro state
      apply mergeHiMemoryEventFree_map
      exact mergeHiMemoryEventFree_tempToMainCell _ _ _
  · exact mergeHiMemoryEventFree_failure

private theorem mergeHiMemoryEventFree_traceOption (value : Option α) :
    MergeHiMemoryEventFree (mergeHiTraceOption value) := by
  cases value
  · exact mergeHiMemoryEventFree_failure
  · exact mergeHiMemoryEventFree_pure _

private theorem mergeHiMemoryEventFree_gallopBFinish
    (afterB : MergeHiCursor κ ν) (aCount bCount : Nat)
    (movedB : MergeHiCursor κ ν)
    (next : MergeHiCursor κ ν → TraceResult (MergeHiResult κ ν))
    (hnext : ∀ cursor, MergeHiMemoryEventFree (next cursor)) :
    MergeHiMemoryEventFree
      (mergeHiGallopBFinishTraced? afterB aCount bCount movedB next) := by
  unfold mergeHiGallopBFinishTraced?
  split
  · exact hnext _
  · apply mergeHiMemoryEventFree_bind
    · exact mergeHiMemoryEventFree_copyDataDecr _ _ _
    · intro copiedA
      dsimp only
      split
      · exact hnext _
      · split
        · exact hnext _
        · exact hnext _

private theorem mergeHiMemoryEventFree_gallopBAfter
    (afterB : MergeHiCursor κ ν) (aCount : Nat) (gallopB : GallopResult)
    (next : MergeHiCursor κ ν → TraceResult (MergeHiResult κ ν))
    (hnext : ∀ cursor, MergeHiMemoryEventFree (next cursor)) :
    MergeHiMemoryEventFree
      (mergeHiGallopBAfterTraced? afterB aCount gallopB next) := by
  unfold mergeHiGallopBAfterTraced?
  split
  · exact mergeHiMemoryEventFree_fuelExhausted _
  · dsimp only
    apply mergeHiMemoryEventFree_bind
    · exact mergeHiMemoryEventFree_moveBBlock _ _
    · intro movedB
      exact mergeHiMemoryEventFree_gallopBFinish _ _ _ _ _ hnext

private theorem mergeHiMemoryEventFree_gallopB
    (afterB : MergeHiCursor κ ν) (aCount : Nat)
    (next : MergeHiCursor κ ν → TraceResult (MergeHiResult κ ν))
    (hnext : ∀ cursor, MergeHiMemoryEventFree (next cursor)) :
    MergeHiMemoryEventFree (mergeHiGallopBTraced? afterB aCount next) := by
  unfold mergeHiGallopBTraced?
  apply mergeHiMemoryEventFree_bind
  · exact mergeHiMemoryEventFree_keyRead _ _
  · intro left
    apply mergeHiMemoryEventFree_bind
    · exact mergeHiMemoryEventFree_traceOption _
    · intro _temp
      apply mergeHiMemoryEventFree_bind
      · exact mergeHiMemoryEventFree_gallopLeft _ _ _ _ _
      · intro gallopB
        exact mergeHiMemoryEventFree_gallopBAfter _ _ _ _ hnext

private theorem mergeHiMemoryEventFree_gallopRoundFinish
    (movedA : MergeHiCursor κ ν) (aCount : Nat)
    (next : MergeHiCursor κ ν → TraceResult (MergeHiResult κ ν))
    (hnext : ∀ cursor, MergeHiMemoryEventFree (next cursor)) :
    MergeHiMemoryEventFree
      (mergeHiGallopRoundFinishTraced? movedA aCount next) := by
  unfold mergeHiGallopRoundFinishTraced?
  split
  · exact hnext _
  · apply mergeHiMemoryEventFree_bind
    · exact mergeHiMemoryEventFree_copyTempDecr _ _ _
    · intro copiedB
      dsimp only
      split
      · exact hnext _
      · exact mergeHiMemoryEventFree_gallopB _ _ _ hnext

private theorem mergeHiMemoryEventFree_gallopRoundAfter
    (cursor : MergeHiCursor κ ν) (minGallop : PySSize)
    (state : MergeState κ ν) (gallopA : GallopResult)
    (next : MergeHiCursor κ ν → TraceResult (MergeHiResult κ ν))
    (hnext : ∀ cursor, MergeHiMemoryEventFree (next cursor)) :
    MergeHiMemoryEventFree
      (mergeHiGallopRoundAfterTraced? cursor minGallop state gallopA next) := by
  unfold mergeHiGallopRoundAfterTraced?
  split
  · exact mergeHiMemoryEventFree_fuelExhausted _
  · dsimp only
    apply mergeHiMemoryEventFree_bind
    · exact mergeHiMemoryEventFree_moveABlock _ _
    · intro movedA
      exact mergeHiMemoryEventFree_gallopRoundFinish _ _ _ hnext

private theorem mergeHiMemoryEventFree_gallopRound
    (cursor : MergeHiCursor κ ν)
    (next : MergeHiCursor κ ν → TraceResult (MergeHiResult κ ν))
    (hnext : ∀ cursor, MergeHiMemoryEventFree (next cursor)) :
    MergeHiMemoryEventFree (mergeHiGallopRoundTraced? cursor next) := by
  unfold mergeHiGallopRoundTraced?
  dsimp only
  apply mergeHiMemoryEventFree_bind
  · exact mergeHiMemoryEventFree_tempRead _ _
  · intro right
    apply mergeHiMemoryEventFree_bind
    · exact mergeHiMemoryEventFree_gallopRight _ _ _ _ _
    · intro gallopA
      exact mergeHiMemoryEventFree_gallopRoundAfter _ _ _ _ _ hnext

private theorem mergeHiMemoryEventFree_loop
    (fuel : Nat) (cursor : MergeHiCursor κ ν) :
    MergeHiMemoryEventFree (mergeHiLoopTraced? fuel cursor) := by
  induction fuel generalizing cursor with
  | zero =>
      simp only [mergeHiLoopTraced?]
      split
      · exact mergeHiMemoryEventFree_succeed _
      · split
        · exact mergeHiMemoryEventFree_copyA _
        · exact mergeHiMemoryEventFree_fuelExhausted _
  | succ fuel ih =>
      simp only [mergeHiLoopTraced?]
      split
      · exact mergeHiMemoryEventFree_succeed _
      · split
        · exact mergeHiMemoryEventFree_copyA _
        · split
          · apply mergeHiMemoryEventFree_bind
            · exact mergeHiMemoryEventFree_tempRead _ _
            · intro right
              apply mergeHiMemoryEventFree_bind
              · exact mergeHiMemoryEventFree_keyRead _ _
              · intro left
                split
                · apply mergeHiMemoryEventFree_bind
                  · exact mergeHiMemoryEventFree_copyDataDecr _ _ _
                  · intro copied
                    exact ih _
                · apply mergeHiMemoryEventFree_bind
                  · exact mergeHiMemoryEventFree_copyTempDecr _ _ _
                  · intro copied
                    exact ih _
          · exact mergeHiMemoryEventFree_gallopRound _ _ (fun _ => ih _)

private theorem mergeHiTraced_topLevelEvents_empty
    (state : MergeState κ ν) (ssa ssb : Int) (na nb : Nat) :
    MergeHiMemoryEventFree (mergeHiTraced? state ssa ssb na nb) := by
  unfold mergeHiTraced?
  split
  · dsimp only
    split
    · exact mergeHiMemoryEventFree_pure _
    · apply mergeHiMemoryEventFree_bind
      · exact mergeHiMemoryEventFree_mainToTempMemcpy _ _ _ _ _ _
      · intro copiedTemp
        apply mergeHiMemoryEventFree_bind
        · exact mergeHiMemoryEventFree_copyDataDecr _ _ _
        · intro copiedFirst
          exact mergeHiMemoryEventFree_loop _ _
    · apply mergeHiMemoryEventFree_bind
      · exact mergeHiMemoryEventFree_mainToTempMemcpy _ _ _ _ _ _
      · intro copiedTemp
        apply mergeHiMemoryEventFree_bind
        · exact mergeHiMemoryEventFree_copyDataDecr _ _ _
        · intro copiedFirst
          exact mergeHiMemoryEventFree_loop _ _
  · exact mergeHiMemoryEventFree_failure

/-- A raw directional `merge_hi` contributes no top-level merge-memory event;
the surrounding `merge_at` wrapper therefore owns exactly one call event. -/
theorem mergeHiTraced_memoryEvents_empty
    (state : MergeState κ ν) (ssa ssb : Int) (na nb : Nat) :
    (mergeHiTraced? state ssa ssb na nb).trace.memoryEvents = [] :=
  (mergeHiTraced_topLevelEvents_empty state ssa ssb na nb).1

/-- A raw directional `merge_hi` emits no merge-policy event.  Its enclosing
`merge_at` invocation owns the unique logical merge event, recorded before
the trimming gallops. -/
theorem mergeHiTraced_policyEvents_empty
    (state : MergeState κ ν) (ssa ssb : Int) (na nb : Nat) :
    (mergeHiTraced? state ssa ssb na nb).trace.policyEvents = [] :=
  (mergeHiTraced_topLevelEvents_empty state ssa ssb na nb).2

/-! ## Exact erasure of movement primitives -/

private theorem optionMap_eq_bindSome (value : Option α) (f : α → β) :
    value.map f = value.bind fun item => some (f item) := by
  cases value <;> rfl

@[simp]
theorem mergeTempRead_eq_mergeHiTempRead (storage : TempStorage κ ν)
    (index : Int) :
    mergeTempRead? storage index = mergeHiTempRead? storage index := by
  by_cases hindex : 0 ≤ index
  · cases hcell : storage.cells[index.toNat]? with
    | none => simp [mergeTempRead?, mergeHiTempRead?, hindex, hcell]
    | some cell =>
        cases cell <;> simp [mergeTempRead?, mergeHiTempRead?, hindex, hcell]
  · simp [mergeTempRead?, mergeHiTempRead?, hindex]

@[simp]
theorem mergeTempWrite_eq_mergeHiTempWrite (storage : TempStorage κ ν)
    (index : Int) (entry : SortSliceEntry κ ν) :
    mergeTempWrite? storage index entry =
      mergeHiTempWrite? storage index entry := by
  by_cases hindex : 0 ≤ index
  · by_cases hbounds : index.toNat < storage.cells.size <;>
      simp [mergeTempWrite?, mergeHiTempWrite?, hindex, hbounds,
        Array.setIfInBounds]
  · simp [mergeTempWrite?, mergeHiTempWrite?, hindex]

@[simp]
theorem mainToTempCell_eq_mergeHiCopyDataToTemp
    (state : MergeState κ ν) (dst src : Int) :
    mainToTempCell? state dst src = mergeHiCopyDataToTemp? state dst src := by
  simp [mainToTempCell?, mergeHiCopyDataToTemp?]

@[simp]
theorem tempToMainCell_eq_mergeHiCopyTempToData
    (state : MergeState κ ν) (dst src : Int) :
    tempToMainCell? state dst src = mergeHiCopyTempToData? state dst src := by
  simp [tempToMainCell?, mergeHiCopyTempToData?]

theorem mainToTempMemcpy_eq_mergeHiMemcpyDataToTemp
    (site : MergeHiMemcpyCallsite)
    (hDirection : site.backings =
      { destination := .temporary, source := .main })
    (count : Nat) (state : MergeState κ ν) (dst src : Int) :
    mainToTempMemcpy? count state dst src =
      mergeHiMemcpyDataToTemp? site hDirection count state dst src := by
  induction count generalizing state dst src with
  | zero => rfl
  | succ count ih =>
      simp [mainToTempMemcpy?, mergeHiMemcpyDataToTemp?, ih]

theorem tempToMainMemcpy_eq_mergeHiMemcpyTempToData
    (site : MergeHiMemcpyCallsite)
    (hDirection : site.backings =
      { destination := .main, source := .temporary })
    (count : Nat) (state : MergeState κ ν) (dst src : Int) :
    tempToMainMemcpy? count state dst src =
      mergeHiMemcpyTempToData? site hDirection count state dst src := by
  induction count generalizing state dst src with
  | zero => rfl
  | succ count ih =>
      simp [tempToMainMemcpy?, mergeHiMemcpyTempToData?, ih]

@[simp]
theorem erase_mergeHiCopyDataDecrTraced (state : MergeState κ ν)
    (dst src : Int) :
    (mergeHiCopyDataDecrTraced? state dst src).erase =
      mergeHiCopyDataDecr? state dst src := by
  exact erase_mainDataCopyDecrTraced state dst src

@[simp]
theorem erase_mergeHiCopyTempDecrTraced (state : MergeState κ ν)
    (dst src : Int) :
    (mergeHiCopyTempDecrTraced? state dst src).erase =
      mergeHiCopyTempDecr? state dst src := by
  rw [mergeHiCopyTempDecrTraced?, TraceResult.erase_map,
    erase_tempToMainCellTraced, tempToMainCell_eq_mergeHiCopyTempToData]
  cases hcopy : mergeHiCopyTempToData? state dst src <;>
    simp [mergeHiCopyTempDecr?, hcopy]

@[simp]
theorem erase_mergeHiMoveABlockTraced (cursor : MergeHiCursor κ ν)
    (count : Nat) :
    (mergeHiMoveABlockTraced? cursor count).erase =
      mergeHiMoveABlock? cursor count := by
  unfold mergeHiMoveABlockTraced? mergeHiMoveABlock?
  by_cases hcount : count = 0
  · simp [hcount]
  · simp only [hcount, ↓reduceIte, TraceResult.erase_map,
      erase_mainDataMemmoveTraced]
    exact optionMap_eq_bindSome _ _

@[simp]
theorem erase_mergeHiMoveBBlockTraced (cursor : MergeHiCursor κ ν)
    (count : Nat) :
    (mergeHiMoveBBlockTraced? cursor count).erase =
      mergeHiMoveBBlock? cursor count := by
  unfold mergeHiMoveBBlockTraced? mergeHiMoveBBlock?
  by_cases hcount : count = 0
  · simp [hcount]
  · simp only [hcount, ↓reduceIte, TraceResult.erase_map,
      erase_tempToMainMemcpyTraced]
    rw [tempToMainMemcpy_eq_mergeHiMemcpyTempToData .gallopTempToData rfl]
    exact optionMap_eq_bindSome _ _

@[simp]
private theorem erase_mergeHiGallopBFinishTraced
    (afterB : MergeHiCursor κ ν) (aCount bCount : Nat)
    (movedB : MergeHiCursor κ ν)
    (nextTraced : MergeHiCursor κ ν → TraceResult (MergeHiResult κ ν))
    (next : MergeHiCursor κ ν → Option (MergeHiResult κ ν))
    (hnext : ∀ cursor, (nextTraced cursor).erase = next cursor) :
    (mergeHiGallopBFinishTraced? afterB aCount bCount movedB
      nextTraced).erase =
      mergeHiGallopBFinish? afterB aCount bCount movedB next := by
  unfold mergeHiGallopBFinishTraced? mergeHiGallopBFinish?
  by_cases hterminal : movedB.nb = 0 ∨ movedB.nb = 1
  · simp [hterminal, hnext]
  · simp only [hterminal, ↓reduceIte, TraceResult.erase_bind,
      erase_mergeHiCopyDataDecrTraced]
    apply Option.bind_congr
    intro copiedA _hcopied
    split
    · exact hnext _
    · split <;> exact hnext _

@[simp]
private theorem erase_mergeHiGallopBAfterTraced
    (afterB : MergeHiCursor κ ν) (aCount : Nat) (gallopB : GallopResult)
    (nextTraced : MergeHiCursor κ ν → TraceResult (MergeHiResult κ ν))
    (next : MergeHiCursor κ ν → Option (MergeHiResult κ ν))
    (hnext : ∀ cursor, (nextTraced cursor).erase = next cursor) :
    (mergeHiGallopBAfterTraced? afterB aCount gallopB nextTraced).erase =
      mergeHiGallopBAfter? afterB aCount gallopB next := by
  unfold mergeHiGallopBAfterTraced? mergeHiGallopBAfter?
  cases hfuel : gallopB.fuelExhausted with
  | false =>
    change
      ((mergeHiMoveBBlockTraced? afterB
        (afterB.nb - gallopB.index)).bind fun movedB =>
          mergeHiGallopBFinishTraced? afterB aCount
            (afterB.nb - gallopB.index) movedB nextTraced).erase =
      (mergeHiMoveBBlock? afterB (afterB.nb - gallopB.index)).bind
        fun movedB => mergeHiGallopBFinish? afterB aCount
          (afterB.nb - gallopB.index) movedB next
    rw [TraceResult.erase_bind, erase_mergeHiMoveBBlockTraced]
    apply Option.bind_congr
    intro movedB _hmoved
    exact erase_mergeHiGallopBFinishTraced afterB aCount
      (afterB.nb - gallopB.index) movedB nextTraced next hnext
  | true =>
    change (mergeHiFuelExhaustedTraced afterB).erase =
      some (mergeHiFuelExhausted afterB)
    simp [mergeHiFuelExhaustedTraced]

private theorem mergeHiGallopB_eq_helpers
    (afterB : MergeHiCursor κ ν) (aCount : Nat)
    (next : MergeHiCursor κ ν → Option (MergeHiResult κ ν)) :
    mergeHiGallopB? afterB aCount next =
      (afterB.state.data.read? afterB.ssa).bind fun left =>
        (initializedTempPrefix? afterB.state.a afterB.nb).bind fun temp =>
          mergeHiBindOptionAcross
              (gallopLeft? afterB.state temp 0 left.key afterB.nb
                (afterB.nb - 1))
              (fun gallop => mergeHiGallopBAfter? afterB aCount gallop next) := by
  unfold mergeHiGallopB? mergeHiGallopBAfter?
  cases hleft : afterB.state.data.read? afterB.ssa with
  | none => simp [bind, Option.bind]
  | some left =>
    simp only [bind, Option.bind]
    cases htemp : initializedTempPrefix? afterB.state.a afterB.nb with
    | none => simp
    | some temp =>
      simp only [Bool.or_eq_true, BitVec.ofNat_eq_ofNat,
        Int.ofNat_eq_natCast]
      cases hgallop : gallopLeft? afterB.state temp 0 left.key afterB.nb
          (afterB.nb - 1) with
      | none => simp [mergeHiBindOptionAcross]
      | some gallop =>
        simp only [mergeHiBindOptionAcross]
        cases hfuel : gallop.fuelExhausted with
        | true =>
          have htrue : (true : Bool) = true := rfl
          rw [if_pos htrue, if_pos htrue]
        | false =>
          have hfalse : ¬ (false : Bool) = true := by decide
          rw [if_neg hfalse, if_neg hfalse]
          by_cases hcount : afterB.nb - gallop.index = 0
          · simp [Option.bind, hcount, mergeHiMoveBBlock?,
              mergeHiGallopBFinish?]
          · simp only [hcount, ↓reduceIte, mergeHiMoveBBlock?]
            cases hcopy : mergeHiMemcpyTempToData? .gallopTempToData rfl
                (afterB.nb - gallop.index) afterB.state
                (afterB.dest - Int.ofNat (afterB.nb - gallop.index) + 1)
                (afterB.ssb - Int.ofNat (afterB.nb - gallop.index) + 1) <;>
              simp [bind, Option.bind, mergeHiGallopBFinish?]

private theorem mergeHiGallopRound_eq_helpers
    (cursor : MergeHiCursor κ ν)
    (next : MergeHiCursor κ ν → Option (MergeHiResult κ ν)) :
    mergeHiGallopRound? cursor next =
      let minGallop := mergeHiDecreaseMinGallop cursor.minGallop
      let state := { cursor.state with min_gallop := minGallop }
      (mergeTempRead? state.a cursor.ssb).bind fun right =>
        mergeHiBindOptionAcross
          (gallopRight? state state.data cursor.basea right.key
            cursor.na (cursor.na - 1))
          (fun gallopA =>
            mergeHiGallopRoundAfter? cursor minGallop state gallopA next) := by
  simp only [mergeHiGallopRound?, mergeDataMemmove_eq,
    mergeTempRead_eq_mergeHiTempRead]
  cases hright : mergeHiTempRead?
      { cursor.state with
        min_gallop := mergeHiDecreaseMinGallop cursor.minGallop }.a
      cursor.ssb with
  | none => simp [bind, Option.bind]
  | some right =>
      simp only [bind, Option.bind]
      cases hgallop : gallopRight?
          { cursor.state with
            min_gallop := mergeHiDecreaseMinGallop cursor.minGallop }
          { cursor.state with
            min_gallop := mergeHiDecreaseMinGallop cursor.minGallop }.data
          cursor.basea right.key cursor.na (cursor.na - 1) with
      | none => simp [mergeHiBindOptionAcross]
      | some gallop =>
          simp only [mergeHiBindOptionAcross]
          cases hfuel : gallop.fuelExhausted with
          | true => simp [mergeHiGallopRoundAfter?, hfuel]
          | false =>
              simp only [mergeHiGallopRoundAfter?, hfuel, Bool.false_eq_true,
                ↓reduceIte]
              by_cases hcount : cursor.na - gallop.index = 0
              · simp only [mergeHiMoveABlock?, hcount, ↓reduceIte,
                  mergeHiGallopRoundFinish?]
                rfl
              · simp only [mergeHiMoveABlock?, hcount, ↓reduceIte]
                cases hmove : cursor.state.data.memmove?
                    (cursor.dest - Int.ofNat (cursor.na - gallop.index) + 1)
                    (cursor.ssa - Int.ofNat (cursor.na - gallop.index) + 1)
                    (cursor.na - gallop.index) with
                | none =>
                    unfold mainDataMemmove?
                    rw [hmove]
                    rfl
                | some data =>
                    unfold mainDataMemmove?
                    rw [hmove]
                    rfl

@[simp]
theorem erase_mergeHiFuelExhaustedTraced (cursor : MergeHiCursor κ ν) :
    (mergeHiFuelExhaustedTraced cursor).erase =
      some (mergeHiFuelExhausted cursor) := by
  simp [mergeHiFuelExhaustedTraced]

@[simp]
theorem erase_mergeHiSucceedTraced (cursor : MergeHiCursor κ ν) :
    (mergeHiSucceedTraced? cursor).erase = mergeHiSucceed? cursor := by
  unfold mergeHiSucceedTraced? mergeHiSucceed?
  by_cases hnb : cursor.nb = 0
  · simp [hnb]
  · simp only [hnb, ↓reduceIte, TraceResult.erase_map,
      erase_tempToMainMemcpyTraced]
    rw [tempToMainMemcpy_eq_mergeHiMemcpyTempToData .finalTempToData rfl]
    cases hcopy : mergeHiMemcpyTempToData? .finalTempToData rfl cursor.nb
        cursor.state (cursor.dest - Int.ofNat (cursor.nb - 1)) 0 <;>
      simp

@[simp]
theorem erase_mergeHiCopyATraced (cursor : MergeHiCursor κ ν) :
    (mergeHiCopyATraced? cursor).erase = mergeHiCopyA? cursor := by
  unfold mergeHiCopyATraced? mergeHiCopyA?
  simp only [mergeDataMemmove_eq]
  by_cases htail : cursor.nb = 1 ∧ 0 < cursor.na
  · rw [if_pos htail, if_pos htail, TraceResult.erase_bind,
      erase_mainDataMemmoveTraced]
    simp only [mainDataMemmove?, TraceResult.erase_map,
      erase_tempToMainCellTraced,
      tempToMainCell_eq_mergeHiCopyTempToData]
    cases hmove : cursor.state.data.memmove?
        (cursor.dest + (1 - Int.ofNat cursor.na))
        (cursor.ssa + (1 - Int.ofNat cursor.na)) cursor.na with
    | none => simp
    | some data =>
        exact optionMap_eq_bindSome _ _
  · rw [if_neg htail, if_neg htail]
    rfl

/-! ## Proof-only raw-domain erasure API -/

/-- A direct temporary-prefix gallop erases to the reviewed materialized-slice
gallop whenever prefix materialization succeeds.  No safety premise is needed:
outside the signed gallop domain both evaluators reject by the same guard. -/
private theorem erase_mergeHiTemporaryGallopLeft_of_eq_some
    (state : MergeState κ ν) (count hint : Nat)
    (slice : SortSlice κ ν) (key : κ)
    (hSlice : initializedTempPrefix? state.a count = some slice) :
    (gallopLeftTraced? state (.temporary state.a 0) key count hint).erase =
      gallopLeft? state slice 0 key count hint := by
  rw [erase_gallopLeftTraced]
  by_cases hInput : 0 < count ∧ hint < count ∧ count ≤ PY_SSIZE_T_MAX
  · exact gallopLeftFromSource_eq_slice_of_ssize state
      (.temporary state.a 0) slice 0 key count hint
      (initializedTempPrefix_agreesWithSlice_of_eq_some state.a count slice
        hSlice)
      hInput.1 hInput.2.1 hInput.2.2
  · unfold gallopLeftFromSource? gallopLeft?
    simp only [hInput, if_false]

/-- Erasure commutes with the second half of one `merge_hi` galloping round
whenever it commutes with the supplied continuation. -/
private theorem erase_mergeHiGallopBTraced
    (afterB : MergeHiCursor κ ν) (aCount : Nat)
    (nextTraced : MergeHiCursor κ ν → TraceResult (MergeHiResult κ ν))
    (next : MergeHiCursor κ ν → Option (MergeHiResult κ ν))
    (hNext : ∀ cursor, (nextTraced cursor).erase = next cursor) :
    (mergeHiGallopBTraced? afterB aCount nextTraced).erase =
      mergeHiGallopB? afterB aCount next := by
  rw [mergeHiGallopB_eq_helpers]
  unfold mergeHiGallopBTraced?
  rw [TraceResult.erase_bind, TraceResult.erase_sortSliceKeysRead]
  cases hLeft : afterB.state.data.read? afterB.ssa with
  | none => simp
  | some left =>
      simp only [Option.bind_some, TraceResult.erase_bind,
        erase_mergeHiTraceOption]
      cases hTemp : initializedTempPrefix? afterB.state.a afterB.nb with
      | none => simp
      | some temp =>
          simp only [Option.bind_some]
          rw [erase_mergeHiTemporaryGallopLeft_of_eq_some afterB.state
            afterB.nb (afterB.nb - 1) temp left.key hTemp]
          unfold mergeHiBindOptionAcross
          cases hGallop : gallopLeft? afterB.state temp 0 left.key afterB.nb
              (afterB.nb - 1) with
          | none => simp
          | some gallop =>
              simp only [Option.bind_some]
              exact erase_mergeHiGallopBAfterTraced afterB aCount gallop
                nextTraced next hNext

private theorem erase_mergeHiGallopRoundFinishTraced
    (movedA : MergeHiCursor κ ν) (aCount : Nat)
    (nextTraced : MergeHiCursor κ ν → TraceResult (MergeHiResult κ ν))
    (next : MergeHiCursor κ ν → Option (MergeHiResult κ ν))
    (hNext : ∀ cursor, (nextTraced cursor).erase = next cursor) :
    (mergeHiGallopRoundFinishTraced? movedA aCount nextTraced).erase =
      mergeHiGallopRoundFinish? movedA aCount next := by
  unfold mergeHiGallopRoundFinishTraced? mergeHiGallopRoundFinish?
  by_cases hFinished : movedA.na = 0
  · simp [hFinished, hNext]
  · rw [if_neg hFinished, if_neg hFinished, TraceResult.erase_bind,
      erase_mergeHiCopyTempDecrTraced]
    apply Option.bind_congr
    intro copiedB _hCopied
    let afterB : MergeHiCursor κ ν :=
      { movedA with
        state := copiedB.state
        dest := copiedB.dst
        ssb := copiedB.src
        nb := movedA.nb - 1 }
    change
      (if afterB.nb = 1 then nextTraced afterB
        else mergeHiGallopBTraced? afterB aCount nextTraced).erase =
      if afterB.nb = 1 then next afterB
        else mergeHiGallopB? afterB aCount next
    by_cases hOne : afterB.nb = 1
    · rw [if_pos hOne, if_pos hOne]
      exact hNext _
    · rw [if_neg hOne, if_neg hOne]
      exact erase_mergeHiGallopBTraced _ _ nextTraced next hNext

private theorem erase_mergeHiGallopRoundAfterTraced
    (cursor : MergeHiCursor κ ν) (minGallop : PySSize)
    (state : MergeState κ ν) (gallopA : GallopResult)
    (nextTraced : MergeHiCursor κ ν → TraceResult (MergeHiResult κ ν))
    (next : MergeHiCursor κ ν → Option (MergeHiResult κ ν))
    (hNext : ∀ cursor, (nextTraced cursor).erase = next cursor) :
    (mergeHiGallopRoundAfterTraced? cursor minGallop state gallopA
      nextTraced).erase =
      mergeHiGallopRoundAfter? cursor minGallop state gallopA next := by
  unfold mergeHiGallopRoundAfterTraced? mergeHiGallopRoundAfter?
  cases hFuel : gallopA.fuelExhausted with
  | true => simp [erase_mergeHiFuelExhaustedTraced]
  | false =>
      simp only [Bool.false_eq_true, if_false, TraceResult.erase_bind,
        erase_mergeHiMoveABlockTraced]
      apply Option.bind_congr
      intro movedA _hMoved
      exact erase_mergeHiGallopRoundFinishTraced movedA
        (cursor.na - gallopA.index) nextTraced next hNext

/-- Erasure commutes with one complete `merge_hi` galloping round whenever it
commutes with the supplied continuation.  This premise-free structural bridge
is the proof-only API consumed by the top-level raw-domain erasure chain. -/
theorem erase_mergeHiGallopRoundTraced
    (cursor : MergeHiCursor κ ν)
    (nextTraced : MergeHiCursor κ ν → TraceResult (MergeHiResult κ ν))
    (next : MergeHiCursor κ ν → Option (MergeHiResult κ ν))
    (hNext : ∀ cursor, (nextTraced cursor).erase = next cursor) :
    (mergeHiGallopRoundTraced? cursor nextTraced).erase =
      mergeHiGallopRound? cursor next := by
  rw [mergeHiGallopRound_eq_helpers]
  unfold mergeHiGallopRoundTraced?
  let minGallop := mergeHiDecreaseMinGallop cursor.minGallop
  let state : MergeState κ ν := { cursor.state with min_gallop := minGallop }
  change
    ((TraceResult.tempPayloadRead? state.a cursor.ssb).bind fun right =>
      (gallopRightTraced? state (.main state.data cursor.basea) right.key
        cursor.na (cursor.na - 1)).bind fun gallopA =>
          mergeHiGallopRoundAfterTraced? cursor minGallop state gallopA
            nextTraced).erase =
      (mergeTempRead? state.a cursor.ssb).bind fun right =>
        mergeHiBindOptionAcross
          (gallopRight? state state.data cursor.basea right.key cursor.na
            (cursor.na - 1)) fun gallopA =>
              mergeHiGallopRoundAfter? cursor minGallop state gallopA next
  rw [TraceResult.erase_bind, erase_mergeTempRead]
  cases hRight : mergeTempRead? state.a cursor.ssb with
  | none => simp
  | some right =>
      simp only [Option.bind_some, TraceResult.erase_bind]
      rw [erase_gallopRightTraced_main]
      unfold mergeHiBindOptionAcross
      cases hGallop : gallopRight? state state.data cursor.basea right.key
          cursor.na (cursor.na - 1) with
      | none => simp
      | some gallop =>
          simp only [Option.bind_some]
          exact erase_mergeHiGallopRoundAfterTraced cursor minGallop state
            gallop nextTraced next hNext

/-! ## Backward cursor and public safety vocabulary -/

/-- A physical temporary prefix is a valid direct gallop source exactly when
its cells are allocated and initialized. -/
theorem mergeHiTemporary_validRange (storage : TempStorage κ ν) (count : Nat)
    (hbound : count ≤ storage.cells.size)
    (hinitialized : TempRangeInitialized storage 0 count) :
    (GallopKeySource.temporary storage 0).ValidRange count := by
  refine ⟨by simp [GallopKeySource.base], ?_, ?_⟩
  · simpa [GallopKeySource.base, GallopKeySource.extent,
      Int.ofNat_eq_natCast] using Int.ofNat_le.mpr hbound
  · intro i hi
    rcases hinitialized i hi with ⟨entry, hentry⟩
    refine ⟨entry, ?_⟩
    rw [erase_mergeTempRead] at hentry
    simpa [GallopKeySource.read?, GallopKeySource.base,
      mergeTempRead?, Int.ofNat_eq_natCast] using hentry

/-- Any in-bounds half-open main range is a valid direct main gallop source. -/
theorem mergeHiMain_validRange (slice : SortSlice κ ν) (base : Int)
    (count : Nat) (hbase : 0 ≤ base)
    (hend : base + Int.ofNat count ≤ Int.ofNat slice.entries.size) :
    (GallopKeySource.main slice base).ValidRange count := by
  refine ⟨hbase, ?_, ?_⟩
  · simpa [GallopKeySource.base, GallopKeySource.extent] using hend
  · intro i hi
    have hiInt : Int.ofNat i < Int.ofNat count := Int.ofNat_lt.mpr hi
    have hindex : SortSlice.IndexInBounds slice
        (base + Int.ofNat i) := by
      constructor
      · exact add_nonneg hbase (Int.natCast_nonneg i)
      · exact lt_of_lt_of_le (by simpa [add_comm] using
          (add_lt_add_left hiInt base)) hend
    rcases SortSlice.read_eq_some_of_indexInBounds slice _ hindex with
      ⟨entry, hentry⟩
    exact ⟨entry, by
      simpa [GallopKeySource.read?, GallopKeySource.base] using hentry⟩

/-- State fields that the merge is forbidden to change.  Allocation may
change `a`, its backing, and `alloced`; the adaptive `min_gallop` is also an
intentional merge output. -/
structure MergeHiStableFrame (before after : MergeState κ ν) : Prop where
  listlen : after.listlen = before.listlen
  basekeys : after.basekeys = before.basekeys
  dataSize : after.data.entries.size = before.data.entries.size
  tempValuesMode : after.a.hasValues = before.a.hasValues
  pending : after.pending = before.pending
  comparator : after.key_compare = before.key_compare
  mrCurrent : after.mr_current = before.mr_current
  mrE : after.mr_e = before.mr_e
  mrMask : after.mr_mask = before.mr_mask

namespace MergeHiStableFrame

theorem refl (state : MergeState κ ν) : MergeHiStableFrame state state := by
  constructor <;> rfl

theorem trans {first second third : MergeState κ ν}
    (hfirst : MergeHiStableFrame first second)
    (hsecond : MergeHiStableFrame second third) :
    MergeHiStableFrame first third := by
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
    MergeHiStableFrame before after := by
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
    MergeHiStableFrame before (mergeGetmem before need).state := by
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

end MergeHiStableFrame

/-- Exact temporary-storage metadata preserved after `merge_getmem` has
selected the backing used by `merge_hi`.  The initial copy may replace payload
contents, so the frame records their extent rather than extensional equality. -/
structure MergeHiStorageFrame (before after : MergeState κ ν) : Prop where
  cellsSize : after.a.cells.size = before.a.cells.size
  backing : after.a.backing = before.a.backing
  hasValues : after.a.hasValues = before.a.hasValues
  alloced : after.alloced = before.alloced

namespace MergeHiStorageFrame

theorem refl (state : MergeState κ ν) : MergeHiStorageFrame state state := by
  constructor <;> rfl

theorem trans {first second third : MergeState κ ν}
    (hfirst : MergeHiStorageFrame first second)
    (hsecond : MergeHiStorageFrame second third) :
    MergeHiStorageFrame first third := by
  exact
    { cellsSize := hsecond.cellsSize.trans hfirst.cellsSize
      backing := hsecond.backing.trans hfirst.backing
      hasValues := hsecond.hasValues.trans hfirst.hasValues
      alloced := hsecond.alloced.trans hfirst.alloced }

theorem of_movement {before after : MergeState κ ν}
    (hframe : MergeMovementFrame before after) :
    MergeHiStorageFrame before after :=
  { cellsSize := hframe.tempSize
    backing := hframe.tempBacking
    hasValues := hframe.tempValuesMode
    alloced := hframe.alloced }

/-- The framed metadata determines exactly the physical pointer-slot count. -/
theorem physicalSlots_eq {before after : MergeState κ ν}
    (hframe : MergeHiStorageFrame before after) :
    after.a.physicalSlots = before.a.physicalSlots := by
  simp only [TempStorage.physicalSlots, TempStorage.multiplier]
  rw [hframe.cellsSize, hframe.hasValues]

end MergeHiStorageFrame

/-- Inductive invariant for every live right-to-left merge cursor.  The three
equalities are the subtraction-sensitive core: they retain the legal `-1`
sentinels rather than coercing backward cursors through `Nat`. -/
structure MergeHiCursorInvariant (origin : MergeState κ ν) (request : Nat)
    (cursor : MergeHiCursor κ ν) : Prop where
  baseNonnegative : 0 ≤ cursor.basea
  ssaEquation : cursor.ssa + 1 = cursor.basea + Int.ofNat cursor.na
  ssbEquation : cursor.ssb + 1 = Int.ofNat cursor.nb
  destEquation :
    cursor.dest + 1 = cursor.basea + Int.ofNat (cursor.na + cursor.nb)
  mainRange :
    cursor.basea + Int.ofNat (cursor.na + cursor.nb) ≤
      Int.ofNat cursor.state.data.entries.size
  leftWordBound : cursor.na ≤ PY_LIST_MAX
  rightWordBound : cursor.nb ≤ PY_LIST_MAX
  tempCapacity : cursor.nb ≤ cursor.state.a.cells.size
  tempValuesMode : TempRangeValuesMode cursor.state.a 0 cursor.nb
  tempInvariant : TempStorageInv cursor.state.a cursor.state.alloced
  tempLive : cursor.state.a.Live
  requestFits : request ≤ cursor.state.alloced.toNat
  valuesMode :
    SortSlice.ValuesModeInvariant cursor.state.a.hasValues cursor.state.data
  stableFrame : MergeHiStableFrame origin cursor.state
  storageFrame : MergeHiStorageFrame origin cursor.state

/-- The outer fuel stays strictly ahead of the number of unmerged entries.
That one-step slack is created by the forced initial left copy. -/
def MergeHiFuelInvariant (fuel : Nat) (cursor : MergeHiCursor κ ν) : Prop :=
  cursor.na + cursor.nb < fuel

namespace MergeHiCursorInvariant

theorem ssaInBounds {origin : MergeState κ ν} {request : Nat}
    {cursor : MergeHiCursor κ ν}
    (h : MergeHiCursorInvariant origin request cursor) (hna : 0 < cursor.na) :
    SortSlice.IndexInBounds cursor.state.data cursor.ssa := by
  have heq := h.ssaEquation
  have hrange := h.mainRange
  have hbase := h.baseNonnegative
  have hnbNonnegative : (0 : Int) ≤ (cursor.nb : Int) :=
    Int.natCast_nonneg _
  change 0 ≤ cursor.ssa ∧
    cursor.ssa < Int.ofNat cursor.state.data.entries.size
  simp only [Int.ofNat_eq_natCast, Nat.cast_add] at heq hrange ⊢
  constructor <;> omega

theorem ssbInBounds {origin : MergeState κ ν} {request : Nat}
    {cursor : MergeHiCursor κ ν}
    (h : MergeHiCursorInvariant origin request cursor) (hnb : 0 < cursor.nb) :
    TempIndexInBounds cursor.state.a cursor.ssb := by
  have heq := h.ssbEquation
  have hcapacity : (cursor.nb : Int) ≤
      (cursor.state.a.cells.size : Int) := by
    exact_mod_cast h.tempCapacity
  change 0 ≤ cursor.ssb ∧
    cursor.ssb < Int.ofNat cursor.state.a.cells.size
  simp only [Int.ofNat_eq_natCast] at heq ⊢
  constructor <;> omega

theorem destInBounds {origin : MergeState κ ν} {request : Nat}
    {cursor : MergeHiCursor κ ν}
    (h : MergeHiCursorInvariant origin request cursor)
    (hactive : 0 < cursor.na + cursor.nb) :
    SortSlice.IndexInBounds cursor.state.data cursor.dest := by
  have heq := h.destEquation
  have hrange := h.mainRange
  have hbase := h.baseNonnegative
  have hsumPositive : (0 : Int) < (cursor.na + cursor.nb : Nat) := by
    exact_mod_cast hactive
  change 0 ≤ cursor.dest ∧
    cursor.dest < Int.ofNat cursor.state.data.entries.size
  simp only [Int.ofNat_eq_natCast, Nat.cast_add] at heq hrange ⊢
  constructor <;> omega

theorem tempReadable {origin : MergeState κ ν} {request : Nat}
    {cursor : MergeHiCursor κ ν}
    (h : MergeHiCursorInvariant origin request cursor)
    (hnb : 0 < cursor.nb) :
    ∃ entry, mergeTempRead? cursor.state.a cursor.ssb = some entry := by
  have heq := h.ssbEquation
  have hindex : cursor.ssb = Int.ofNat (cursor.nb - 1) := by
    simp only [Int.ofNat_eq_natCast] at heq ⊢
    omega
  rcases h.tempValuesMode (cursor.nb - 1) (by omega) with
    ⟨entry, hread, _⟩
  rw [erase_mergeTempRead] at hread
  rw [hindex]
  exact ⟨entry, by simpa using hread⟩

theorem temporaryValidRange {origin : MergeState κ ν} {request : Nat}
    {cursor : MergeHiCursor κ ν}
    (h : MergeHiCursorInvariant origin request cursor) :
    (GallopKeySource.temporary cursor.state.a 0).ValidRange cursor.nb :=
  mergeHiTemporary_validRange cursor.state.a cursor.nb h.tempCapacity
    h.tempValuesMode.initialized

theorem mainValidRange {origin : MergeState κ ν} {request : Nat}
    {cursor : MergeHiCursor κ ν}
    (h : MergeHiCursorInvariant origin request cursor) :
    (GallopKeySource.main cursor.state.data cursor.basea).ValidRange cursor.na := by
  apply mergeHiMain_validRange cursor.state.data cursor.basea cursor.na
      h.baseNonnegative
  have hrange := h.mainRange
  simp only [Int.ofNat_eq_natCast, Nat.cast_add] at hrange ⊢
  have hnbNonnegative : (0 : Int) ≤ (cursor.nb : Int) :=
    Int.natCast_nonneg _
  omega

theorem replaceState {origin : MergeState κ ν} {request : Nat}
    {cursor : MergeHiCursor κ ν}
    (h : MergeHiCursorInvariant origin request cursor)
    (after : MergeState κ ν) (hframe : MergeMovementFrame cursor.state after)
    (htemp : after.a = cursor.state.a)
    (hmode : SortSlice.ValuesModeInvariant after.a.hasValues after.data) :
    MergeHiCursorInvariant origin request { cursor with state := after } := by
  exact
    { baseNonnegative := h.baseNonnegative
      ssaEquation := h.ssaEquation
      ssbEquation := h.ssbEquation
      destEquation := h.destEquation
      mainRange := by simpa only [hframe.dataSize] using h.mainRange
      leftWordBound := h.leftWordBound
      rightWordBound := h.rightWordBound
      tempCapacity := by simpa only [htemp] using h.tempCapacity
      tempValuesMode := by simpa only [htemp] using h.tempValuesMode
      tempInvariant := hframe.tempStorageInv h.tempInvariant
      tempLive := hframe.live h.tempLive
      requestFits := by simpa only [hframe.alloced] using h.requestFits
      valuesMode := hmode
      stableFrame := h.stableFrame.trans (.of_movement hframe)
      storageFrame := h.storageFrame.trans (.of_movement hframe) }

theorem setMinGallop {origin : MergeState κ ν} {request : Nat}
    {cursor : MergeHiCursor κ ν}
    (h : MergeHiCursorInvariant origin request cursor)
    (minGallop : PySSize) :
    MergeHiCursorInvariant origin request
      { cursor with
        state := { cursor.state with min_gallop := minGallop }
        minGallop := minGallop } := by
  exact
    { baseNonnegative := h.baseNonnegative
      ssaEquation := h.ssaEquation
      ssbEquation := h.ssbEquation
      destEquation := h.destEquation
      mainRange := h.mainRange
      leftWordBound := h.leftWordBound
      rightWordBound := h.rightWordBound
      tempCapacity := h.tempCapacity
      tempValuesMode := h.tempValuesMode
      tempInvariant := h.tempInvariant
      tempLive := h.tempLive
      requestFits := h.requestFits
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

/-- The phase counters and local threshold guide control flow only.  They do
not describe physical state, and the transcription may intentionally update
the local threshold before writing `state.min_gallop`. -/
theorem setControl {origin : MergeState κ ν} {request : Nat}
    {cursor : MergeHiCursor κ ν}
    (h : MergeHiCursorInvariant origin request cursor)
    (minGallop : PySSize) (phase : MergeHiPhase) :
    MergeHiCursorInvariant origin request
      { cursor with minGallop := minGallop, phase := phase } := by
  exact
    { baseNonnegative := h.baseNonnegative
      ssaEquation := h.ssaEquation
      ssbEquation := h.ssbEquation
      destEquation := h.destEquation
      mainRange := h.mainRange
      leftWordBound := h.leftWordBound
      rightWordBound := h.rightWordBound
      tempCapacity := h.tempCapacity
      tempValuesMode := h.tempValuesMode
      tempInvariant := h.tempInvariant
      tempLive := h.tempLive
      requestFits := h.requestFits
      valuesMode := h.valuesMode
      stableFrame := h.stableFrame
      storageFrame := h.storageFrame }

theorem copyA {origin : MergeState κ ν} {request : Nat}
    {cursor : MergeHiCursor κ ν}
    (h : MergeHiCursorInvariant origin request cursor)
    (after : MergeState κ ν) (hframe : MergeMovementFrame cursor.state after)
    (htemp : after.a = cursor.state.a)
    (hmode : SortSlice.ValuesModeInvariant after.a.hasValues after.data)
    (hna : 0 < cursor.na) :
    MergeHiCursorInvariant origin request
      { cursor with
        state := after
        dest := cursor.dest - 1
        ssa := cursor.ssa - 1
        na := cursor.na - 1 } := by
  have hs := h.replaceState after hframe htemp hmode
  exact
    { baseNonnegative := h.baseNonnegative
      ssaEquation := by
        have heq := h.ssaEquation
        simp only [Int.ofNat_eq_natCast, Nat.cast_sub hna] at heq ⊢
        omega
      ssbEquation := h.ssbEquation
      destEquation := by
        have heq := h.destEquation
        simp only [Int.ofNat_eq_natCast, Nat.cast_add, Nat.cast_sub hna]
          at heq ⊢
        omega
      mainRange := by
        have hrange := hs.mainRange
        simp only [Int.ofNat_eq_natCast, Nat.cast_add, Nat.cast_sub hna]
          at hrange ⊢
        omega
      leftWordBound := (Nat.sub_le cursor.na 1).trans h.leftWordBound
      rightWordBound := h.rightWordBound
      tempCapacity := hs.tempCapacity
      tempValuesMode := hs.tempValuesMode
      tempInvariant := hs.tempInvariant
      tempLive := hs.tempLive
      requestFits := hs.requestFits
      valuesMode := hs.valuesMode
      stableFrame := hs.stableFrame
      storageFrame := hs.storageFrame }

theorem copyB {origin : MergeState κ ν} {request : Nat}
    {cursor : MergeHiCursor κ ν}
    (h : MergeHiCursorInvariant origin request cursor)
    (after : MergeState κ ν) (hframe : MergeMovementFrame cursor.state after)
    (htemp : after.a = cursor.state.a)
    (hmode : SortSlice.ValuesModeInvariant after.a.hasValues after.data)
    (hnb : 0 < cursor.nb) :
    MergeHiCursorInvariant origin request
      { cursor with
        state := after
        dest := cursor.dest - 1
        ssb := cursor.ssb - 1
        nb := cursor.nb - 1 } := by
  have hs := h.replaceState after hframe htemp hmode
  exact
    { baseNonnegative := h.baseNonnegative
      ssaEquation := h.ssaEquation
      ssbEquation := by
        have heq := h.ssbEquation
        simp only [Int.ofNat_eq_natCast, Nat.cast_sub hnb] at heq ⊢
        omega
      destEquation := by
        have heq := h.destEquation
        simp only [Int.ofNat_eq_natCast, Nat.cast_add, Nat.cast_sub hnb]
          at heq ⊢
        omega
      mainRange := by
        have hrange := hs.mainRange
        simp only [Int.ofNat_eq_natCast, Nat.cast_add, Nat.cast_sub hnb]
          at hrange ⊢
        omega
      leftWordBound := h.leftWordBound
      rightWordBound := (Nat.sub_le cursor.nb 1).trans h.rightWordBound
      tempCapacity := (Nat.sub_le cursor.nb 1).trans hs.tempCapacity
      tempValuesMode := by
        change TempRangeValuesMode after.a 0 (cursor.nb - 1)
        intro offset hoffset
        exact hs.tempValuesMode offset
          (lt_of_lt_of_le hoffset (Nat.sub_le cursor.nb 1))
      tempInvariant := hs.tempInvariant
      tempLive := hs.tempLive
      requestFits := hs.requestFits
      valuesMode := hs.valuesMode
      stableFrame := hs.stableFrame
      storageFrame := hs.storageFrame }

theorem copyABlock {origin : MergeState κ ν} {request : Nat}
    {cursor : MergeHiCursor κ ν}
    (h : MergeHiCursorInvariant origin request cursor)
    (count : Nat) (hcount : count ≤ cursor.na)
    (after : MergeState κ ν) (hframe : MergeMovementFrame cursor.state after)
    (htemp : after.a = cursor.state.a)
    (hmode : SortSlice.ValuesModeInvariant after.a.hasValues after.data) :
    MergeHiCursorInvariant origin request
      { cursor with
        state := after
        dest := cursor.dest - Int.ofNat count
        ssa := cursor.ssa - Int.ofNat count
        na := cursor.na - count } := by
  have hs := h.replaceState after hframe htemp hmode
  exact
    { baseNonnegative := h.baseNonnegative
      ssaEquation := by
        have heq := h.ssaEquation
        simp only [Int.ofNat_eq_natCast, Nat.cast_sub hcount] at heq ⊢
        omega
      ssbEquation := h.ssbEquation
      destEquation := by
        have heq := h.destEquation
        simp only [Int.ofNat_eq_natCast, Nat.cast_add, Nat.cast_sub hcount]
          at heq ⊢
        omega
      mainRange := by
        have hrange := hs.mainRange
        simp only [Int.ofNat_eq_natCast, Nat.cast_add, Nat.cast_sub hcount]
          at hrange ⊢
        omega
      leftWordBound := (Nat.sub_le cursor.na count).trans h.leftWordBound
      rightWordBound := h.rightWordBound
      tempCapacity := hs.tempCapacity
      tempValuesMode := hs.tempValuesMode
      tempInvariant := hs.tempInvariant
      tempLive := hs.tempLive
      requestFits := hs.requestFits
      valuesMode := hs.valuesMode
      stableFrame := hs.stableFrame
      storageFrame := hs.storageFrame }

theorem copyBBlock {origin : MergeState κ ν} {request : Nat}
    {cursor : MergeHiCursor κ ν}
    (h : MergeHiCursorInvariant origin request cursor)
    (count : Nat) (hcount : count ≤ cursor.nb)
    (after : MergeState κ ν) (hframe : MergeMovementFrame cursor.state after)
    (htemp : after.a = cursor.state.a)
    (hmode : SortSlice.ValuesModeInvariant after.a.hasValues after.data) :
    MergeHiCursorInvariant origin request
      { cursor with
        state := after
        dest := cursor.dest - Int.ofNat count
        ssb := cursor.ssb - Int.ofNat count
        nb := cursor.nb - count } := by
  have hs := h.replaceState after hframe htemp hmode
  exact
    { baseNonnegative := h.baseNonnegative
      ssaEquation := h.ssaEquation
      ssbEquation := by
        have heq := h.ssbEquation
        simp only [Int.ofNat_eq_natCast, Nat.cast_sub hcount] at heq ⊢
        omega
      destEquation := by
        have heq := h.destEquation
        simp only [Int.ofNat_eq_natCast, Nat.cast_add, Nat.cast_sub hcount]
          at heq ⊢
        omega
      mainRange := by
        have hrange := hs.mainRange
        simp only [Int.ofNat_eq_natCast, Nat.cast_add, Nat.cast_sub hcount]
          at hrange ⊢
        omega
      leftWordBound := h.leftWordBound
      rightWordBound := (Nat.sub_le cursor.nb count).trans h.rightWordBound
      tempCapacity := (Nat.sub_le cursor.nb count).trans hs.tempCapacity
      tempValuesMode := by
        change TempRangeValuesMode after.a 0 (cursor.nb - count)
        intro offset hoffset
        exact hs.tempValuesMode offset
          (lt_of_lt_of_le hoffset (Nat.sub_le cursor.nb count))
      tempInvariant := hs.tempInvariant
      tempLive := hs.tempLive
      requestFits := hs.requestFits
      valuesMode := hs.valuesMode
      stableFrame := hs.stableFrame
      storageFrame := hs.storageFrame }

end MergeHiCursorInvariant

/-! ## Concrete adversarial-comparator hedge fixtures -/

/-- The concrete non-irreflexive-comparator cursor used by
`mergeHi_inconsistentComparator_nbZero_succeed_regression` satisfies the full
assembly invariant, including its subtraction-sensitive cursor geometry. -/
theorem mergeHiNbZeroHedgeRegressionCursor_invariant :
    MergeHiCursorInvariant mergeHiNbZeroHedgeRegressionState 2
      mergeHiNbZeroHedgeRegressionCursor := by
  refine
    { baseNonnegative := by decide
      ssaEquation := by decide
      ssbEquation := by decide
      destEquation := by decide
      mainRange := by decide
      leftWordBound := by decide
      rightWordBound := by decide
      tempCapacity := by decide
      tempValuesMode := ?_
      tempInvariant := by
        have hcapacity : 4 ≤ MERGESTATE_TEMP_SIZE := by decide
        simpa [mergeHiNbZeroHedgeRegressionCursor,
          mergeHiNbZeroHedgeRegressionState, TempStorageInv,
          TempStorage.multiplier] using hcapacity
      tempLive := by
        simp [mergeHiNbZeroHedgeRegressionCursor,
          mergeHiNbZeroHedgeRegressionState, TempStorage.Live]
      requestFits := by decide
      valuesMode := ?_
      stableFrame := ?_
      storageFrame := ?_ }
  · intro index hindex
    have hindex' : index < 2 := by
      simpa [mergeHiNbZeroHedgeRegressionCursor,
        mergeHiNbZeroHedgeRegressionState] using hindex
    interval_cases index <;>
      simp [mergeHiNbZeroHedgeRegressionCursor,
        mergeHiNbZeroHedgeRegressionState,
        SortSlice.EntryMatchesValuesMode]
  · intro index hindex
    have hindex' : index < 3 := by
      simpa [mergeHiNbZeroHedgeRegressionCursor,
        mergeHiNbZeroHedgeRegressionState] using hindex
    interval_cases index <;>
      simp [mergeHiNbZeroHedgeRegressionCursor,
        mergeHiNbZeroHedgeRegressionState,
        SortSlice.EntryMatchesValuesMode]
  · simpa [mergeHiNbZeroHedgeRegressionCursor] using
      MergeHiStableFrame.refl mergeHiNbZeroHedgeRegressionState
  · simpa [mergeHiNbZeroHedgeRegressionCursor] using
      MergeHiStorageFrame.refl mergeHiNbZeroHedgeRegressionState

/-- Changing only the comparator to strict `<` preserves the full assembly
invariant of the `merge_hi` hedge-regression geometry. -/
theorem mergeHiNbZeroHedgeStrictControlCursor_invariant :
    MergeHiCursorInvariant mergeHiNbZeroHedgeStrictControlState 2
      mergeHiNbZeroHedgeStrictControlCursor := by
  refine
    { baseNonnegative := by decide
      ssaEquation := by decide
      ssbEquation := by decide
      destEquation := by decide
      mainRange := by decide
      leftWordBound := by decide
      rightWordBound := by decide
      tempCapacity := by decide
      tempValuesMode := ?_
      tempInvariant := by
        have hcapacity : 4 ≤ MERGESTATE_TEMP_SIZE := by decide
        simpa [mergeHiNbZeroHedgeStrictControlCursor,
          mergeHiNbZeroHedgeStrictControlState,
          mergeHiNbZeroHedgeRegressionCursor,
          mergeHiNbZeroHedgeRegressionState, TempStorageInv,
          TempStorage.multiplier] using hcapacity
      tempLive := by
        simp [mergeHiNbZeroHedgeStrictControlCursor,
          mergeHiNbZeroHedgeStrictControlState,
          mergeHiNbZeroHedgeRegressionCursor,
          mergeHiNbZeroHedgeRegressionState, TempStorage.Live]
      requestFits := by decide
      valuesMode := ?_
      stableFrame := ?_
      storageFrame := ?_ }
  · intro index hindex
    have hindex' : index < 2 := by
      simpa [mergeHiNbZeroHedgeStrictControlCursor,
        mergeHiNbZeroHedgeStrictControlState,
        mergeHiNbZeroHedgeRegressionCursor,
        mergeHiNbZeroHedgeRegressionState] using hindex
    interval_cases index <;>
      simp [mergeHiNbZeroHedgeStrictControlCursor,
        mergeHiNbZeroHedgeStrictControlState,
        mergeHiNbZeroHedgeRegressionCursor,
        mergeHiNbZeroHedgeRegressionState,
        SortSlice.EntryMatchesValuesMode]
  · intro index hindex
    have hindex' : index < 3 := by
      simpa [mergeHiNbZeroHedgeStrictControlCursor,
        mergeHiNbZeroHedgeStrictControlState,
        mergeHiNbZeroHedgeRegressionCursor,
        mergeHiNbZeroHedgeRegressionState] using hindex
    interval_cases index <;>
      simp [mergeHiNbZeroHedgeStrictControlCursor,
        mergeHiNbZeroHedgeStrictControlState,
        mergeHiNbZeroHedgeRegressionCursor,
        mergeHiNbZeroHedgeRegressionState,
        SortSlice.EntryMatchesValuesMode]
  · simpa [mergeHiNbZeroHedgeStrictControlCursor] using
      MergeHiStableFrame.refl mergeHiNbZeroHedgeStrictControlState
  · simpa [mergeHiNbZeroHedgeStrictControlCursor] using
      MergeHiStorageFrame.refl mergeHiNbZeroHedgeStrictControlState

/-- Internal inductive postcondition shared by terminal paths and the phase
driver.  The reference computation is the corresponding reviewed untraced
fragment, so erasure stays lockstep throughout the induction. -/
private structure MergeHiCorePost
    (origin : MergeState κ ν) (request : Nat)
    (execution : TraceResult (MergeHiResult κ ν))
    (reference : Option (MergeHiResult κ ν))
    (result : MergeHiResult κ ν) : Prop where
  resultEq : execution.result = some result
  returnCode : result.returnCode = 0
  resultFuel : result.fuelExhausted = false
  traceSafe : MovementTraceSafe execution
  exactErasure : execution.erase = reference
  tempInvariant : TempStorageInv result.state.a result.state.alloced
  tempLive : result.state.a.Live
  requestFits : request ≤ result.state.alloced.toNat
  valuesMode :
    SortSlice.ValuesModeInvariant result.state.a.hasValues result.state.data
  stableFrame : MergeHiStableFrame origin result.state
  storageFrame : MergeHiStorageFrame origin result.state

private def MergeHiContinuationSafe
    (origin : MergeState κ ν) (request fuel : Nat)
    (nextTraced : MergeHiCursor κ ν → TraceResult (MergeHiResult κ ν))
    (next : MergeHiCursor κ ν → Option (MergeHiResult κ ν)) : Prop :=
  ∀ cursor,
    MergeHiCursorInvariant origin request cursor →
    MergeHiFuelInvariant fuel cursor →
    ∃ result, MergeHiCorePost origin request
      (nextTraced cursor) (next cursor) result

private theorem MergeHiCorePost.bind
    (origin : MergeState κ ν) (request : Nat)
    (current : TraceResult α)
    (next : α → TraceResult (MergeHiResult κ ν)) (value : α)
    (reference : Option (MergeHiResult κ ν)) (result : MergeHiResult κ ν)
    (hcurrent : current.result = some value)
    (hcurrentSafe : MovementTraceSafe current)
    (hnext : MergeHiCorePost origin request (next value) reference result)
    (herase : (current.bind next).erase = reference) :
    MergeHiCorePost origin request (current.bind next) reference result := by
  exact
    { resultEq := by
        unfold TraceResult.bind
        rw [hcurrent]
        exact hnext.resultEq
      returnCode := hnext.returnCode
      resultFuel := hnext.resultFuel
      traceSafe := MovementTraceSafe.bind current next value hcurrent
        hcurrentSafe hnext.traceSafe
      exactErasure := herase
      tempInvariant := hnext.tempInvariant
      tempLive := hnext.tempLive
      requestFits := hnext.requestFits
      valuesMode := hnext.valuesMode
      stableFrame := hnext.stableFrame
      storageFrame := hnext.storageFrame }

private theorem MergeHiCorePost.prepend
    (origin : MergeState κ ν) (request : Nat)
    (current : TraceResult α)
    (next : α → TraceResult (MergeHiResult κ ν))
    (reference : α → Option (MergeHiResult κ ν))
    (value : α) (result : MergeHiResult κ ν)
    (hcurrent : current.result = some value)
    (hcurrentSafe : MovementTraceSafe current)
    (hnext : MergeHiCorePost origin request (next value)
      (reference value) result) :
    MergeHiCorePost origin request (current.bind next)
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
        simpa using hnext.exactErasure
      tempInvariant := hnext.tempInvariant
      tempLive := hnext.tempLive
      requestFits := hnext.requestFits
      valuesMode := hnext.valuesMode
      stableFrame := hnext.stableFrame
      storageFrame := hnext.storageFrame }

private theorem MergeHiCorePost.reference_eq
    {origin : MergeState κ ν} {request : Nat}
    {execution : TraceResult (MergeHiResult κ ν)}
    {first second : Option (MergeHiResult κ ν)}
    {result : MergeHiResult κ ν}
    (h : MergeHiCorePost origin request execution first result)
    (heq : first = second) :
    MergeHiCorePost origin request execution second result := by
  subst second
  exact h

private theorem movementTraceSafe_of_gallopTraceSafe
    (execution : TraceResult α) (h : GallopTraceSafe execution) :
    MovementTraceSafe execution := by
  exact ⟨h.1, h.2.1, h.2.2.1, h.2.2.2⟩

private theorem mergeHiTempReadTraced_safe (storage : TempStorage κ ν)
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

private theorem mergeHiMainKeyReadTraced_safe (slice : SortSlice κ ν)
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

private theorem mainDataCopyDecr_temp_eq_of_result
    (state : MergeState κ ν) (dst src : Int)
    (result : MergeHiDataCursorResult κ ν)
    (hresult : (mergeHiCopyDataDecrTraced? state dst src).result =
      some result) :
    result.state.a = state.a := by
  unfold mergeHiCopyDataDecrTraced? mainDataCopyDecrTraced? at hresult
  cases hcopy :
      (SortSlice.copyDecrTraced? state.a.hasValues state.data dst src).result with
  | none => simp [TraceResult.map, hcopy] at hresult
  | some copied =>
      simp [TraceResult.map, hcopy] at hresult
      subst result
      rfl

theorem mergeHiCopyDataDecrTraced_safe
    (origin : MergeState κ ν) (request : Nat)
    (cursor : MergeHiCursor κ ν)
    (hinvariant : MergeHiCursorInvariant origin request cursor)
    (hna : 0 < cursor.na) :
    ∃ copied,
      (mergeHiCopyDataDecrTraced? cursor.state cursor.dest
        cursor.ssa).result = some copied ∧
      MovementTraceSafe
        (mergeHiCopyDataDecrTraced? cursor.state cursor.dest cursor.ssa) ∧
      MergeHiCursorInvariant origin request
        { cursor with
          state := copied.state
          dest := copied.dst
          ssa := copied.src
          na := cursor.na - 1 } ∧
      copied.dst = cursor.dest - 1 ∧ copied.src = cursor.ssa - 1 := by
  have hdest := hinvariant.destInBounds (by omega)
  have hsrc := hinvariant.ssaInBounds hna
  rcases mainDataCopyDecrTraced_safe cursor.state cursor.dest cursor.ssa
      hinvariant.tempInvariant hinvariant.tempLive hinvariant.valuesMode
      hdest hsrc with ⟨copied, hpost⟩
  have htemp := mainDataCopyDecr_temp_eq_of_result cursor.state cursor.dest
    cursor.ssa copied hpost.success
  have hnextInv : MergeHiCursorInvariant origin request
      { cursor with
        state := copied.state
        dest := copied.dst
        ssa := copied.src
        na := cursor.na - 1 } := by
    simpa only [hpost.dstDecrement, hpost.srcDecrement] using
      hinvariant.copyA copied.state hpost.frame htemp hpost.valuesMode hna
  exact ⟨copied, hpost.success, hpost.traceSafe, hnextInv,
    hpost.dstDecrement, hpost.srcDecrement⟩

theorem mergeHiCopyTempDecrTraced_safe
    (origin : MergeState κ ν) (request : Nat)
    (cursor : MergeHiCursor κ ν)
    (hinvariant : MergeHiCursorInvariant origin request cursor)
    (hnb : 0 < cursor.nb) :
    ∃ copied,
      (mergeHiCopyTempDecrTraced? cursor.state cursor.dest
        cursor.ssb).result = some copied ∧
      MovementTraceSafe
        (mergeHiCopyTempDecrTraced? cursor.state cursor.dest cursor.ssb) ∧
      MergeHiCursorInvariant origin request
        { cursor with
          state := copied.state
          dest := copied.dst
          ssb := copied.src
          nb := cursor.nb - 1 } ∧
      copied.dst = cursor.dest - 1 ∧ copied.src = cursor.ssb - 1 := by
  have hdest := hinvariant.destInBounds (by omega)
  have htemp := hinvariant.ssbInBounds hnb
  have hreadable := hinvariant.tempReadable hnb
  rcases tempToMainCellTraced_safe cursor.state cursor.dest cursor.ssb
      hdest htemp hinvariant.tempLive hreadable with
    ⟨state, hstate, htraceSafe, hframe⟩
  have hcore : tempToMainCell? cursor.state cursor.dest cursor.ssb =
      some state := by
    rw [← erase_tempToMainCellTraced]
    exact hstate
  have htempEq := tempToMainCell_temp_eq_of_eq_some cursor.state state
    cursor.dest cursor.ssb hcore
  have hentryMode : ∀ entry,
      mergeTempRead? cursor.state.a cursor.ssb = some entry →
        SortSlice.EntryMatchesValuesMode cursor.state.a.hasValues entry := by
    intro entry hentry
    have hindex : cursor.ssb = Int.ofNat (cursor.nb - 1) := by
      have heq := hinvariant.ssbEquation
      simp only [Int.ofNat_eq_natCast] at heq ⊢
      omega
    rcases hinvariant.tempValuesMode (cursor.nb - 1) (by omega) with
      ⟨stored, hstored, hstoredMode⟩
    rw [erase_mergeTempRead] at hstored
    simp only [zero_add] at hstored
    rw [hindex] at hentry
    have heq : stored = entry := Option.some.inj (hstored.symm.trans hentry)
    simpa [heq] using hstoredMode
  have hmode := tempToMainCell_valuesMode_of_eq_some cursor.state state
    cursor.dest cursor.ssb hinvariant.valuesMode hentryMode hcore
  let copied : MergeHiDataCursorResult κ ν :=
    { state := state, dst := cursor.dest - 1, src := cursor.ssb - 1 }
  have hcopied :
      (mergeHiCopyTempDecrTraced? cursor.state cursor.dest
        cursor.ssb).result = some copied := by
    simp [mergeHiCopyTempDecrTraced?, TraceResult.map, hstate, copied]
  have hnextInv : MergeHiCursorInvariant origin request
      { cursor with
        state := copied.state
        dest := copied.dst
        ssb := copied.src
        nb := cursor.nb - 1 } := by
    exact hinvariant.copyB state hframe htempEq hmode hnb
  exact ⟨copied, hcopied, MovementTraceSafe.map _ _ htraceSafe,
    hnextInv, rfl, rfl⟩

/-- The common remainder path is total and safe for every invariant cursor.
The `nb = 0` hedge is retained as an access-free success; the nonempty branch
consumes the classified final-copy provenance permit. -/
private theorem mergeHiSucceedTraced_safe
    (origin : MergeState κ ν) (request : Nat) (cursor : MergeHiCursor κ ν)
    (hinvariant : MergeHiCursorInvariant origin request cursor) :
    ∃ result, MergeHiCorePost origin request
      (mergeHiSucceedTraced? cursor) (mergeHiSucceed? cursor) result := by
  by_cases hnb : cursor.nb = 0
  · let result : MergeHiResult κ ν :=
      { state := cursor.state, returnCode := 0, fuelExhausted := false }
    refine ⟨result, ?_⟩
    refine
      { resultEq := ?_
        returnCode := rfl
        resultFuel := rfl
        traceSafe := ?_
        exactErasure := erase_mergeHiSucceedTraced cursor
        tempInvariant := hinvariant.tempInvariant
        tempLive := hinvariant.tempLive
        requestFits := hinvariant.requestFits
        valuesMode := hinvariant.valuesMode
        stableFrame := hinvariant.stableFrame
        storageFrame := hinvariant.storageFrame }
    · simp [mergeHiSucceedTraced?, hnb, TraceResult.map,
        TraceResult.pure, result]
    · rw [mergeHiSucceedTraced?, if_pos hnb]
      exact MovementTraceSafe.map _ _
        (MovementTraceSafe.pure cursor.state)
  · have hnbPositive : 0 < cursor.nb := Nat.pos_of_ne_zero hnb
    have hstart :
        cursor.dest - Int.ofNat (cursor.nb - 1) =
          cursor.basea + Int.ofNat cursor.na := by
      have hdest := hinvariant.destEquation
      simp only [Int.ofNat_eq_natCast, Nat.cast_add] at hdest ⊢
      omega
    have hmain : SortSlice.RangeInBounds cursor.state.data
        (cursor.dest - Int.ofNat (cursor.nb - 1)) cursor.nb := by
      rw [hstart]
      constructor
      · exact add_nonneg hinvariant.baseNonnegative (Int.natCast_nonneg _)
      · have hrange := hinvariant.mainRange
        simpa only [Int.ofNat_eq_natCast, Nat.cast_add, add_assoc] using hrange
    have htemp : TempRangeInBounds cursor.state.a 0 cursor.nb := by
      constructor
      · rfl
      · simpa [Int.ofNat_eq_natCast] using
          Int.ofNat_le.mpr hinvariant.tempCapacity
    rcases tempToMainMemcpyTraced_post (.hi .finalTempToData)
        mergeHiFinalTempToDataPermit cursor.nb cursor.state
        (cursor.dest - Int.ofNat (cursor.nb - 1)) 0 hmain htemp
        hinvariant.tempValuesMode hinvariant.tempInvariant hinvariant.tempLive
        hinvariant.valuesMode with ⟨state, hpost⟩
    let result : MergeHiResult κ ν :=
      { state := state, returnCode := 0, fuelExhausted := false }
    refine ⟨result, ?_⟩
    refine
      { resultEq := ?_
        returnCode := rfl
        resultFuel := rfl
        traceSafe := ?_
        exactErasure := erase_mergeHiSucceedTraced cursor
        tempInvariant := hpost.tempInvariant
        tempLive := hpost.tempLive
        requestFits := ?_
        valuesMode := hpost.valuesMode
        stableFrame := hinvariant.stableFrame.trans
          (MergeHiStableFrame.of_movement hpost.frame)
        storageFrame := hinvariant.storageFrame.trans
          (MergeHiStorageFrame.of_movement hpost.frame) }
    · rw [mergeHiSucceedTraced?, if_neg hnb]
      change Option.map _ _ = some result
      rw [hpost.success]
      rfl
    · rw [mergeHiSucceedTraced?, if_neg hnb]
      exact MovementTraceSafe.map _ _ hpost.traceSafe
    · change request ≤ state.alloced.toNat
      rw [hpost.frame.alloced]
      exact hinvariant.requestFits

private theorem mainDataMemmove_temp_eq_of_eq_some
    (state result : MergeState κ ν) (dst src : Int) (count : Nat)
    (hresult : mainDataMemmove? state dst src count = some result) :
    result.a = state.a := by
  unfold mainDataMemmove? at hresult
  rcases Option.bind_eq_some_iff.mp hresult with ⟨data, _hmove, hfinal⟩
  injection hfinal with hfinal
  subst result
  rfl

theorem mergeHiMoveABlockTraced_safe
    (origin : MergeState κ ν) (request : Nat)
    (cursor : MergeHiCursor κ ν)
    (hinvariant : MergeHiCursorInvariant origin request cursor)
    (count : Nat) (hcount : count ≤ cursor.na) :
    ∃ moved,
      (mergeHiMoveABlockTraced? cursor count).result = some moved ∧
      MovementTraceSafe (mergeHiMoveABlockTraced? cursor count) ∧
      MergeHiCursorInvariant origin request moved ∧
      moved.na = cursor.na - count ∧ moved.nb = cursor.nb := by
  by_cases hzero : count = 0
  · subst count
    refine ⟨cursor, ?_, ?_, hinvariant, rfl, rfl⟩
    · rfl
    · exact MovementTraceSafe.pure cursor
  · have hpositive : 0 < count := Nat.pos_of_ne_zero hzero
    have hsrcStart : cursor.ssa - Int.ofNat count + 1 =
        cursor.basea + Int.ofNat (cursor.na - count) := by
      have heq := hinvariant.ssaEquation
      simp only [Int.ofNat_eq_natCast, Nat.cast_sub hcount] at heq ⊢
      omega
    have hdstStart : cursor.dest - Int.ofNat count + 1 =
        cursor.basea + Int.ofNat (cursor.na + cursor.nb - count) := by
      have heq := hinvariant.destEquation
      have hsum : count ≤ cursor.na + cursor.nb := hcount.trans (Nat.le_add_right _ _)
      simp only [Int.ofNat_eq_natCast, Nat.cast_add, Nat.cast_sub hsum]
        at heq ⊢
      omega
    have hsrc : SortSlice.RangeInBounds cursor.state.data
        (cursor.ssa - Int.ofNat count + 1) count := by
      rw [hsrcStart]
      constructor
      · exact add_nonneg hinvariant.baseNonnegative (Int.natCast_nonneg _)
      · have hrange := hinvariant.mainRange
        simp only [Int.ofNat_eq_natCast, Nat.cast_add, Nat.cast_sub hcount]
          at hrange ⊢
        omega
    have hdst : SortSlice.RangeInBounds cursor.state.data
        (cursor.dest - Int.ofNat count + 1) count := by
      rw [hdstStart]
      constructor
      · exact add_nonneg hinvariant.baseNonnegative (Int.natCast_nonneg _)
      · have hrange := hinvariant.mainRange
        have hsum : count ≤ cursor.na + cursor.nb :=
          hcount.trans (Nat.le_add_right _ _)
        simp only [Int.ofNat_eq_natCast, Nat.cast_add, Nat.cast_sub hsum]
          at hrange ⊢
        omega
    rcases mainDataMemmoveTraced_safe cursor.state
        (cursor.dest - Int.ofNat count + 1)
        (cursor.ssa - Int.ofNat count + 1) count
        hinvariant.tempInvariant hinvariant.tempLive hinvariant.valuesMode
        hdst hsrc with ⟨state, hpost⟩
    have htemp := mainDataMemmove_temp_eq_of_eq_some cursor.state state
      (cursor.dest - Int.ofNat count + 1)
      (cursor.ssa - Int.ofNat count + 1) count (by
        rw [← hpost.exactErasure]
        exact hpost.success)
    let moved : MergeHiCursor κ ν :=
      { cursor with
        state := state
        dest := cursor.dest - Int.ofNat count
        ssa := cursor.ssa - Int.ofNat count
        na := cursor.na - count }
    have hmovedInv : MergeHiCursorInvariant origin request moved := by
      exact hinvariant.copyABlock count hcount state hpost.frame htemp
        hpost.valuesMode
    refine ⟨moved, ?_, ?_, hmovedInv, rfl, rfl⟩
    · rw [mergeHiMoveABlockTraced?, if_neg hzero]
      simp only [TraceResult.map]
      rw [hpost.success]
      rfl
    · rw [mergeHiMoveABlockTraced?, if_neg hzero]
      exact MovementTraceSafe.map _ _ hpost.traceSafe

theorem mergeHiMoveBBlockTraced_safe
    (origin : MergeState κ ν) (request : Nat)
    (cursor : MergeHiCursor κ ν)
    (hinvariant : MergeHiCursorInvariant origin request cursor)
    (count : Nat) (hcount : count ≤ cursor.nb) :
    ∃ moved,
      (mergeHiMoveBBlockTraced? cursor count).result = some moved ∧
      MovementTraceSafe (mergeHiMoveBBlockTraced? cursor count) ∧
      MergeHiCursorInvariant origin request moved ∧
      moved.na = cursor.na ∧ moved.nb = cursor.nb - count := by
  by_cases hzero : count = 0
  · subst count
    refine ⟨cursor, ?_, ?_, hinvariant, rfl, rfl⟩
    · rfl
    · exact MovementTraceSafe.pure cursor
  · have hsrcStart : cursor.ssb - Int.ofNat count + 1 =
        Int.ofNat (cursor.nb - count) := by
      have heq := hinvariant.ssbEquation
      simp only [Int.ofNat_eq_natCast, Nat.cast_sub hcount] at heq ⊢
      omega
    have hdstStart : cursor.dest - Int.ofNat count + 1 =
        cursor.basea + Int.ofNat (cursor.na + cursor.nb - count) := by
      have heq := hinvariant.destEquation
      have hsum : count ≤ cursor.na + cursor.nb :=
        hcount.trans (Nat.le_add_left _ _)
      simp only [Int.ofNat_eq_natCast, Nat.cast_add, Nat.cast_sub hsum]
        at heq ⊢
      omega
    have hmain : SortSlice.RangeInBounds cursor.state.data
        (cursor.dest - Int.ofNat count + 1) count := by
      rw [hdstStart]
      constructor
      · exact add_nonneg hinvariant.baseNonnegative (Int.natCast_nonneg _)
      · have hrange := hinvariant.mainRange
        have hsum : count ≤ cursor.na + cursor.nb :=
          hcount.trans (Nat.le_add_left _ _)
        simp only [Int.ofNat_eq_natCast, Nat.cast_add, Nat.cast_sub hsum]
          at hrange ⊢
        omega
    have htemp : TempRangeInBounds cursor.state.a
        (cursor.ssb - Int.ofNat count + 1) count := by
      rw [hsrcStart]
      constructor
      · exact Int.natCast_nonneg _
      · have hcapacity := hinvariant.tempCapacity
        have hbound : cursor.nb - count + count ≤
            cursor.state.a.cells.size := by
          rw [Nat.sub_add_cancel hcount]
          exact hcapacity
        simpa only [Int.ofNat_eq_natCast, Nat.cast_add,
          Nat.cast_sub hcount] using Int.ofNat_le.mpr hbound
    have htempMode : TempRangeValuesMode cursor.state.a
        (cursor.ssb - Int.ofNat count + 1) count := by
      rw [hsrcStart]
      intro offset hoffset
      have htotal : cursor.nb - count + offset < cursor.nb := by omega
      rcases hinvariant.tempValuesMode (cursor.nb - count + offset) htotal with
        ⟨entry, hread, hmode⟩
      refine ⟨entry, ?_, hmode⟩
      simpa only [zero_add, Int.ofNat_eq_natCast, Nat.cast_add] using hread
    rcases tempToMainMemcpyTraced_post (.hi .gallopTempToData)
        mergeHiGallopTempToDataPermit count cursor.state
        (cursor.dest - Int.ofNat count + 1)
        (cursor.ssb - Int.ofNat count + 1) hmain htemp htempMode
        hinvariant.tempInvariant hinvariant.tempLive hinvariant.valuesMode with
      ⟨state, hpost⟩
    have hcore : tempToMainMemcpy? count cursor.state
        (cursor.dest - Int.ofNat count + 1)
        (cursor.ssb - Int.ofNat count + 1) = some state := by
      rw [← hpost.exactErasure]
      exact hpost.success
    have htempEq := tempToMainMemcpy_temp_eq_of_eq_some count cursor.state state
      (cursor.dest - Int.ofNat count + 1)
      (cursor.ssb - Int.ofNat count + 1) hcore
    let moved : MergeHiCursor κ ν :=
      { cursor with
        state := state
        dest := cursor.dest - Int.ofNat count
        ssb := cursor.ssb - Int.ofNat count
        nb := cursor.nb - count }
    have hmovedInv : MergeHiCursorInvariant origin request moved := by
      exact hinvariant.copyBBlock count hcount state hpost.frame htempEq
        hpost.valuesMode
    refine ⟨moved, ?_, ?_, hmovedInv, rfl, rfl⟩
    · rw [mergeHiMoveBBlockTraced?, if_neg hzero]
      simp only [TraceResult.map]
      rw [hpost.success]
      rfl
    · rw [mergeHiMoveBBlockTraced?, if_neg hzero]
      exact MovementTraceSafe.map _ _ hpost.traceSafe

private theorem mergeHiGallopBFinishTraced_safe
    (origin : MergeState κ ν) (request fuel : Nat)
    (afterB : MergeHiCursor κ ν) (aCount bCount : Nat)
    (movedB : MergeHiCursor κ ν)
    (hinvariant : MergeHiCursorInvariant origin request movedB)
    (hfuel : MergeHiFuelInvariant fuel movedB)
    (hna : 0 < movedB.na)
    (nextTraced : MergeHiCursor κ ν → TraceResult (MergeHiResult κ ν))
    (next : MergeHiCursor κ ν → Option (MergeHiResult κ ν))
    (hnext : MergeHiContinuationSafe origin request fuel nextTraced next) :
    ∃ result, MergeHiCorePost origin request
      (mergeHiGallopBFinishTraced? afterB aCount bCount movedB nextTraced)
      (mergeHiGallopBFinish? afterB aCount bCount movedB next) result := by
  by_cases hterminal : movedB.nb = 0 ∨ movedB.nb = 1
  · rcases hnext movedB hinvariant hfuel with ⟨result, hresult⟩
    exact ⟨result, by
      simpa [mergeHiGallopBFinishTraced?, mergeHiGallopBFinish?, hterminal]
        using hresult⟩
  · rcases mergeHiCopyDataDecrTraced_safe origin request movedB hinvariant
        hna with ⟨copiedA, hcopy, hcopySafe, hcopiedInv, _hdst, _hsrc⟩
    let afterA : MergeHiCursor κ ν :=
      { movedB with
        state := copiedA.state
        dest := copiedA.dst
        ssa := copiedA.src
        na := movedB.na - 1 }
    have hafterInv : MergeHiCursorInvariant origin request afterA := hcopiedInv
    have hafterFuel : MergeHiFuelInvariant fuel afterA := by
      have hf := hfuel
      change movedB.na + movedB.nb < fuel at hf
      change movedB.na - 1 + movedB.nb < fuel
      omega
    let tracedTail := fun copied : MergeHiDataCursorResult κ ν =>
      let cursor : MergeHiCursor κ ν :=
        { movedB with
          state := copied.state
          dest := copied.dst
          ssa := copied.src
          na := movedB.na - 1 }
      if cursor.na = 0 then
        nextTraced cursor
      else if mergeHiCountAtLeast aCount MIN_GALLOP ||
          mergeHiCountAtLeast bCount MIN_GALLOP then
        nextTraced { cursor with phase := .galloping aCount bCount }
      else
        let minGallop := afterB.minGallop + 1
        let state := { cursor.state with min_gallop := minGallop }
        nextTraced
          { cursor with
            state := state
            minGallop := minGallop
            phase := .straight 0 0 }
    let tail := fun copied : MergeHiDataCursorResult κ ν =>
      let cursor : MergeHiCursor κ ν :=
        { movedB with
          state := copied.state
          dest := copied.dst
          ssa := copied.src
          na := movedB.na - 1 }
      if cursor.na = 0 then
        next cursor
      else if mergeHiCountAtLeast aCount MIN_GALLOP ||
          mergeHiCountAtLeast bCount MIN_GALLOP then
        next { cursor with phase := .galloping aCount bCount }
      else
        let minGallop := afterB.minGallop + 1
        let state := { cursor.state with min_gallop := minGallop }
        next
          { cursor with
            state := state
            minGallop := minGallop
            phase := .straight 0 0 }
    have htail : ∃ result, MergeHiCorePost origin request
        (tracedTail copiedA) (tail copiedA) result := by
      by_cases hzero : afterA.na = 0
      · rcases hnext afterA hafterInv hafterFuel with ⟨result, hresult⟩
        have hzero' : movedB.na - 1 = 0 := by simpa [afterA] using hzero
        exact ⟨result, by
          simp only [tracedTail, tail]
          rw [if_pos hzero', if_pos hzero']
          exact hresult⟩
      · have hzero' : ¬ movedB.na - 1 = 0 := by simpa [afterA] using hzero
        let gallopAgain := mergeHiCountAtLeast aCount MIN_GALLOP ||
          mergeHiCountAtLeast bCount MIN_GALLOP
        by_cases hgallop : gallopAgain = true
        · let nextCursor : MergeHiCursor κ ν :=
            { afterA with phase := .galloping aCount bCount }
          have hnextInv : MergeHiCursorInvariant origin request nextCursor := by
            exact hafterInv.setControl afterA.minGallop
              (.galloping aCount bCount)
          have hnextFuel : MergeHiFuelInvariant fuel nextCursor := by
            change afterA.na + afterA.nb < fuel
            exact hafterFuel
          rcases hnext nextCursor hnextInv hnextFuel with ⟨result, hresult⟩
          exact ⟨result, by
            simp only [tracedTail, tail]
            rw [if_neg hzero', if_neg hzero']
            have hgallop' :
                (mergeHiCountAtLeast aCount MIN_GALLOP ||
                  mergeHiCountAtLeast bCount MIN_GALLOP) = true := by
              exact hgallop
            rw [if_pos hgallop', if_pos hgallop']
            exact hresult⟩
        · let minGallop := afterB.minGallop + 1
          let nextCursor : MergeHiCursor κ ν :=
            { afterA with
              state := { afterA.state with min_gallop := minGallop }
              minGallop := minGallop
              phase := .straight 0 0 }
          have hnextInv : MergeHiCursorInvariant origin request nextCursor := by
            exact (hafterInv.setMinGallop minGallop).setControl minGallop
              (.straight 0 0)
          have hnextFuel : MergeHiFuelInvariant fuel nextCursor := by
            change afterA.na + afterA.nb < fuel
            exact hafterFuel
          rcases hnext nextCursor hnextInv hnextFuel with ⟨result, hresult⟩
          exact ⟨result, by
            simp only [tracedTail, tail]
            rw [if_neg hzero', if_neg hzero']
            have hgallop' : ¬
                (mergeHiCountAtLeast aCount MIN_GALLOP ||
                  mergeHiCountAtLeast bCount MIN_GALLOP) = true := by
              exact hgallop
            rw [if_neg hgallop', if_neg hgallop']
            exact hresult⟩
    rcases htail with ⟨result, htail⟩
    have hpost := MergeHiCorePost.prepend origin request
      (mergeHiCopyDataDecrTraced? movedB.state movedB.dest movedB.ssa)
      tracedTail tail copiedA result hcopy hcopySafe htail
    exact ⟨result, by
      simpa [mergeHiGallopBFinishTraced?, mergeHiGallopBFinish?, hterminal,
        tracedTail, tail] using hpost⟩

private theorem mergeHiGallopBAfterTraced_safe
    (origin : MergeState κ ν) (request fuel : Nat)
    (afterB : MergeHiCursor κ ν) (aCount : Nat)
    (gallopB : GallopResult)
    (hinvariant : MergeHiCursorInvariant origin request afterB)
    (hfuel : MergeHiFuelInvariant fuel afterB)
    (hna : 0 < afterB.na)
    (_hbound : gallopB.index ≤ afterB.nb)
    (hnotFuel : gallopB.fuelExhausted = false)
    (nextTraced : MergeHiCursor κ ν → TraceResult (MergeHiResult κ ν))
    (next : MergeHiCursor κ ν → Option (MergeHiResult κ ν))
    (hnext : MergeHiContinuationSafe origin request fuel nextTraced next) :
    ∃ result, MergeHiCorePost origin request
      (mergeHiGallopBAfterTraced? afterB aCount gallopB nextTraced)
      (mergeHiGallopBAfter? afterB aCount gallopB next) result := by
  let bCount := afterB.nb - gallopB.index
  have hbCount : bCount ≤ afterB.nb := Nat.sub_le _ _
  rcases mergeHiMoveBBlockTraced_safe origin request afterB hinvariant
      bCount hbCount with
    ⟨movedB, hmove, hmoveSafe, hmovedInv, hmovedNa, hmovedNb⟩
  have hmovedFuel : MergeHiFuelInvariant fuel movedB := by
    have hf := hfuel
    change afterB.na + afterB.nb < fuel at hf
    change movedB.na + movedB.nb < fuel
    rw [hmovedNa, hmovedNb]
    omega
  have hmovedNaPositive : 0 < movedB.na := by simpa [hmovedNa] using hna
  rcases mergeHiGallopBFinishTraced_safe origin request fuel afterB aCount
      bCount movedB hmovedInv hmovedFuel hmovedNaPositive nextTraced next hnext with
    ⟨result, hfinish⟩
  have hpost := MergeHiCorePost.prepend origin request
    (mergeHiMoveBBlockTraced? afterB bCount)
    (fun moved => mergeHiGallopBFinishTraced? afterB aCount bCount moved
      nextTraced)
    (fun moved => mergeHiGallopBFinish? afterB aCount bCount moved next)
    movedB result hmove hmoveSafe hfinish
  exact ⟨result, by
    simpa [mergeHiGallopBAfterTraced?, mergeHiGallopBAfter?, hnotFuel,
      bCount] using hpost⟩

private theorem mergeHiGallopBTraced_safe
    (origin : MergeState κ ν) (request fuel : Nat)
    (afterB : MergeHiCursor κ ν) (aCount : Nat)
    (hinvariant : MergeHiCursorInvariant origin request afterB)
    (hfuel : MergeHiFuelInvariant fuel afterB)
    (hna : 0 < afterB.na) (hnb : 1 < afterB.nb)
    (nextTraced : MergeHiCursor κ ν → TraceResult (MergeHiResult κ ν))
    (next : MergeHiCursor κ ν → Option (MergeHiResult κ ν))
    (hnext : MergeHiContinuationSafe origin request fuel nextTraced next) :
    ∃ result, MergeHiCorePost origin request
      (mergeHiGallopBTraced? afterB aCount nextTraced)
      (mergeHiGallopB? afterB aCount next) result := by
  have hssa := hinvariant.ssaInBounds hna
  rcases SortSlice.read_eq_some_of_indexInBounds afterB.state.data afterB.ssa
      hssa with ⟨left, hleft⟩
  have hleftResult :
      (TraceResult.sortSliceKeysRead? afterB.state.data afterB.ssa).result =
        some left := by
    change (TraceResult.sortSliceKeysRead? afterB.state.data afterB.ssa).erase =
      some left
    simpa using hleft
  have hleftSafe := mergeHiMainKeyReadTraced_safe afterB.state.data afterB.ssa
    hssa
  have hprefixInitialized : MergeHiTempPrefixInitialized afterB.state.a
      afterB.nb := by
    intro offset hoffset
    rcases hinvariant.tempValuesMode offset hoffset with
      ⟨entry, hread, _hmode⟩
    rw [erase_mergeTempRead] at hread
    refine ⟨entry, ?_⟩
    simpa [mergeTempRead_eq_mergeHiTempRead] using hread
  rcases mergeHiInitializedTempPrefix_exists_of_initialized afterB.state.a
      afterB.nb hprefixInitialized with ⟨temp, htemp⟩
  have htempResult :
      (mergeHiTraceOption (initializedTempPrefix? afterB.state.a
        afterB.nb)).result = some temp := by
    rw [htemp]
    rfl
  have htempSafe : MovementTraceSafe
      (mergeHiTraceOption (initializedTempPrefix? afterB.state.a
        afterB.nb)) := by
    simpa [mergeHiTraceOption, htemp] using MovementTraceSafe.pure temp
  have hagrees := initializedTempPrefix_agreesWithSlice_of_eq_some
    afterB.state.a afterB.nb temp htemp
  rcases gallopLeft_temporary_safe afterB.state afterB.state.a 0 temp 0
      left.key afterB.nb (afterB.nb - 1) hinvariant.temporaryValidRange
      hinvariant.tempLive hagrees (by omega) (by omega)
      hinvariant.rightWordBound with
    ⟨gallopB, hgallop, hgallopFuel, hgallopBound, htraceFuel,
      htracePushes, htraceBounds, htraceLive, hgallopErase⟩
  have hgallopSafe : MovementTraceSafe
      (gallopLeftTraced? afterB.state (.temporary afterB.state.a 0)
        left.key afterB.nb (afterB.nb - 1)) :=
    ⟨htraceFuel, htracePushes, htraceBounds, htraceLive⟩
  rcases mergeHiGallopBAfterTraced_safe origin request fuel afterB aCount
      gallopB hinvariant hfuel hna hgallopBound hgallopFuel nextTraced next
      hnext with ⟨result, hafter⟩
  have hgallopPost := MergeHiCorePost.prepend origin request
    (gallopLeftTraced? afterB.state (.temporary afterB.state.a 0)
      left.key afterB.nb (afterB.nb - 1))
    (fun gallop => mergeHiGallopBAfterTraced? afterB aCount gallop
      nextTraced)
    (fun gallop => mergeHiGallopBAfter? afterB aCount gallop next)
    gallopB result hgallop hgallopSafe hafter
  have hgallopPost' : MergeHiCorePost origin request
      ((gallopLeftTraced? afterB.state (.temporary afterB.state.a 0)
        left.key afterB.nb (afterB.nb - 1)).bind fun gallop =>
          mergeHiGallopBAfterTraced? afterB aCount gallop nextTraced)
      (mergeHiBindOptionAcross
        (gallopLeft? afterB.state temp 0 left.key afterB.nb
          (afterB.nb - 1))
        (fun gallop => mergeHiGallopBAfter? afterB aCount gallop next))
      result := by
    apply hgallopPost.reference_eq
    rw [hgallopErase]
    unfold mergeHiBindOptionAcross
    cases gallopLeft? afterB.state temp 0 left.key afterB.nb
      (afterB.nb - 1) <;> rfl
  have htempPost := MergeHiCorePost.prepend origin request
    (mergeHiTraceOption (initializedTempPrefix? afterB.state.a afterB.nb))
    (fun _temp =>
      (gallopLeftTraced? afterB.state (.temporary afterB.state.a 0)
        left.key afterB.nb (afterB.nb - 1)).bind fun gallop =>
          mergeHiGallopBAfterTraced? afterB aCount gallop nextTraced)
    (fun materialized => mergeHiBindOptionAcross
      (gallopLeft? afterB.state materialized 0 left.key afterB.nb
        (afterB.nb - 1))
      (fun gallop => mergeHiGallopBAfter? afterB aCount gallop next))
    temp result htempResult htempSafe hgallopPost'
  have htempPost' : MergeHiCorePost origin request
      ((mergeHiTraceOption
        (initializedTempPrefix? afterB.state.a afterB.nb)).bind fun _temp =>
          (gallopLeftTraced? afterB.state (.temporary afterB.state.a 0)
            left.key afterB.nb (afterB.nb - 1)).bind fun gallop =>
              mergeHiGallopBAfterTraced? afterB aCount gallop nextTraced)
      ((initializedTempPrefix? afterB.state.a afterB.nb).bind fun materialized =>
        mergeHiBindOptionAcross
          (gallopLeft? afterB.state materialized 0 left.key afterB.nb
            (afterB.nb - 1))
          (fun gallop => mergeHiGallopBAfter? afterB aCount gallop next))
      result := by
    apply htempPost.reference_eq
    rw [erase_mergeHiTraceOption]
  have hleftPost := MergeHiCorePost.prepend origin request
    (TraceResult.sortSliceKeysRead? afterB.state.data afterB.ssa)
    (fun read =>
      (mergeHiTraceOption
        (initializedTempPrefix? afterB.state.a afterB.nb)).bind fun _temp =>
          (gallopLeftTraced? afterB.state (.temporary afterB.state.a 0)
            read.key afterB.nb (afterB.nb - 1)).bind fun gallop =>
              mergeHiGallopBAfterTraced? afterB aCount gallop nextTraced)
    (fun read =>
      (initializedTempPrefix? afterB.state.a afterB.nb).bind fun materialized =>
        mergeHiBindOptionAcross
          (gallopLeft? afterB.state materialized 0 read.key afterB.nb
            (afterB.nb - 1))
          (fun gallop => mergeHiGallopBAfter? afterB aCount gallop next))
    left result hleftResult hleftSafe htempPost'
  have hleftPost' := hleftPost.reference_eq
    (mergeHiGallopB_eq_helpers afterB aCount next).symm
  exact ⟨result, by
    simpa only [mergeHiGallopBTraced?, TraceResult.erase_sortSliceKeysRead]
      using hleftPost'⟩

private theorem mergeHiGallopRoundFinishTraced_safe
    (origin : MergeState κ ν) (request fuel : Nat)
    (movedA : MergeHiCursor κ ν) (aCount : Nat)
    (hinvariant : MergeHiCursorInvariant origin request movedA)
    (hbudget : movedA.na + movedA.nb ≤ fuel)
    (hterminalFuel : movedA.na = 0 → MergeHiFuelInvariant fuel movedA)
    (hnb : 1 < movedA.nb)
    (nextTraced : MergeHiCursor κ ν → TraceResult (MergeHiResult κ ν))
    (next : MergeHiCursor κ ν → Option (MergeHiResult κ ν))
    (hnext : MergeHiContinuationSafe origin request fuel nextTraced next) :
    ∃ result, MergeHiCorePost origin request
      (mergeHiGallopRoundFinishTraced? movedA aCount nextTraced)
      (mergeHiGallopRoundFinish? movedA aCount next) result := by
  by_cases hnaZero : movedA.na = 0
  · rcases hnext movedA hinvariant (hterminalFuel hnaZero) with
      ⟨result, hresult⟩
    exact ⟨result, by
      simpa [mergeHiGallopRoundFinishTraced?, mergeHiGallopRoundFinish?,
        hnaZero] using hresult⟩
  · have hna : 0 < movedA.na := Nat.pos_of_ne_zero hnaZero
    rcases mergeHiCopyTempDecrTraced_safe origin request movedA hinvariant
        (by omega) with
      ⟨copiedB, hcopy, hcopySafe, hcopiedInv, _hdst, _hsrc⟩
    let afterB : MergeHiCursor κ ν :=
      { movedA with
        state := copiedB.state
        dest := copiedB.dst
        ssb := copiedB.src
        nb := movedA.nb - 1 }
    have hafterInv : MergeHiCursorInvariant origin request afterB := hcopiedInv
    have hafterFuel : MergeHiFuelInvariant fuel afterB := by
      change movedA.na + (movedA.nb - 1) < fuel
      omega
    let tracedTail := fun copied : MergeHiDataCursorResult κ ν =>
      let cursor : MergeHiCursor κ ν :=
        { movedA with
          state := copied.state
          dest := copied.dst
          ssb := copied.src
          nb := movedA.nb - 1 }
      if cursor.nb = 1 then nextTraced cursor
      else mergeHiGallopBTraced? cursor aCount nextTraced
    let tail := fun copied : MergeHiDataCursorResult κ ν =>
      let cursor : MergeHiCursor κ ν :=
        { movedA with
          state := copied.state
          dest := copied.dst
          ssb := copied.src
          nb := movedA.nb - 1 }
      if cursor.nb = 1 then next cursor
      else mergeHiGallopB? cursor aCount next
    have htail : ∃ result, MergeHiCorePost origin request
        (tracedTail copiedB) (tail copiedB) result := by
      by_cases hone : afterB.nb = 1
      · rcases hnext afterB hafterInv hafterFuel with ⟨result, hresult⟩
        have hone' : movedA.nb - 1 = 1 := by simpa [afterB] using hone
        exact ⟨result, by
          simp only [tracedTail, tail]
          rw [if_pos hone', if_pos hone']
          exact hresult⟩
      · have hafterNa : 0 < afterB.na := by simpa [afterB] using hna
        have hafterNb : 1 < afterB.nb := by
          change 1 < movedA.nb - 1
          have hone' : ¬ movedA.nb - 1 = 1 := by
            simpa [afterB] using hone
          omega
        rcases mergeHiGallopBTraced_safe origin request fuel afterB aCount
            hafterInv hafterFuel hafterNa hafterNb nextTraced next hnext with
          ⟨result, hresult⟩
        have hone' : ¬ movedA.nb - 1 = 1 := by simpa [afterB] using hone
        exact ⟨result, by
          simp only [tracedTail, tail]
          rw [if_neg hone', if_neg hone']
          exact hresult⟩
    rcases htail with ⟨result, htail⟩
    have hpost := MergeHiCorePost.prepend origin request
      (mergeHiCopyTempDecrTraced? movedA.state movedA.dest movedA.ssb)
      tracedTail tail copiedB result hcopy hcopySafe htail
    exact ⟨result, by
      simpa [mergeHiGallopRoundFinishTraced?, mergeHiGallopRoundFinish?,
        hnaZero, tracedTail, tail] using hpost⟩

private theorem mergeHiGallopRoundAfterTraced_safe
    (origin : MergeState κ ν) (request fuel : Nat)
    (cursor : MergeHiCursor κ ν) (minGallop : PySSize)
    (state : MergeState κ ν) (gallopA : GallopResult)
    (hinvariant : MergeHiCursorInvariant origin request
      { cursor with state := state, minGallop := minGallop })
    (hfuel : MergeHiFuelInvariant (fuel + 1) cursor)
    (hna : 0 < cursor.na) (hnb : 1 < cursor.nb)
    (hbound : gallopA.index ≤ cursor.na)
    (hnotFuel : gallopA.fuelExhausted = false)
    (nextTraced : MergeHiCursor κ ν → TraceResult (MergeHiResult κ ν))
    (next : MergeHiCursor κ ν → Option (MergeHiResult κ ν))
    (hnext : MergeHiContinuationSafe origin request fuel nextTraced next) :
    ∃ result, MergeHiCorePost origin request
      (mergeHiGallopRoundAfterTraced? cursor minGallop state gallopA nextTraced)
      (mergeHiGallopRoundAfter? cursor minGallop state gallopA next) result := by
  let adjusted : MergeHiCursor κ ν :=
    { cursor with state := state, minGallop := minGallop }
  let aCount := cursor.na - gallopA.index
  have haCount : aCount ≤ adjusted.na := by
    simp [aCount, adjusted]
  rcases mergeHiMoveABlockTraced_safe origin request adjusted hinvariant
      aCount haCount with
    ⟨movedA, hmove, hmoveSafe, hmovedInv, hmovedNa, hmovedNb⟩
  have hmovedBudget : movedA.na + movedA.nb ≤ fuel := by
    have hf := hfuel
    change cursor.na + cursor.nb < fuel + 1 at hf
    rw [hmovedNa, hmovedNb]
    simp only [adjusted]
    omega
  have hmovedTerminalFuel : movedA.na = 0 →
      MergeHiFuelInvariant fuel movedA := by
    intro hmovedZero
    have hf := hfuel
    change cursor.na + cursor.nb < fuel + 1 at hf
    change movedA.na + movedA.nb < fuel
    rw [hmovedNa, hmovedNb]
    have hmovedZero' : adjusted.na - aCount = 0 := by
      rw [← hmovedNa]
      exact hmovedZero
    have hcursorZero : cursor.na - aCount = 0 := by
      simpa [adjusted] using hmovedZero'
    simp only [adjusted]
    have haPositive : 0 < aCount := by
      omega
    omega
  have hmovedNbPositive : 1 < movedA.nb := by
    simpa [hmovedNb, adjusted] using hnb
  rcases mergeHiGallopRoundFinishTraced_safe origin request fuel movedA aCount
      hmovedInv hmovedBudget hmovedTerminalFuel hmovedNbPositive nextTraced next
      hnext with ⟨result, hfinish⟩
  have hpost := MergeHiCorePost.prepend origin request
    (mergeHiMoveABlockTraced? adjusted aCount)
    (fun moved => mergeHiGallopRoundFinishTraced? moved aCount nextTraced)
    (fun moved => mergeHiGallopRoundFinish? moved aCount next)
    movedA result hmove hmoveSafe hfinish
  exact ⟨result, by
    simpa [mergeHiGallopRoundAfterTraced?, mergeHiGallopRoundAfter?,
      hnotFuel, adjusted, aCount] using hpost⟩

private theorem mergeHiGallopRoundTraced_safe
    (origin : MergeState κ ν) (request fuel : Nat)
    (cursor : MergeHiCursor κ ν)
    (hinvariant : MergeHiCursorInvariant origin request cursor)
    (hfuel : MergeHiFuelInvariant (fuel + 1) cursor)
    (hna : 0 < cursor.na) (hnb : 1 < cursor.nb)
    (nextTraced : MergeHiCursor κ ν → TraceResult (MergeHiResult κ ν))
    (next : MergeHiCursor κ ν → Option (MergeHiResult κ ν))
    (hnext : MergeHiContinuationSafe origin request fuel nextTraced next) :
    ∃ result, MergeHiCorePost origin request
      (mergeHiGallopRoundTraced? cursor nextTraced)
      (mergeHiGallopRound? cursor next) result := by
  let minGallop := mergeHiDecreaseMinGallop cursor.minGallop
  let state : MergeState κ ν := { cursor.state with min_gallop := minGallop }
  let adjusted : MergeHiCursor κ ν :=
    { cursor with state := state, minGallop := minGallop }
  have hadjustedInv : MergeHiCursorInvariant origin request adjusted := by
    exact hinvariant.setMinGallop minGallop
  have hnbPositive : 0 < adjusted.nb := by
    simpa [adjusted] using Nat.zero_lt_of_lt hnb
  rcases hadjustedInv.tempReadable hnbPositive with ⟨right, hright⟩
  have hrightResult :
      (TraceResult.tempPayloadRead? state.a cursor.ssb).result = some right := by
    change (TraceResult.tempPayloadRead? state.a cursor.ssb).erase = some right
    rw [erase_mergeTempRead]
    simpa [adjusted, state] using hright
  have hrightSafe : MovementTraceSafe
      (TraceResult.tempPayloadRead? state.a cursor.ssb) := by
    apply mergeHiTempReadTraced_safe
    · simpa [adjusted, state] using hadjustedInv.ssbInBounds hnbPositive
    · simpa [adjusted, state] using hadjustedInv.tempLive
  have hvalid :
      (GallopKeySource.main state.data cursor.basea).ValidRange cursor.na := by
    simpa [adjusted, state] using hadjustedInv.mainValidRange
  rcases gallopRight_main_safe state state.data cursor.basea right.key
      cursor.na (cursor.na - 1) hvalid hna (by omega)
      hinvariant.leftWordBound with
    ⟨gallopA, hgallopResult, hgallopFuel, hgallopBound,
      hgallopTraceFuel, hgallopNoPushes, hgallopBounds, hgallopLive,
      hgallopErase⟩
  have hgallopSafe : MovementTraceSafe
      (gallopRightTraced? state (.main state.data cursor.basea) right.key
        cursor.na (cursor.na - 1)) :=
    ⟨hgallopTraceFuel, hgallopNoPushes, hgallopBounds, hgallopLive⟩
  rcases mergeHiGallopRoundAfterTraced_safe origin request fuel cursor
      minGallop state gallopA hadjustedInv hfuel hna hnb hgallopBound
      hgallopFuel nextTraced next hnext with ⟨result, hafter⟩
  have hgallopPost := MergeHiCorePost.prepend origin request
    (gallopRightTraced? state (.main state.data cursor.basea) right.key
      cursor.na (cursor.na - 1))
    (fun gallop =>
      mergeHiGallopRoundAfterTraced? cursor minGallop state gallop nextTraced)
    (fun gallop =>
      mergeHiGallopRoundAfter? cursor minGallop state gallop next)
    gallopA result hgallopResult hgallopSafe hafter
  have hgallopPost' : MergeHiCorePost origin request
      ((gallopRightTraced? state (.main state.data cursor.basea) right.key
        cursor.na (cursor.na - 1)).bind fun gallop =>
          mergeHiGallopRoundAfterTraced? cursor minGallop state gallop
            nextTraced)
      (mergeHiBindOptionAcross
        (gallopRight? state state.data cursor.basea right.key cursor.na
          (cursor.na - 1))
        (fun gallop =>
          mergeHiGallopRoundAfter? cursor minGallop state gallop next))
      result := by
    apply hgallopPost.reference_eq
    rw [hgallopErase]
    unfold mergeHiBindOptionAcross
    cases gallopRight? state state.data cursor.basea right.key cursor.na
      (cursor.na - 1) <;> rfl
  have hrightPost := MergeHiCorePost.prepend origin request
    (TraceResult.tempPayloadRead? state.a cursor.ssb)
    (fun entry =>
      (gallopRightTraced? state (.main state.data cursor.basea) entry.key
        cursor.na (cursor.na - 1)).bind fun gallop =>
          mergeHiGallopRoundAfterTraced? cursor minGallop state gallop
            nextTraced)
    (fun entry =>
      mergeHiBindOptionAcross
        (gallopRight? state state.data cursor.basea entry.key cursor.na
          (cursor.na - 1))
        (fun gallop =>
          mergeHiGallopRoundAfter? cursor minGallop state gallop next))
    right result hrightResult hrightSafe hgallopPost'
  have hrightPost' : MergeHiCorePost origin request
      ((TraceResult.tempPayloadRead? state.a cursor.ssb).bind fun entry =>
        (gallopRightTraced? state (.main state.data cursor.basea) entry.key
          cursor.na (cursor.na - 1)).bind fun gallop =>
            mergeHiGallopRoundAfterTraced? cursor minGallop state gallop
              nextTraced)
      ((mergeTempRead? state.a cursor.ssb).bind fun entry =>
        mergeHiBindOptionAcross
          (gallopRight? state state.data cursor.basea entry.key cursor.na
            (cursor.na - 1))
          (fun gallop =>
            mergeHiGallopRoundAfter? cursor minGallop state gallop next))
      result := by
    apply hrightPost.reference_eq
    rw [erase_mergeTempRead]
  have hrightPost'' := hrightPost'.reference_eq
    (by simpa [minGallop, state] using
      (mergeHiGallopRound_eq_helpers cursor next).symm)
  exact ⟨result, by
    simpa only [mergeHiGallopRoundTraced?] using hrightPost''⟩

/-- The `CopyA` tail is safe at the exact nonempty/single-right-entry state
where CPython jumps to it.  Its right-shift is overlap-safe memmove, followed
by the one physical temporary read that installs the smallest right entry. -/
private theorem mergeHiCopyATraced_safe
    (origin : MergeState κ ν) (request : Nat) (cursor : MergeHiCursor κ ν)
    (hinvariant : MergeHiCursorInvariant origin request cursor)
    (htail : cursor.nb = 1 ∧ 0 < cursor.na) :
    ∃ result, MergeHiCorePost origin request
      (mergeHiCopyATraced? cursor) (mergeHiCopyA? cursor) result := by
  have hsrcEq : cursor.ssa + (1 - Int.ofNat cursor.na) = cursor.basea := by
    have heq := hinvariant.ssaEquation
    simp only [Int.ofNat_eq_natCast] at heq ⊢
    omega
  have hdstEq : cursor.dest + (1 - Int.ofNat cursor.na) =
      cursor.basea + 1 := by
    have heq := hinvariant.destEquation
    simp only [htail.1, Int.ofNat_eq_natCast, Nat.cast_add,
      Nat.cast_one] at heq ⊢
    omega
  have hsrcRange : SortSlice.RangeInBounds cursor.state.data
      (cursor.ssa + (1 - Int.ofNat cursor.na)) cursor.na := by
    rw [hsrcEq]
    constructor
    · exact hinvariant.baseNonnegative
    · have hrange := hinvariant.mainRange
      simp only [htail.1, Int.ofNat_eq_natCast, Nat.cast_add,
        Nat.cast_one] at hrange ⊢
      omega
  have hdstRange : SortSlice.RangeInBounds cursor.state.data
      (cursor.dest + (1 - Int.ofNat cursor.na)) cursor.na := by
    rw [hdstEq]
    constructor
    · exact add_nonneg hinvariant.baseNonnegative (by norm_num)
    · have hrange := hinvariant.mainRange
      simp only [htail.1, Int.ofNat_eq_natCast, Nat.cast_add,
        Nat.cast_one] at hrange ⊢
      omega
  rcases mainDataMemmoveTraced_safe cursor.state
      (cursor.dest + (1 - Int.ofNat cursor.na))
      (cursor.ssa + (1 - Int.ofNat cursor.na)) cursor.na
      hinvariant.tempInvariant hinvariant.tempLive hinvariant.valuesMode
      hdstRange hsrcRange with ⟨shifted, hshift⟩
  have hshiftCore : mainDataMemmove? cursor.state
      (cursor.dest + (1 - Int.ofNat cursor.na))
      (cursor.ssa + (1 - Int.ofNat cursor.na)) cursor.na = some shifted := by
    rw [← hshift.exactErasure]
    exact hshift.success
  have htempEq : shifted.a = cursor.state.a :=
    mainDataMemmove_temp_eq_of_eq_some cursor.state shifted _ _ _ hshiftCore
  have hcellDstEq : cursor.dest - Int.ofNat cursor.na = cursor.basea := by
    have heq := hinvariant.destEquation
    simp only [htail.1, Int.ofNat_eq_natCast, Nat.cast_add,
      Nat.cast_one] at heq ⊢
    omega
  have hcellMain : SortSlice.IndexInBounds shifted.data
      (cursor.dest - Int.ofNat cursor.na) := by
    rw [hcellDstEq]
    constructor
    · exact hinvariant.baseNonnegative
    · have hrange := hinvariant.mainRange
      have hsize := hshift.frame.dataSize
      simp only [htail.1, Int.ofNat_eq_natCast, Nat.cast_add,
        Nat.cast_one] at hrange
      rw [hsize]
      simp only [Int.ofNat_eq_natCast]
      omega
  have hssb : cursor.ssb = 0 := by
    have heq := hinvariant.ssbEquation
    simp only [htail.1, Int.ofNat_eq_natCast, Nat.cast_one] at heq
    omega
  have hcellTemp : TempIndexInBounds shifted.a cursor.ssb := by
    rw [hssb, htempEq]
    constructor
    · rfl
    · have hcapacity := hinvariant.tempCapacity
      simp only [htail.1] at hcapacity
      have hpositive : 0 < cursor.state.a.cells.size := by omega
      rw [Int.ofNat_eq_natCast]
      exact_mod_cast hpositive
  have hshiftedTempMode : TempRangeValuesMode shifted.a 0 1 := by
    simpa only [htempEq, htail.1] using hinvariant.tempValuesMode
  rcases hshiftedTempMode.head with ⟨entry, hentryRead, hentryMode⟩
  have hreadable : ∃ entry, mergeTempRead? shifted.a cursor.ssb = some entry := by
    refine ⟨entry, ?_⟩
    rw [hssb]
    exact hentryRead
  rcases tempToMainCellTraced_safe shifted
      (cursor.dest - Int.ofNat cursor.na) cursor.ssb hcellMain hcellTemp
      hshift.tempLive hreadable with ⟨state, hcell, hcellSafe, hcellFrame⟩
  have hcellCore : tempToMainCell? shifted
      (cursor.dest - Int.ofNat cursor.na) cursor.ssb = some state := by
    rw [← erase_tempToMainCellTraced]
    exact hcell
  have hstateMode :
      SortSlice.ValuesModeInvariant state.a.hasValues state.data := by
    apply tempToMainCell_valuesMode_of_eq_some shifted state
      (cursor.dest - Int.ofNat cursor.na) cursor.ssb hshift.valuesMode
      _ hcellCore
    intro other hother
    rw [hssb] at hother
    rw [hentryRead] at hother
    injection hother with hother
    subst other
    exact hentryMode
  let result : MergeHiResult κ ν :=
    { state := state, returnCode := 0, fuelExhausted := false }
  refine ⟨result, ?_⟩
  refine
    { resultEq := ?_
      returnCode := rfl
      resultFuel := rfl
      traceSafe := ?_
      exactErasure := erase_mergeHiCopyATraced cursor
      tempInvariant := hcellFrame.tempStorageInv hshift.tempInvariant
      tempLive := hcellFrame.live hshift.tempLive
      requestFits := ?_
      valuesMode := hstateMode
      stableFrame := (hinvariant.stableFrame.trans
        (MergeHiStableFrame.of_movement hshift.frame)).trans
          (MergeHiStableFrame.of_movement hcellFrame)
      storageFrame := (hinvariant.storageFrame.trans
        (MergeHiStorageFrame.of_movement hshift.frame)).trans
          (MergeHiStorageFrame.of_movement hcellFrame) }
  · rw [mergeHiCopyATraced?, if_pos htail]
    dsimp only
    unfold TraceResult.bind
    rw [hshift.success]
    change Option.map _
      (tempToMainCellTraced? shifted
        (cursor.dest - Int.ofNat cursor.na) cursor.ssb).result = some result
    rw [hcell]
    rfl
  · rw [mergeHiCopyATraced?, if_pos htail]
    apply MovementTraceSafe.bind _ _ shifted hshift.success hshift.traceSafe
    exact MovementTraceSafe.map _ _ hcellSafe
  · change request ≤ state.alloced.toNat
    rw [hcellFrame.alloced, hshift.frame.alloced]
    exact hinvariant.requestFits

/-- Complete recursive driver contract.  The strict slack is consumed by one
real backward copy before each recursive call, while both terminal labels are
handled before phase dispatch. -/
private theorem mergeHiLoopTraced_safe
    (origin : MergeState κ ν) (request fuel : Nat)
    (cursor : MergeHiCursor κ ν)
    (hinvariant : MergeHiCursorInvariant origin request cursor)
    (hfuel : MergeHiFuelInvariant fuel cursor) :
    ∃ result, MergeHiCorePost origin request
      (mergeHiLoopTraced? fuel cursor) (mergeHiLoop? fuel cursor) result := by
  induction fuel generalizing cursor with
  | zero =>
      unfold MergeHiFuelInvariant at hfuel
      omega
  | succ fuel ih =>
      by_cases hterminal : cursor.na = 0 ∨ cursor.nb = 0
      · simpa [mergeHiLoopTraced?, mergeHiLoop?, hterminal] using
          mergeHiSucceedTraced_safe origin request cursor hinvariant
      · have hna : 0 < cursor.na := by omega
        have hnbPositive : 0 < cursor.nb := by omega
        by_cases hnbOne : cursor.nb = 1
        · have hnaZero : ¬ cursor.na = 0 := by omega
          simpa [mergeHiLoopTraced?, mergeHiLoop?, hterminal, hnbOne,
            hnaZero] using
            mergeHiCopyATraced_safe origin request cursor hinvariant
              ⟨hnbOne, hna⟩
        · have hnb : 1 < cursor.nb := by omega
          cases hphase : cursor.phase with
          | galloping aCount bCount =>
              simpa [mergeHiLoopTraced?, mergeHiLoop?, hterminal, hnbOne,
                hphase] using
                mergeHiGallopRoundTraced_safe origin request fuel cursor
                  hinvariant hfuel hna hnb (mergeHiLoopTraced? fuel)
                  (mergeHiLoop? fuel) ih
          | straight aCount bCount =>
              rcases hinvariant.tempReadable hnbPositive with
                ⟨right, hright⟩
              have hrightResult :
                  (TraceResult.tempPayloadRead? cursor.state.a
                    cursor.ssb).result = some right := by
                change (TraceResult.tempPayloadRead? cursor.state.a
                  cursor.ssb).erase = some right
                rw [erase_mergeTempRead]
                exact hright
              have hrightSafe := mergeHiTempReadTraced_safe cursor.state.a
                cursor.ssb (hinvariant.ssbInBounds hnbPositive)
                hinvariant.tempLive
              rcases SortSlice.read_eq_some_of_indexInBounds cursor.state.data
                  cursor.ssa (hinvariant.ssaInBounds hna) with
                ⟨left, hleft⟩
              have hleftResult :
                  (TraceResult.sortSliceKeysRead? cursor.state.data
                    cursor.ssa).result = some left := by
                change cursor.state.data.read? cursor.ssa = some left
                exact hleft
              have hleftSafe := mergeHiMainKeyReadTraced_safe
                cursor.state.data cursor.ssa (hinvariant.ssaInBounds hna)
              let tracedAfterLeft := fun (rightEntry entry : SortSliceEntry κ ν) =>
                if iflt cursor.state.key_compare rightEntry.key entry.key then
                  (mergeHiCopyDataDecrTraced? cursor.state cursor.dest
                    cursor.ssa).bind fun copied =>
                      let nextCount := aCount + 1
                      let next : MergeHiCursor κ ν :=
                        { cursor with
                          state := copied.state
                          dest := copied.dst
                          ssa := copied.src
                          na := cursor.na - 1
                          phase :=
                            if mergeHiCountAtLeast nextCount cursor.minGallop then
                              .galloping nextCount 0
                            else
                              .straight nextCount 0
                          minGallop :=
                            if mergeHiCountAtLeast nextCount cursor.minGallop then
                              cursor.minGallop + 1
                            else
                              cursor.minGallop }
                      mergeHiLoopTraced? fuel next
                else
                  (mergeHiCopyTempDecrTraced? cursor.state cursor.dest
                    cursor.ssb).bind fun copied =>
                      let nextCount := bCount + 1
                      let next : MergeHiCursor κ ν :=
                        { cursor with
                          state := copied.state
                          dest := copied.dst
                          ssb := copied.src
                          nb := cursor.nb - 1
                          phase :=
                            if mergeHiCountAtLeast nextCount cursor.minGallop then
                              .galloping 0 nextCount
                            else
                              .straight 0 nextCount
                          minGallop :=
                            if mergeHiCountAtLeast nextCount cursor.minGallop then
                              cursor.minGallop + 1
                            else
                              cursor.minGallop }
                      mergeHiLoopTraced? fuel next
              let referenceAfterLeft := fun
                  (rightEntry entry : SortSliceEntry κ ν) =>
                if iflt cursor.state.key_compare rightEntry.key entry.key then
                  (mergeHiCopyDataDecr? cursor.state cursor.dest
                    cursor.ssa).bind fun copied =>
                      let nextCount := aCount + 1
                      let next : MergeHiCursor κ ν :=
                        { cursor with
                          state := copied.state
                          dest := copied.dst
                          ssa := copied.src
                          na := cursor.na - 1
                          phase :=
                            if mergeHiCountAtLeast nextCount cursor.minGallop then
                              .galloping nextCount 0
                            else
                              .straight nextCount 0
                          minGallop :=
                            if mergeHiCountAtLeast nextCount cursor.minGallop then
                              cursor.minGallop + 1
                            else
                              cursor.minGallop }
                      mergeHiLoop? fuel next
                else
                  (mergeHiCopyTempDecr? cursor.state cursor.dest
                    cursor.ssb).bind fun copied =>
                      let nextCount := bCount + 1
                      let next : MergeHiCursor κ ν :=
                        { cursor with
                          state := copied.state
                          dest := copied.dst
                          ssb := copied.src
                          nb := cursor.nb - 1
                          phase :=
                            if mergeHiCountAtLeast nextCount cursor.minGallop then
                              .galloping 0 nextCount
                            else
                              .straight 0 nextCount
                          minGallop :=
                            if mergeHiCountAtLeast nextCount cursor.minGallop then
                              cursor.minGallop + 1
                            else
                              cursor.minGallop }
                      mergeHiLoop? fuel next
              have hselected : ∃ result, MergeHiCorePost origin request
                  (tracedAfterLeft right left)
                  (referenceAfterLeft right left) result := by
                by_cases hcompare :
                    cursor.state.key_compare right.key left.key = true
                · rcases mergeHiCopyDataDecrTraced_safe origin request cursor
                      hinvariant hna with
                    ⟨copied, hcopy, hcopySafe, hcopiedInv, _hdst, _hsrc⟩
                  let nextCount := aCount + 1
                  let next : MergeHiCursor κ ν :=
                    { cursor with
                      state := copied.state
                      dest := copied.dst
                      ssa := copied.src
                      na := cursor.na - 1
                      phase :=
                        if mergeHiCountAtLeast nextCount cursor.minGallop then
                          .galloping nextCount 0
                        else
                          .straight nextCount 0
                      minGallop :=
                        if mergeHiCountAtLeast nextCount cursor.minGallop then
                          cursor.minGallop + 1
                        else
                          cursor.minGallop }
                  have hnextInv : MergeHiCursorInvariant origin request next := by
                    by_cases hcross :
                        mergeHiCountAtLeast nextCount cursor.minGallop = true
                    · simpa [next, nextCount, hcross] using
                        hcopiedInv.setControl (cursor.minGallop + 1)
                          (.galloping nextCount 0)
                    · simpa [next, nextCount, hcross] using
                        hcopiedInv.setControl cursor.minGallop
                          (.straight nextCount 0)
                  have hnextFuel : MergeHiFuelInvariant fuel next := by
                    unfold MergeHiFuelInvariant at hfuel ⊢
                    simp only [next]
                    omega
                  rcases ih next hnextInv hnextFuel with ⟨result, htail⟩
                  have hcopyPost := MergeHiCorePost.prepend origin request
                    (mergeHiCopyDataDecrTraced? cursor.state cursor.dest
                      cursor.ssa)
                    (fun copied =>
                      let nextCount := aCount + 1
                      mergeHiLoopTraced? fuel
                        { cursor with
                          state := copied.state
                          dest := copied.dst
                          ssa := copied.src
                          na := cursor.na - 1
                          phase :=
                            if mergeHiCountAtLeast nextCount cursor.minGallop then
                              .galloping nextCount 0
                            else .straight nextCount 0
                          minGallop :=
                            if mergeHiCountAtLeast nextCount cursor.minGallop then
                              cursor.minGallop + 1
                            else cursor.minGallop })
                    (fun copied =>
                      let nextCount := aCount + 1
                      mergeHiLoop? fuel
                        { cursor with
                          state := copied.state
                          dest := copied.dst
                          ssa := copied.src
                          na := cursor.na - 1
                          phase :=
                            if mergeHiCountAtLeast nextCount cursor.minGallop then
                              .galloping nextCount 0
                            else .straight nextCount 0
                          minGallop :=
                            if mergeHiCountAtLeast nextCount cursor.minGallop then
                              cursor.minGallop + 1
                            else cursor.minGallop })
                    copied result hcopy hcopySafe (by
                      simpa [next, nextCount] using htail)
                  exact ⟨result, by
                    simpa [tracedAfterLeft, referenceAfterLeft, hcompare,
                      erase_mergeHiCopyDataDecrTraced] using hcopyPost⟩
                · rcases mergeHiCopyTempDecrTraced_safe origin request cursor
                      hinvariant hnbPositive with
                    ⟨copied, hcopy, hcopySafe, hcopiedInv, _hdst, _hsrc⟩
                  let nextCount := bCount + 1
                  let next : MergeHiCursor κ ν :=
                    { cursor with
                      state := copied.state
                      dest := copied.dst
                      ssb := copied.src
                      nb := cursor.nb - 1
                      phase :=
                        if mergeHiCountAtLeast nextCount cursor.minGallop then
                          .galloping 0 nextCount
                        else
                          .straight 0 nextCount
                      minGallop :=
                        if mergeHiCountAtLeast nextCount cursor.minGallop then
                          cursor.minGallop + 1
                        else
                          cursor.minGallop }
                  have hnextInv : MergeHiCursorInvariant origin request next := by
                    by_cases hcross :
                        mergeHiCountAtLeast nextCount cursor.minGallop = true
                    · simpa [next, nextCount, hcross] using
                        hcopiedInv.setControl (cursor.minGallop + 1)
                          (.galloping 0 nextCount)
                    · simpa [next, nextCount, hcross] using
                        hcopiedInv.setControl cursor.minGallop
                          (.straight 0 nextCount)
                  have hnextFuel : MergeHiFuelInvariant fuel next := by
                    unfold MergeHiFuelInvariant at hfuel ⊢
                    simp only [next]
                    omega
                  rcases ih next hnextInv hnextFuel with ⟨result, htail⟩
                  have hcopyPost := MergeHiCorePost.prepend origin request
                    (mergeHiCopyTempDecrTraced? cursor.state cursor.dest
                      cursor.ssb)
                    (fun copied =>
                      let nextCount := bCount + 1
                      mergeHiLoopTraced? fuel
                        { cursor with
                          state := copied.state
                          dest := copied.dst
                          ssb := copied.src
                          nb := cursor.nb - 1
                          phase :=
                            if mergeHiCountAtLeast nextCount cursor.minGallop then
                              .galloping 0 nextCount
                            else .straight 0 nextCount
                          minGallop :=
                            if mergeHiCountAtLeast nextCount cursor.minGallop then
                              cursor.minGallop + 1
                            else cursor.minGallop })
                    (fun copied =>
                      let nextCount := bCount + 1
                      mergeHiLoop? fuel
                        { cursor with
                          state := copied.state
                          dest := copied.dst
                          ssb := copied.src
                          nb := cursor.nb - 1
                          phase :=
                            if mergeHiCountAtLeast nextCount cursor.minGallop then
                              .galloping 0 nextCount
                            else .straight 0 nextCount
                          minGallop :=
                            if mergeHiCountAtLeast nextCount cursor.minGallop then
                              cursor.minGallop + 1
                            else cursor.minGallop })
                    copied result hcopy hcopySafe (by
                      simpa [next, nextCount] using htail)
                  exact ⟨result, by
                    simpa [tracedAfterLeft, referenceAfterLeft, hcompare,
                      erase_mergeHiCopyTempDecrTraced] using hcopyPost⟩
              rcases hselected with ⟨result, hselected⟩
              have hleftPost := MergeHiCorePost.prepend origin request
                (TraceResult.sortSliceKeysRead? cursor.state.data cursor.ssa)
                (tracedAfterLeft right) (referenceAfterLeft right) left result
                hleftResult
                hleftSafe hselected
              let tracedAfterRight := fun (entry : SortSliceEntry κ ν) =>
                (TraceResult.sortSliceKeysRead? cursor.state.data
                  cursor.ssa).bind (tracedAfterLeft entry)
              let referenceAfterRight := fun (entry : SortSliceEntry κ ν) =>
                cursor.state.data.read? cursor.ssa |>.bind
                  (referenceAfterLeft entry)
              have hleftPost' : MergeHiCorePost origin request
                  (tracedAfterRight right) (referenceAfterRight right) result := by
                simpa [tracedAfterRight, referenceAfterRight] using hleftPost
              have hrightPost := MergeHiCorePost.prepend origin request
                (TraceResult.tempPayloadRead? cursor.state.a cursor.ssb)
                tracedAfterRight referenceAfterRight right result hrightResult
                hrightSafe hleftPost'
              have hrightPost' : MergeHiCorePost origin request
                  ((TraceResult.tempPayloadRead? cursor.state.a
                    cursor.ssb).bind tracedAfterRight)
                  ((mergeTempRead? cursor.state.a cursor.ssb).bind
                    referenceAfterRight) result := by
                apply hrightPost.reference_eq
                rw [erase_mergeTempRead]
              exact ⟨result, by
                simpa [mergeHiLoopTraced?, mergeHiLoop?, hterminal, hnbOne,
                  hphase, tracedAfterRight, referenceAfterRight,
                  tracedAfterLeft, referenceAfterLeft,
                  mergeTempRead_eq_mergeHiTempRead]
                  using hrightPost'⟩

/-! ## Concrete trace-witness composition -/

private theorem mergeHiHasAccess_bind_left
    (current : TraceResult α) (next : α → TraceResult β)
    (kind : AccessKind) (region : AccessRegion)
    (hcurrent : current.trace.HasAccess kind region) :
    (current.bind next).trace.HasAccess kind region := by
  rw [TraceResult.trace_bind]
  cases current.result with
  | none => exact hcurrent
  | some value => exact hcurrent.compose_left

private theorem mergeHiHasAccess_bind_right
    (current : TraceResult α) (next : α → TraceResult β)
    (value : α) (kind : AccessKind) (region : AccessRegion)
    (hresult : current.result = some value)
    (hnext : (next value).trace.HasAccess kind region) :
    (current.bind next).trace.HasAccess kind region := by
  rw [TraceResult.trace_bind, hresult]
  exact hnext.compose_right

private theorem mergeHiHasTempAccess_bind_left
    (current : TraceResult α) (next : α → TraceResult β)
    (kind : AccessKind) (hcurrent : current.trace.HasTempAccess kind) :
    (current.bind next).trace.HasTempAccess kind := by
  rcases hcurrent with ⟨backing, hcurrent⟩
  exact ⟨backing, mergeHiHasAccess_bind_left current next kind
    (.tempPayload backing) hcurrent⟩

private theorem mergeHiHasTempAccess_bind_right
    (current : TraceResult α) (next : α → TraceResult β)
    (value : α) (kind : AccessKind)
    (hresult : current.result = some value)
    (hnext : (next value).trace.HasTempAccess kind) :
    (current.bind next).trace.HasTempAccess kind := by
  rcases hnext with ⟨backing, hnext⟩
  exact ⟨backing, mergeHiHasAccess_bind_right current next value kind
    (.tempPayload backing) hresult hnext⟩

private theorem mergeHiTempPayloadRead_hasTempAccess
    (storage : TempStorage κ ν) (index : Int) :
    (TraceResult.tempPayloadRead? storage index).trace.HasTempAccess .read := by
  refine ⟨storage.backing, ?_⟩
  refine ⟨AccessEvent.mk .read (.tempPayload storage.backing) index
    storage.cells.size, ?_, rfl, rfl⟩
  simp [TraceResult.trace_tempPayloadRead, AccessTrace.singletonAccess]

private theorem mergeHiTempToMainCell_hasTempRead
    (state : MergeState κ ν) (mainDst tempSrc : Int) :
    (tempToMainCellTraced? state mainDst tempSrc).trace.HasTempAccess .read := by
  have hkey : (tempToMainKeyTraced? state mainDst tempSrc).trace.HasTempAccess
      .read := by
    unfold tempToMainKeyTraced?
    exact mergeHiHasTempAccess_bind_left _ _ .read
      (mergeHiTempPayloadRead_hasTempAccess state.a tempSrc)
  unfold tempToMainCellTraced?
  exact mergeHiHasTempAccess_bind_left _ _ .read hkey

private theorem mergeHiSucceedTraced_hasTempRead
    (origin : MergeState κ ν) (request : Nat)
    (cursor : MergeHiCursor κ ν)
    (hinvariant : MergeHiCursorInvariant origin request cursor)
    (hnb : 0 < cursor.nb) :
    (mergeHiSucceedTraced? cursor).trace.HasTempAccess .read := by
  have hstart : cursor.dest - Int.ofNat (cursor.nb - 1) =
      cursor.basea + Int.ofNat cursor.na := by
    have hdest := hinvariant.destEquation
    simp only [Int.ofNat_eq_natCast, Nat.cast_add] at hdest ⊢
    omega
  have hmain : SortSlice.RangeInBounds cursor.state.data
      (cursor.dest - Int.ofNat (cursor.nb - 1)) cursor.nb := by
    rw [hstart]
    constructor
    · exact add_nonneg hinvariant.baseNonnegative (Int.natCast_nonneg _)
    · have hrange := hinvariant.mainRange
      simpa only [Int.ofNat_eq_natCast, Nat.cast_add, add_assoc] using hrange
  have htemp : TempRangeInBounds cursor.state.a 0 cursor.nb := by
    constructor
    · rfl
    · simpa [Int.ofNat_eq_natCast] using
        Int.ofNat_le.mpr hinvariant.tempCapacity
  rcases tempToMainMemcpyTraced_post (.hi .finalTempToData)
      mergeHiFinalTempToDataPermit cursor.nb cursor.state
      (cursor.dest - Int.ofNat (cursor.nb - 1)) 0 hmain htemp
      hinvariant.tempValuesMode hinvariant.tempInvariant hinvariant.tempLive
      hinvariant.valuesMode with ⟨_, hpost⟩
  rw [mergeHiSucceedTraced?, if_neg (Nat.ne_of_gt hnb)]
  exact hpost.tempReadEvent hnb

private theorem mergeHiCopyATraced_hasTempRead
    (origin : MergeState κ ν) (request : Nat)
    (cursor : MergeHiCursor κ ν)
    (hinvariant : MergeHiCursorInvariant origin request cursor)
    (htail : cursor.nb = 1 ∧ 0 < cursor.na) :
    (mergeHiCopyATraced? cursor).trace.HasTempAccess .read := by
  have hsrcEq : cursor.ssa + (1 - Int.ofNat cursor.na) = cursor.basea := by
    have heq := hinvariant.ssaEquation
    simp only [Int.ofNat_eq_natCast] at heq ⊢
    omega
  have hdstEq : cursor.dest + (1 - Int.ofNat cursor.na) =
      cursor.basea + 1 := by
    have heq := hinvariant.destEquation
    simp only [htail.1, Int.ofNat_eq_natCast, Nat.cast_add,
      Nat.cast_one] at heq ⊢
    omega
  have hsrc : SortSlice.RangeInBounds cursor.state.data
      (cursor.ssa + (1 - Int.ofNat cursor.na)) cursor.na := by
    rw [hsrcEq]
    constructor
    · exact hinvariant.baseNonnegative
    · have hrange := hinvariant.mainRange
      simp only [htail.1, Int.ofNat_eq_natCast, Nat.cast_add,
        Nat.cast_one] at hrange ⊢
      omega
  have hdst : SortSlice.RangeInBounds cursor.state.data
      (cursor.dest + (1 - Int.ofNat cursor.na)) cursor.na := by
    rw [hdstEq]
    constructor
    · exact add_nonneg hinvariant.baseNonnegative (by norm_num)
    · have hrange := hinvariant.mainRange
      simp only [htail.1, Int.ofNat_eq_natCast, Nat.cast_add,
        Nat.cast_one] at hrange ⊢
      omega
  rcases mainDataMemmoveTraced_safe cursor.state
      (cursor.dest + (1 - Int.ofNat cursor.na))
      (cursor.ssa + (1 - Int.ofNat cursor.na)) cursor.na
      hinvariant.tempInvariant hinvariant.tempLive hinvariant.valuesMode
      hdst hsrc with ⟨shifted, hshift⟩
  rw [mergeHiCopyATraced?, if_pos htail]
  exact mergeHiHasTempAccess_bind_right _ _ shifted .read hshift.success
    (mergeHiTempToMainCell_hasTempRead shifted
      (cursor.dest - Int.ofNat cursor.na) cursor.ssb)

private theorem mergeHiInitialLoop_hasTempRead
    (fuel : Nat) (cursor : MergeHiCursor κ ν)
    (hna : 0 < cursor.na) (hnb : 1 < cursor.nb)
    (hphase : cursor.phase = .straight 0 0) :
    (mergeHiLoopTraced? (fuel + 1) cursor).trace.HasTempAccess .read := by
  have hterminal : ¬ (cursor.na = 0 ∨ cursor.nb = 0) := by omega
  have hone : ¬ cursor.nb = 1 := by omega
  rw [mergeHiLoopTraced?, if_neg hterminal, if_neg hone, hphase]
  exact mergeHiHasTempAccess_bind_left _ _ .read
    (mergeHiTempPayloadRead_hasTempAccess cursor.state.a cursor.ssb)

/-- The allocation performed at the `merge_hi` entry.  Naming it once keeps
the allocation/copy stage and later entry-erasure stage definitionally in
sync. -/
def mergeHiAllocated (call : MergeAtCall κ ν) :
    MergeGetmemResult κ ν :=
  mergeGetmem call.state (BitVec.ofNat 64 call.nb)

/-- Full externally consumable postcondition for an actual `merge_at`
`merge_hi` continuation. -/
structure MergeHiSafetyPost
    (pre : MergeState κ ν) (scanned i : Nat) (call : MergeAtCall κ ν)
    (execution : TraceResult (MergeHiResult κ ν))
    (result : MergeHiResult κ ν) : Prop where
  resultEq : execution.result = some result
  returnCode : result.returnCode = 0
  resultFuel : result.fuelExhausted = false
  traceFuel : execution.trace.fuelExhausted = false
  accessesInBounds : execution.trace.allAccessesInBounds
  tempAccessesLive : execution.trace.tempPayloadAccessesLive
  noPushes : execution.trace.pushDepths = []
  noMemoryEvents : execution.trace.memoryEvents = []
  exactErasure : execution.erase =
    mergeHi? call.state call.ssa call.ssb call.na call.nb
  tempInvariant : TempStorageInv result.state.a result.state.alloced
  tempLive : result.state.a.Live
  logicalCapacity : result.state.a.cells.size = result.state.alloced.toNat
  requestFits : call.nb ≤ result.state.alloced.toNat
  valuesMode :
    SortSlice.ValuesModeInvariant result.state.a.hasValues result.state.data
  stableFrame : MergeHiStableFrame call.state result.state
  geometry : MergeAtSafetyGeometry pre scanned i call
  requestFacts : MergeGetmemRequestBoundFacts pre scanned i call.nb call
  inputTempInvariant : TempStorageInv call.state.a call.state.alloced
  inputTempLive : call.state.a.Live
  inputValuesMode :
    SortSlice.ValuesModeInvariant call.state.a.hasValues call.state.data
  directionalDispatch : call.nb < call.na
  /-- Exact allocation certificate for the `merge_getmem` result consumed by
  the directional merge. -/
  allocationPost : MergeGetmemStoragePost call.state
    (BitVec.ofNat 64 call.nb) (mergeHiAllocated call)
  /-- Exact temporary-storage metadata frame from post-`merge_getmem` through
  the final right-to-left merge state. -/
  postGetmemStorageFrame :
    MergeHiStorageFrame (mergeHiAllocated call).state result.state
  /-- Reuse transports a caller-supplied physical-slot bound, while growth
  establishes it from the allocation guard. -/
  physicalSlotsBound :
    call.state.a.physicalSlots ≤ PY_SSIZE_T_MAX / PY_OBJECT_PTR_BYTES →
      result.state.a.physicalSlots ≤ PY_SSIZE_T_MAX / PY_OBJECT_PTR_BYTES
  memcpyProvenance : MergeMemcpyCallsiteProvenanceContract κ ν
  inputKeyEvent : execution.trace.HasAccess .read .inputKeys
  tempWriteEvent : execution.trace.HasTempAccess .write
  tempReadEvent : execution.trace.HasTempAccess .read
  synchronizedValuesEvent : call.state.a.hasValues = true →
    execution.trace.HasAccess .read .synchronizedValues

/-! ## Staged proof of the public contract -/

/-- Cursor immediately before CPython's forced first copy from the left run. -/
def mergeHiFullCursor (call : MergeAtCall κ ν)
    (copied : MergeState κ ν) : MergeHiCursor κ ν :=
  { state := copied
    dest := call.ssb + Int.ofNat (call.nb - 1)
    ssa := call.ssa + Int.ofNat (call.na - 1)
    ssb := Int.ofNat (call.nb - 1)
    basea := call.ssa
    na := call.na
    nb := call.nb
    minGallop := copied.min_gallop
    phase := .straight 0 0 }

/-- Cursor passed to the recursive phase machine after the forced first copy. -/
def mergeHiInitialCursor (call : MergeAtCall κ ν)
    (forced : MergeHiDataCursorResult κ ν) : MergeHiCursor κ ν :=
  { state := forced.state
    dest := forced.dst
    ssa := forced.src
    ssb := Int.ofNat (call.nb - 1)
    basea := call.ssa
    na := call.na - 1
    nb := call.nb
    minGallop := forced.state.min_gallop
    phase := .straight 0 0 }

/-- Traced continuation following the forced first copy. -/
private def mergeHiTracedTail (call : MergeAtCall κ ν)
    (item : MergeHiDataCursorResult κ ν) : TraceResult (MergeHiResult κ ν) :=
  mergeHiLoopTraced? (call.na + call.nb) (mergeHiInitialCursor call item)

/-- Reviewed untraced continuation corresponding to `mergeHiTracedTail`. -/
private def mergeHiReferenceTail (call : MergeAtCall κ ν)
    (item : MergeHiDataCursorResult κ ν) : Option (MergeHiResult κ ν) :=
  mergeHiLoop? (call.na + call.nb) (mergeHiInitialCursor call item)

/-- Traced entry continuation following the initial main-to-temporary copy. -/
private def mergeHiTracedAfterCopy (call : MergeAtCall κ ν)
    (state : MergeState κ ν) : TraceResult (MergeHiResult κ ν) :=
  (mergeHiCopyDataDecrTraced? state
    (call.ssb + Int.ofNat (call.nb - 1))
    (call.ssa + Int.ofNat (call.na - 1))).bind (mergeHiTracedTail call)

/-- Untraced entry continuation corresponding to `mergeHiTracedAfterCopy`. -/
private def mergeHiReferenceAfterCopy (call : MergeAtCall κ ν)
    (state : MergeState κ ν) : Option (MergeHiResult κ ν) :=
  (mergeHiCopyDataDecr? state
    (call.ssb + Int.ofNat (call.nb - 1))
    (call.ssa + Int.ofNat (call.na - 1))).bind (mergeHiReferenceTail call)

/-- Evidence produced by the call-site/allocation stage.  It fixes the exact
initial `memcpy`, the forced first backward copy, and the cursor invariant that
the recursive phase machine consumes. -/
structure MergeHiPrepared
    (pre : MergeState κ ν) (scanned i : Nat) (call : MergeAtCall κ ν)
    (copied : MergeState κ ν) (forced : MergeHiDataCursorResult κ ν) : Prop where
  requestFacts : MergeGetmemRequestBoundFacts pre scanned i call.nb call
  geometry : MergeAtSafetyGeometry pre scanned i call
  inputTempInvariant : TempStorageInv call.state.a call.state.alloced
  inputTempLive : call.state.a.Live
  inputValuesMode :
    SortSlice.ValuesModeInvariant call.state.a.hasValues call.state.data
  directionalDispatch : call.nb < call.na
  allocation : MergeGetmemStoragePost call.state
    (BitVec.ofNat 64 call.nb) (mergeHiAllocated call)
  initialCopy : MainToTempMemcpyPost (.hi .initialDataToTemp)
    mergeHiInitialDataToTempPermit call.nb (mergeHiAllocated call).state copied
    0 call.ssb
  forcedResult :
    (mergeHiCopyDataDecrTraced? copied
      (call.ssb + Int.ofNat (call.nb - 1))
      (call.ssa + Int.ofNat (call.na - 1))).result = some forced
  forcedSafe : MovementTraceSafe
    (mergeHiCopyDataDecrTraced? copied
      (call.ssb + Int.ofNat (call.nb - 1))
      (call.ssa + Int.ofNat (call.na - 1)))
  initialInvariant : MergeHiCursorInvariant (mergeHiAllocated call).state call.nb
    (mergeHiInitialCursor call forced)
  initialFuel : MergeHiFuelInvariant (call.na + call.nb)
    (mergeHiInitialCursor call forced)

/-- The allocation and initial-copy stage derives every cursor premise from
the actual `prepareMergeAt?` branch, rather than asking the loop proof to
reconstruct call-site geometry. -/
theorem mergeHi_prepare
    (pre : MergeState κ ν) (scanned i : Nat) (call : MergeAtCall κ ν)
    (hlayout : PendingLayout pre scanned)
    (hmax : pre.listlen.toNat ≤ PY_LIST_MAX)
    (hprepare : prepareMergeAt? pre i = some (.mergeHi call))
    (hInv : TempStorageInv pre.a pre.alloced)
    (hLive : pre.a.Live)
    (hMode : SortSlice.ValuesModeInvariant pre.a.hasValues pre.data) :
    ∃ copied forced, MergeHiPrepared pre scanned i call copied forced := by
  have hrequest := mergeGetmem_hi_request_bound pre scanned i call hlayout hmax
    hprepare
  have hgeometry := mergeHi_callsite_safety_geometry pre scanned i call hlayout
    hmax hprepare
  have hdispatch := (prepareMergeAt_hi_callsite_of_eq_some pre i call hprepare).2
  have hevidence := hgeometry.evidence
  have hcallInv : TempStorageInv call.state.a call.state.alloced := by
    simpa only [hevidence.storage_eq, hevidence.alloced_eq] using hInv
  have hcallLive : call.state.a.Live := by
    simpa only [hevidence.storage_eq] using hLive
  have hcallMode :
      SortSlice.ValuesModeInvariant call.state.a.hasValues call.state.data := by
    simpa only [hevidence.hasValues_eq, hevidence.data_eq] using hMode
  have hallocPost : MergeGetmemStoragePost call.state
      (BitVec.ofNat 64 call.nb) (mergeHiAllocated call) := by
    exact mergeGetmem_storage_valid call.state (BitVec.ofNat 64 call.nb)
      hcallInv hcallLive hrequest.requestNonnegative
      (fun _ => hrequest.requestWithinLimit)
  have hallocatedMode :
      SortSlice.ValuesModeInvariant (mergeHiAllocated call).state.a.hasValues
        (mergeHiAllocated call).state.data := by
    simpa only [hallocPost.valuesMode, hallocPost.data_eq] using hcallMode
  have htempRange : TempRangeInBounds (mergeHiAllocated call).state.a 0
      call.nb := by
    constructor
    · omega
    · simp only [zero_add]
      apply Int.ofNat_le.mpr
      rw [hallocPost.logicalCapacity]
      simpa only [hrequest.requestRoundtrip] using hallocPost.requestFits
  have hmainRange : SortSlice.RangeInBounds
      (mergeHiAllocated call).state.data call.ssb call.nb := by
    constructor
    · exact hgeometry.ssbNonnegative
    · rw [hallocPost.data_eq]
      exact hgeometry.rightRange
  rcases mainToTempMemcpyTraced_post (.hi .initialDataToTemp)
      mergeHiInitialDataToTempPermit call.nb (mergeHiAllocated call).state 0
      call.ssb htempRange hmainRange hallocPost.invariant hallocPost.live
      hallocatedMode with ⟨copied, hcopy⟩
  have hfull : MergeHiCursorInvariant (mergeHiAllocated call).state call.nb
      (mergeHiFullCursor call copied) := by
    refine
      { baseNonnegative := hgeometry.ssaNonnegative
        ssaEquation := ?_
        ssbEquation := ?_
        destEquation := ?_
        mainRange := ?_
        leftWordBound := ?_
        rightWordBound := ?_
        tempCapacity := ?_
        tempValuesMode := ?_
        tempInvariant := hcopy.tempInvariant
        tempLive := hcopy.tempLive
        requestFits := ?_
        valuesMode := hcopy.valuesMode
        stableFrame := MergeHiStableFrame.of_movement hcopy.frame
        storageFrame := MergeHiStorageFrame.of_movement hcopy.frame }
    · change call.ssa + Int.ofNat (call.na - 1) + 1 =
        call.ssa + Int.ofNat call.na
      simp only [Int.ofNat_eq_natCast, Nat.cast_sub hgeometry.leftPositive]
      omega
    · change Int.ofNat (call.nb - 1) + 1 = Int.ofNat call.nb
      simp only [Int.ofNat_eq_natCast, Nat.cast_sub hgeometry.rightPositive]
      omega
    · change call.ssb + Int.ofNat (call.nb - 1) + 1 =
        call.ssa + Int.ofNat (call.na + call.nb)
      have hadjacent := hgeometry.adjacent
      simp only [Int.ofNat_eq_natCast, Nat.cast_add,
        Nat.cast_sub hgeometry.rightPositive] at hadjacent ⊢
      omega
    · change call.ssa + Int.ofNat (call.na + call.nb) ≤
        Int.ofNat copied.data.entries.size
      rw [hcopy.frame.dataSize, hallocPost.data_eq]
      exact hgeometry.mergedRange
    · change call.na ≤ PY_LIST_MAX
      have hrun := hgeometry.runLengthBound
      omega
    · change call.nb ≤ PY_LIST_MAX
      have hrun := hgeometry.runLengthBound
      omega
    · change call.nb ≤ copied.a.cells.size
      rw [hcopy.frame.tempSize, hallocPost.logicalCapacity]
      simpa only [hrequest.requestRoundtrip] using hallocPost.requestFits
    · simpa [mergeHiFullCursor] using hcopy.tempValuesMode
    · change call.nb ≤ copied.alloced.toNat
      rw [hcopy.frame.alloced]
      simpa only [hrequest.requestRoundtrip] using hallocPost.requestFits
  rcases mergeHiCopyDataDecrTraced_safe (mergeHiAllocated call).state call.nb
      (mergeHiFullCursor call copied) hfull hgeometry.leftPositive with
    ⟨forced, hforced, hforcedSafe, hforcedInv, _hdst, _hsrc⟩
  have hinitial : MergeHiCursorInvariant (mergeHiAllocated call).state call.nb
      (mergeHiInitialCursor call forced) := by
    simpa [mergeHiInitialCursor, mergeHiFullCursor] using
      hforcedInv.setControl forced.state.min_gallop (.straight 0 0)
  have hinitialFuel : MergeHiFuelInvariant (call.na + call.nb)
      (mergeHiInitialCursor call forced) := by
    unfold MergeHiFuelInvariant
    simp only [mergeHiInitialCursor]
    have hna := hgeometry.leftPositive
    omega
  refine ⟨copied, forced,
    { requestFacts := hrequest
      geometry := hgeometry
      inputTempInvariant := hcallInv
      inputTempLive := hcallLive
      inputValuesMode := hcallMode
      directionalDispatch := hdispatch
      allocation := hallocPost
      initialCopy := hcopy
      forcedResult := ?_
      forcedSafe := ?_
      initialInvariant := hinitial
      initialFuel := hinitialFuel }⟩
  · simpa [mergeHiFullCursor] using hforced
  · simpa [mergeHiFullCursor] using hforcedSafe

/-- Lockstep result after the recursive merge driver has finished.  Besides
the aggregate core contract, this stage retains the exact traced entry shape
and the non-vacuous temporary-read witness needed by the observable post. -/
private structure MergeHiLockstepPost
    (call : MergeAtCall κ ν) (copied : MergeState κ ν)
    (result : MergeHiResult κ ν) : Prop where
  core : MergeHiCorePost (mergeHiAllocated call).state call.nb
    (mergeHiTraced? call.state call.ssa call.ssb call.na call.nb)
    (mergeHi? call.state call.ssa call.ssb call.na call.nb) result
  tracedEntry :
    mergeHiTraced? call.state call.ssa call.ssb call.na call.nb =
      (mainToTempMemcpyTraced? (.hi .initialDataToTemp)
        mergeHiInitialDataToTempPermit call.nb
        (mergeHiAllocated call).state 0 call.ssb).bind
          (mergeHiTracedAfterCopy call)
  afterCopyRead :
    (mergeHiTracedAfterCopy call copied).trace.HasTempAccess .read

/-- The loop/lockstep stage consumes only the prepared cursor contract.  It
proves termination, exact erasure against the untraced transcription, and a
real temporary read on every successful path. -/
private theorem mergeHi_lockstep
    (pre : MergeState κ ν) (scanned i : Nat) (call : MergeAtCall κ ν)
    (copied : MergeState κ ν) (forced : MergeHiDataCursorResult κ ν)
    (hprepared : MergeHiPrepared pre scanned i call copied forced) :
    ∃ result, MergeHiLockstepPost call copied result := by
  have hgeometry := hprepared.geometry
  have hallocPost := hprepared.allocation
  have hcopy := hprepared.initialCopy
  have hinitial := hprepared.initialInvariant
  rcases mergeHiLoopTraced_safe (mergeHiAllocated call).state call.nb
      (call.na + call.nb)
      (mergeHiInitialCursor call forced) hinitial hprepared.initialFuel with
    ⟨result, hloop⟩
  have hsumPositive : 0 < call.na + call.nb := by
    have hna := hgeometry.leftPositive
    omega
  let loopFuel := call.na + call.nb - 1
  have hloopFuelEq : call.na + call.nb = loopFuel + 1 := by
    dsimp [loopFuel]
    omega
  have hloopRead :
      (mergeHiLoopTraced? (call.na + call.nb)
        (mergeHiInitialCursor call forced)).trace.HasTempAccess .read := by
    by_cases hnaZero : (mergeHiInitialCursor call forced).na = 0
    · have hnbPositive : 0 < (mergeHiInitialCursor call forced).nb := by
        simpa [mergeHiInitialCursor] using hgeometry.rightPositive
      rw [hloopFuelEq]
      simpa [mergeHiLoopTraced?, hnaZero] using
        mergeHiSucceedTraced_hasTempRead (mergeHiAllocated call).state call.nb
          (mergeHiInitialCursor call forced) hinitial hnbPositive
    · have hnaPositive : 0 < (mergeHiInitialCursor call forced).na :=
        Nat.pos_of_ne_zero hnaZero
      by_cases hnbOne : (mergeHiInitialCursor call forced).nb = 1
      · have hterminal : ¬ ((mergeHiInitialCursor call forced).na = 0 ∨
            (mergeHiInitialCursor call forced).nb = 0) := by
          omega
        rw [hloopFuelEq, mergeHiLoopTraced?, if_neg hterminal,
          if_pos hnbOne]
        exact mergeHiCopyATraced_hasTempRead (mergeHiAllocated call).state call.nb
          (mergeHiInitialCursor call forced) hinitial ⟨hnbOne, hnaPositive⟩
      · have hnbLarge : 1 < (mergeHiInitialCursor call forced).nb := by
          have hnbPositive : 0 < (mergeHiInitialCursor call forced).nb := by
            simpa [mergeHiInitialCursor] using hgeometry.rightPositive
          omega
        rw [hloopFuelEq]
        exact mergeHiInitialLoop_hasTempRead loopFuel
          (mergeHiInitialCursor call forced) hnaPositive hnbLarge (by rfl)
  have hloop' : MergeHiCorePost (mergeHiAllocated call).state call.nb
      (mergeHiTracedTail call forced) (mergeHiReferenceTail call forced)
      result := by
    simpa [mergeHiTracedTail, mergeHiReferenceTail] using hloop
  have hafterForced := MergeHiCorePost.prepend
    (mergeHiAllocated call).state call.nb
    (mergeHiCopyDataDecrTraced? copied
      (call.ssb + Int.ofNat (call.nb - 1))
      (call.ssa + Int.ofNat (call.na - 1)))
    (mergeHiTracedTail call) (mergeHiReferenceTail call) forced result
    hprepared.forcedResult hprepared.forcedSafe hloop'
  have hafterCopy : MergeHiCorePost (mergeHiAllocated call).state call.nb
      (mergeHiTracedAfterCopy call copied)
      (mergeHiReferenceAfterCopy call copied) result := by
    simpa [mergeHiTracedAfterCopy, mergeHiReferenceAfterCopy,
      erase_mergeHiCopyDataDecrTraced] using hafterForced
  have hafterCopyRead :
      (mergeHiTracedAfterCopy call copied).trace.HasTempAccess .read := by
    apply mergeHiHasTempAccess_bind_right
      (mergeHiCopyDataDecrTraced? copied
        (call.ssb + Int.ofNat (call.nb - 1))
        (call.ssa + Int.ofNat (call.na - 1)))
      (mergeHiTracedTail call) forced .read hprepared.forcedResult
    simpa [mergeHiTracedTail] using hloopRead
  have hwhole := MergeHiCorePost.prepend (mergeHiAllocated call).state call.nb
    (mainToTempMemcpyTraced? (.hi .initialDataToTemp)
      mergeHiInitialDataToTempPermit call.nb
      (mergeHiAllocated call).state 0 call.ssb)
    (mergeHiTracedAfterCopy call) (mergeHiReferenceAfterCopy call) copied
    result hcopy.success hcopy.traceSafe hafterCopy
  have hreference :
      (mainToTempMemcpyTraced? (.hi .initialDataToTemp)
          mergeHiInitialDataToTempPermit call.nb
          (mergeHiAllocated call).state 0 call.ssb).erase.bind
            (mergeHiReferenceAfterCopy call) =
        (mergeHiMemcpyDataToTemp? .initialDataToTemp rfl call.nb
          (mergeHiAllocated call).state 0 call.ssb).bind
            (mergeHiReferenceAfterCopy call) := by
    calc
      _ = (mainToTempMemcpy? call.nb (mergeHiAllocated call).state 0
          call.ssb).bind (mergeHiReferenceAfterCopy call) := congrArg
            (fun option => option.bind (mergeHiReferenceAfterCopy call))
            hcopy.exactErasure
      _ = _ := congrArg
        (fun option => option.bind (mergeHiReferenceAfterCopy call))
        (mainToTempMemcpy_eq_mergeHiMemcpyDataToTemp .initialDataToTemp rfl
          call.nb (mergeHiAllocated call).state 0 call.ssb)
  have hwholeTagged := MergeHiCorePost.reference_eq hwhole hreference
  have hentryGuard :
      0 < call.na ∧ 0 < call.nb ∧ call.na ≤ PY_SSIZE_T_MAX ∧
        call.nb ≤ PY_SSIZE_T_MAX ∧
        call.ssa + Int.ofNat call.na = call.ssb :=
    ⟨hgeometry.leftPositive, hgeometry.rightPositive,
      hgeometry.leftWordBound, hgeometry.rightWordBound, hgeometry.adjacent⟩
  have htracedEntry :
      mergeHiTraced? call.state call.ssa call.ssb call.na call.nb =
        (mainToTempMemcpyTraced? (.hi .initialDataToTemp)
          mergeHiInitialDataToTempPermit call.nb
          (mergeHiAllocated call).state 0 call.ssb).bind
            (mergeHiTracedAfterCopy call) := by
    rw [mergeHiTraced?, if_pos hentryGuard]
    change (match (mergeHiAllocated call).outcome with
      | .guardRejected => _
      | .reused => _
      | .grown => _) = _
    rcases hallocPost.outcome with houtcome | houtcome
    · rw [houtcome]
      rfl
    · rw [houtcome]
      rfl
  have hreferenceEntry :
      mergeHi? call.state call.ssa call.ssb call.na call.nb =
        (mergeHiMemcpyDataToTemp? .initialDataToTemp rfl call.nb
          (mergeHiAllocated call).state 0 call.ssb).bind
            (mergeHiReferenceAfterCopy call) := by
    rw [mergeHi?, if_pos hentryGuard]
    change (match (mergeHiAllocated call).outcome with
      | .guardRejected => _
      | .reused => _
      | .grown => _) = _
    rcases hallocPost.outcome with houtcome | houtcome
    · rw [houtcome]
      rfl
    · rw [houtcome]
      rfl
  have hcore : MergeHiCorePost (mergeHiAllocated call).state call.nb
      (mergeHiTraced? call.state call.ssa call.ssb call.na call.nb)
      (mergeHi? call.state call.ssa call.ssb call.na call.nb) result := by
    rw [htracedEntry, hreferenceEntry]
    exact hwholeTagged
  exact ⟨result,
    { core := hcore
      tracedEntry := htracedEntry
      afterCopyRead := hafterCopyRead }⟩

/-- Observable evidence separated from the recursive lockstep proof.  These
witnesses rule out a vacuous safety result: the successful merge really reads
the input, writes and later reads temporary storage, and preserves the
classified-`memcpy` provenance boundary. -/
private structure MergeHiObservablePost
    (call : MergeAtCall κ ν) (result : MergeHiResult κ ν) : Prop where
  core : MergeHiCorePost (mergeHiAllocated call).state call.nb
    (mergeHiTraced? call.state call.ssa call.ssb call.na call.nb)
    (mergeHi? call.state call.ssa call.ssb call.na call.nb) result
  memcpyProvenance : MergeMemcpyCallsiteProvenanceContract κ ν
  inputKeyEvent :
    (mergeHiTraced? call.state call.ssa call.ssb call.na
      call.nb).trace.HasAccess .read .inputKeys
  tempWriteEvent :
    (mergeHiTraced? call.state call.ssa call.ssb call.na
      call.nb).trace.HasTempAccess .write
  tempReadEvent :
    (mergeHiTraced? call.state call.ssa call.ssb call.na
      call.nb).trace.HasTempAccess .read
  synchronizedValuesEvent : call.state.a.hasValues = true →
    (mergeHiTraced? call.state call.ssa call.ssb call.na
      call.nb).trace.HasAccess .read .synchronizedValues

/-- Final trace-witness stage.  It prefixes the concrete initial-copy events
through the exact entry equation exported by `mergeHi_lockstep`. -/
private theorem mergeHi_observables
    (pre : MergeState κ ν) (scanned i : Nat) (call : MergeAtCall κ ν)
    (copied : MergeState κ ν) (forced : MergeHiDataCursorResult κ ν)
    (result : MergeHiResult κ ν)
    (hprepared : MergeHiPrepared pre scanned i call copied forced)
    (hlockstep : MergeHiLockstepPost call copied result) :
    MergeHiObservablePost call result := by
  have hcopy := hprepared.initialCopy
  have hgeometry := hprepared.geometry
  have hinputEvent :
      (mergeHiTraced? call.state call.ssa call.ssb call.na
        call.nb).trace.HasAccess .read .inputKeys := by
    have hprefixed := mergeHiHasAccess_bind_left
      (mainToTempMemcpyTraced? (.hi .initialDataToTemp)
        mergeHiInitialDataToTempPermit call.nb
        (mergeHiAllocated call).state 0 call.ssb)
      (mergeHiTracedAfterCopy call) .read .inputKeys
      (hcopy.inputKeyEvent hgeometry.rightPositive)
    rw [hlockstep.tracedEntry]
    exact hprefixed
  have htempWriteEvent :
      (mergeHiTraced? call.state call.ssa call.ssb call.na
        call.nb).trace.HasTempAccess .write := by
    have hprefixed := mergeHiHasTempAccess_bind_left
      (mainToTempMemcpyTraced? (.hi .initialDataToTemp)
        mergeHiInitialDataToTempPermit call.nb
        (mergeHiAllocated call).state 0 call.ssb)
      (mergeHiTracedAfterCopy call) .write
      (hcopy.tempWriteEvent hgeometry.rightPositive)
    rw [hlockstep.tracedEntry]
    exact hprefixed
  have htempReadEvent :
      (mergeHiTraced? call.state call.ssa call.ssb call.na
        call.nb).trace.HasTempAccess .read := by
    have hprefixed := mergeHiHasTempAccess_bind_right
      (mainToTempMemcpyTraced? (.hi .initialDataToTemp)
        mergeHiInitialDataToTempPermit call.nb
        (mergeHiAllocated call).state 0 call.ssb)
      (mergeHiTracedAfterCopy call) copied .read hcopy.success
      hlockstep.afterCopyRead
    rw [hlockstep.tracedEntry]
    exact hprefixed
  refine
    { core := hlockstep.core
      memcpyProvenance := hcopy.provenanceContract
      inputKeyEvent := hinputEvent
      tempWriteEvent := htempWriteEvent
      tempReadEvent := htempReadEvent
      synchronizedValuesEvent := ?_ }
  intro hvalues
  have hallocatedValues : (mergeHiAllocated call).state.a.hasValues = true :=
    hprepared.allocation.valuesMode.trans hvalues
  have hprefixed := mergeHiHasAccess_bind_left
    (mainToTempMemcpyTraced? (.hi .initialDataToTemp)
      mergeHiInitialDataToTempPermit call.nb
      (mergeHiAllocated call).state 0 call.ssb)
    (mergeHiTracedAfterCopy call) .read .synchronizedValues
    (hcopy.synchronizedValuesEvent hgeometry.rightPositive hallocatedValues)
  rw [hlockstep.tracedEntry]
  exact hprefixed

/-- Safety of the concrete `merge_hi` continuation selected by `merge_at`.
All cursor geometry, allocation admissibility, positivity, word bounds, and
backward-sentinel arithmetic are derived from the pending layout and the
actual preparation equation. -/
theorem mergeHi_safe
    (pre : MergeState κ ν) (scanned i : Nat) (call : MergeAtCall κ ν)
    (hlayout : PendingLayout pre scanned)
    (hmax : pre.listlen.toNat ≤ PY_LIST_MAX)
    (hprepare : prepareMergeAt? pre i = some (.mergeHi call))
    (hInv : TempStorageInv pre.a pre.alloced)
    (hLive : pre.a.Live)
    (hMode : SortSlice.ValuesModeInvariant pre.a.hasValues pre.data) :
    ∃ result, MergeHiSafetyPost pre scanned i call
      (mergeHiTraced? call.state call.ssa call.ssb call.na call.nb) result := by
  rcases mergeHi_prepare pre scanned i call hlayout hmax hprepare hInv hLive
      hMode with ⟨copied, forced, hprepared⟩
  rcases mergeHi_lockstep pre scanned i call copied forced hprepared with
    ⟨result, hlockstep⟩
  have hobservable := mergeHi_observables pre scanned i call copied forced
    result hprepared hlockstep
  have hcore := hobservable.core
  have hlogical := TempStorageInv.cells_size_eq hcore.tempInvariant
    hcore.tempLive
  have hphysicalBound :
      call.state.a.physicalSlots ≤ PY_SSIZE_T_MAX / PY_OBJECT_PTR_BYTES →
        result.state.a.physicalSlots ≤
          PY_SSIZE_T_MAX / PY_OBJECT_PTR_BYTES := by
    intro hbefore
    rw [hcore.storageFrame.physicalSlots_eq]
    rcases hprepared.allocation.outcome with hreuse | hgrown
    · rw [hprepared.allocation.reuseAccounting hreuse]
      exact hbefore
    · exact (hprepared.allocation.growthAccounting hgrown).2.2.2.2
  exact ⟨result,
    { resultEq := hcore.resultEq
      returnCode := hcore.returnCode
      resultFuel := hcore.resultFuel
      traceFuel := hcore.traceSafe.fuel
      accessesInBounds := hcore.traceSafe.bounds
      tempAccessesLive := hcore.traceSafe.tempLive
      noPushes := hcore.traceSafe.noPushes
      noMemoryEvents := mergeHiTraced_memoryEvents_empty
        call.state call.ssa call.ssb call.na call.nb
      exactErasure := hcore.exactErasure
      tempInvariant := hcore.tempInvariant
      tempLive := hcore.tempLive
      logicalCapacity := hlogical
      requestFits := hcore.requestFits
      valuesMode := hcore.valuesMode
      stableFrame := (MergeHiStableFrame.of_getmem call.state
        (BitVec.ofNat 64 call.nb) hprepared.allocation).trans hcore.stableFrame
      geometry := hprepared.geometry
      requestFacts := hprepared.requestFacts
      inputTempInvariant := hprepared.inputTempInvariant
      inputTempLive := hprepared.inputTempLive
      inputValuesMode := hprepared.inputValuesMode
      directionalDispatch := hprepared.directionalDispatch
      allocationPost := hprepared.allocation
      postGetmemStorageFrame := hcore.storageFrame
      physicalSlotsBound := hphysicalBound
      memcpyProvenance := hobservable.memcpyProvenance
      inputKeyEvent := hobservable.inputKeyEvent
      tempWriteEvent := hobservable.tempWriteEvent
      tempReadEvent := hobservable.tempReadEvent
      synchronizedValuesEvent := hobservable.synchronizedValuesEvent }⟩
end CPythonListsort
