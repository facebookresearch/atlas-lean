/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Code.Assembly.MergeGetmemRequestBound
import Code.Assembly.MergeGetmemStorageValid
import Code.Assembly.MergeMemcpyProvenance
import Code.Assembly.MergeLoSafety
import Code.Assembly.MergeHiSafety

/-!
# Semantic validation for the real merge-memory trace

`AccessTrace` deliberately stores raw, type-erased observations.  This module
states the propositions those observations must satisfy.  None of the
predicates below changes the evaluator or manufactures a reachability
relation: later assembly theorems apply them to the literal `memoryEvents`
field returned by `listSortImplTraced?`.
-/

namespace CPythonListsort

universe u v

namespace MergeMemorySnapshot

/-- The one-or-two-pointer multiplier represented by a raw snapshot. -/
def multiplier (snapshot : MergeMemorySnapshot) : Nat :=
  if snapshot.hasValues then 2 else 1

/-- Snapshot form of the signed-allocation guard limit. -/
def allocationLimit (snapshot : MergeMemorySnapshot) : Nat :=
  PY_SSIZE_T_MAX / PY_OBJECT_PTR_BYTES / snapshot.multiplier

/-- Literal snapshot form of `TempStorageInv`.  The released case
deliberately leaves `alloced` and `hasValues` stale. -/
def StorageInv (snapshot : MergeMemorySnapshot) : Prop :=
  snapshot.physicalSlots = snapshot.multiplier * snapshot.cellsSize ∧
    match snapshot.backing with
    | .inline =>
        snapshot.cellsSize = snapshot.alloced.toNat ∧
          snapshot.multiplier * snapshot.alloced.toNat ≤
            MERGESTATE_TEMP_SIZE
    | .heap => snapshot.cellsSize = snapshot.alloced.toNat
    | .released => snapshot.cellsSize = 0

/-- Snapshot backing is available for payload access. -/
def Live (snapshot : MergeMemorySnapshot) : Prop :=
  snapshot.backing ≠ .released

/-- Every main-array entry agrees with the retained values-pointer mode.
The separate Boolean equation is intentional: on an empty main array the
entrywise clause alone cannot determine the mode. -/
def ValuesMode (mode : Bool) (snapshot : MergeMemorySnapshot) : Prop :=
  snapshot.hasValues = mode ∧
    ∀ (i : Nat) (hi : i < snapshot.mainValuePresent.length),
      snapshot.mainValuePresent[i] = mode

/-- The active representation facts, excluding the selected-platform heap
upper bound.  That bound is a reachability fact threaded separately from the
inline initializer through each real allocation transition. -/
def ActiveCore (mode : Bool) (snapshot : MergeMemorySnapshot) : Prop :=
  snapshot.StorageInv ∧ snapshot.Live ∧
    snapshot.cellsSize = snapshot.alloced.toNat ∧
    snapshot.ValuesMode mode

/-- The selected-platform physical allocation ceiling. -/
def PhysicalBound (snapshot : MergeMemorySnapshot) : Prop :=
  snapshot.physicalSlots ≤ PY_SSIZE_T_MAX / PY_OBJECT_PTR_BYTES

/-- Raw snapshots cannot validate while lying about their duplicated physical
slot count.  This projection is intentionally independent of backing kind. -/
theorem StorageInv.physicalSlots_eq {snapshot : MergeMemorySnapshot}
    (hInv : snapshot.StorageInv) :
    snapshot.physicalSlots = snapshot.multiplier * snapshot.cellsSize :=
  hInv.1

/-- Anti-phantom regression: changing the duplicated physical-slot count
without changing the raw backing extent is observably rejected. -/
theorem storageInv_rejects_phantomPhysicalSlots
    (snapshot : MergeMemorySnapshot)
    (hWrong : snapshot.physicalSlots ≠
      snapshot.multiplier * snapshot.cellsSize) :
    ¬ snapshot.StorageInv := by
  intro hInv
  exact hWrong hInv.physicalSlots_eq

@[simp]
theorem allocationLimit_ofState (state : MergeState κ ν) :
    (ofState state).allocationLimit = mergeGetmemAllocationLimit state.a := by
  rfl

@[simp]
theorem storageInv_ofState_iff (state : MergeState κ ν) :
    (ofState state).StorageInv ↔ TempStorageInv state.a state.alloced := by
  cases hbacking : state.a.backing <;>
    simp [StorageInv, ofState, TempStorageInv, hbacking,
      multiplier, TempStorage.multiplier, TempStorage.physicalSlots,
      Array.isEmpty_iff]
  all_goals aesop

@[simp]
theorem live_ofState_iff (state : MergeState κ ν) :
    (ofState state).Live ↔ state.a.Live := by
  simp [Live, ofState, TempStorage.Live]

@[simp]
theorem physicalBound_ofState_iff (state : MergeState κ ν) :
    (ofState state).PhysicalBound ↔
      state.a.physicalSlots ≤ PY_SSIZE_T_MAX / PY_OBJECT_PTR_BYTES := by
  rfl

private theorem value_isSome_eq_mode_iff
    (mode : Bool) (entry : SortSliceEntry κ ν) :
    entry.value.isSome = mode ↔
      SortSlice.EntryMatchesValuesMode mode entry := by
  cases mode <;> cases hvalue : entry.value <;>
    simp [SortSlice.EntryMatchesValuesMode, hvalue]

/-- The raw per-entry presence bits are exactly the existing global
values-mode invariant. -/
theorem valuesMode_ofState_iff (mode : Bool) (state : MergeState κ ν) :
    (ofState state).ValuesMode mode ↔
      state.a.hasValues = mode ∧
        SortSlice.ValuesModeInvariant mode state.data := by
  constructor
  · intro hsnapshot
    refine ⟨hsnapshot.1, ?_⟩
    intro i hi
    have hpresence := hsnapshot.2 i (by
      simpa [ofState] using hi)
    have hpresence' : state.data.entries[i].value.isSome = mode := by
      simpa [ofState, List.getElem_map, Array.getElem_toList] using hpresence
    exact (value_isSome_eq_mode_iff mode state.data.entries[i]).mp hpresence'
  · rintro ⟨hbit, hmode⟩
    refine ⟨hbit, ?_⟩
    intro i hi
    have hiArray : i < state.data.entries.size := by
      simpa [ofState] using hi
    have hpresent :=
      (value_isSome_eq_mode_iff mode state.data.entries[i]).mpr
        (hmode i hiArray)
    simpa [ofState, List.getElem_map, Array.getElem_toList] using hpresent

/-- Package an actual active state into the raw snapshot predicate. -/
theorem activeCore_ofState (mode : Bool) (state : MergeState κ ν)
    (hInv : TempStorageInv state.a state.alloced)
    (hLive : state.a.Live)
    (hBit : state.a.hasValues = mode)
    (hMode : SortSlice.ValuesModeInvariant state.a.hasValues state.data) :
    (ofState state).ActiveCore mode := by
  refine ⟨(storageInv_ofState_iff state).2 hInv,
    (live_ofState_iff state).2 hLive, ?_, ?_⟩
  · exact TempStorageInv.cells_size_eq hInv hLive
  · apply (valuesMode_ofState_iff mode state).2
    refine ⟨hBit, ?_⟩
    simpa [hBit] using hMode

end MergeMemorySnapshot

namespace MergeMemoryCallEvent

/-- The intermediate released snapshot which the C control flow exposes when
`merge_getmem` leaves the signed-capacity reuse branch.  This is a raw
observation constructor: the semantic lemmas below prove that its `some`
case is exactly the state immediately after `mergeFreemem`. -/
def mergeMemoryIntermediateFree (state : MergeState κ ν) (need : PySSize) :
    Option MergeMemorySnapshot :=
  if need.sle state.alloced then none
  else some (MergeMemorySnapshot.ofState (mergeFreemem state))

/-- Raw lifecycle observation for one completed `merge_lo` call. -/
def mergeLoMemoryCallEvent (call : MergeAtCall κ ν)
    (result : MergeLoResult κ ν) : MergeMemoryCallEvent :=
  let need : PySSize := BitVec.ofNat 64 call.na
  let allocated := mergeLoAllocated call
  { direction := .lo
    request := need
    na := call.na
    nb := call.nb
    sourceLeftLength := call.left.len
    sourceRightLength := call.right.len
    listlen := call.state.listlen
    outcome := allocated.outcome
    before := MergeMemorySnapshot.ofState call.state
    intermediateFree := mergeMemoryIntermediateFree call.state need
    afterGetmem := MergeMemorySnapshot.ofState allocated.state
    afterMerge := MergeMemorySnapshot.ofState result.state }

/-- Raw lifecycle observation for one completed `merge_hi` call. -/
def mergeHiMemoryCallEvent (call : MergeAtCall κ ν)
    (result : MergeHiResult κ ν) : MergeMemoryCallEvent :=
  let need : PySSize := BitVec.ofNat 64 call.nb
  let allocated := mergeHiAllocated call
  { direction := .hi
    request := need
    na := call.na
    nb := call.nb
    sourceLeftLength := call.left.len
    sourceRightLength := call.right.len
    listlen := call.state.listlen
    outcome := allocated.outcome
    before := MergeMemorySnapshot.ofState call.state
    intermediateFree := mergeMemoryIntermediateFree call.state need
    afterGetmem := MergeMemorySnapshot.ofState allocated.state
    afterMerge := MergeMemorySnapshot.ofState result.state }

/-- Snapshot-level record of the exact `merge_freemem` transition which
precedes a growing (or guard-rejected) allocation attempt. -/
def IsFreedFrom (before freed : MergeMemorySnapshot) : Prop :=
  freed.hasValues = before.hasValues ∧
    freed.alloced = before.alloced ∧
    freed.mainValuePresent = before.mainValuePresent ∧
    if before.backing = .inline then
      freed = before
    else
      freed.backing = .released ∧ freed.cellsSize = 0 ∧
        freed.physicalSlots = 0

/-- `mergeFreemem` has exactly the raw snapshot transition specified by
`IsFreedFrom`, including the inline no-op and the released heap payload. -/
theorem isFreedFrom_ofState_mergeFreemem (state : MergeState κ ν) :
    IsFreedFrom (MergeMemorySnapshot.ofState state)
      (MergeMemorySnapshot.ofState (mergeFreemem state)) := by
  cases hbacking : state.a.backing <;>
    simp [IsFreedFrom, MergeMemorySnapshot.ofState, mergeFreemem,
      hbacking, TempStorage.physicalSlots]

/-- Exact successful `merge_getmem` behavior visible in a call record.
The rejected branch is deliberately absent; later proofs must derive one of
these two arms from the pending-layout request bound. -/
def GetmemValid (call : MergeMemoryCallEvent) : Prop :=
  (call.outcome = .reused ∧
      call.request.sle call.before.alloced = true ∧
      call.intermediateFree = none ∧
      call.afterGetmem = call.before) ∨
    (call.outcome = .grown ∧
      call.request.sle call.before.alloced = false ∧
      ∃ freed,
        call.intermediateFree = some freed ∧
        IsFreedFrom call.before freed ∧
        call.request.toNat ≤ call.before.allocationLimit ∧
        call.afterGetmem.backing = .heap ∧
        call.afterGetmem.hasValues = call.before.hasValues ∧
        call.afterGetmem.alloced = call.request ∧
        call.afterGetmem.cellsSize = call.request.toNat ∧
        call.afterGetmem.physicalSlots =
          call.before.multiplier * call.request.toNat ∧
        call.afterGetmem.mainValuePresent =
          call.before.mainValuePresent)

/-- The literal reuse/growth projection of `mergeGetmem` satisfies the raw
event contract whenever the exact C allocation guard is discharged. -/
private theorem actual_getmemValid
    (direction : MergeMemoryDirection) (state : MergeState κ ν)
    (need : PySSize) (na nb : Nat) (left right listlen : PySSize)
    (hLimit : need.toNat ≤ mergeGetmemAllocationLimit state.a) :
    let allocated := mergeGetmem state need
    let call : MergeMemoryCallEvent :=
      { direction := direction
        request := need
        na := na
        nb := nb
        sourceLeftLength := left
        sourceRightLength := right
        listlen := listlen
        outcome := allocated.outcome
        before := MergeMemorySnapshot.ofState state
        intermediateFree := mergeMemoryIntermediateFree state need
        afterGetmem := MergeMemorySnapshot.ofState allocated.state
        afterMerge := MergeMemorySnapshot.ofState allocated.state }
    call.GetmemValid := by
  dsimp only
  by_cases hReuse : need.sle state.alloced = true
  · left
    rw [mergeGetmem_reused state need hReuse]
    refine ⟨rfl, ?_, ?_, rfl⟩
    · simpa [MergeMemorySnapshot.ofState] using hReuse
    · simp [mergeMemoryIntermediateFree, hReuse]
  · have hReuseFalse : need.sle state.alloced = false :=
      Bool.eq_false_of_not_eq_true hReuse
    right
    have hGrown := mergeGetmem_grown state need hReuseFalse hLimit
    simp only at hGrown
    rcases hGrown with
      ⟨hOutcome, hAlloced, hBacking, hValues, hCells⟩
    refine ⟨hOutcome, hReuseFalse, ?_⟩
    refine ⟨MergeMemorySnapshot.ofState (mergeFreemem state), ?_,
      isFreedFrom_ofState_mergeFreemem state, hLimit, ?_⟩
    · simp [mergeMemoryIntermediateFree, hReuseFalse]
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
    · simpa [MergeMemorySnapshot.ofState] using hBacking
    · simpa [MergeMemorySnapshot.ofState] using hValues
    · simpa [MergeMemorySnapshot.ofState] using hAlloced
    · simpa [MergeMemorySnapshot.ofState] using
        congrArg Array.size hCells
    · have hPhysical :=
        mergeGetmem_grown_physicalSlots state need hReuseFalse hLimit
      by_cases hValuesBit : state.a.hasValues = true
      · simpa [MergeMemorySnapshot.ofState, MergeMemorySnapshot.multiplier,
          TempStorage.multiplier, hValuesBit] using hPhysical
      · simpa [MergeMemorySnapshot.ofState, MergeMemorySnapshot.multiplier,
          TempStorage.multiplier, hValuesBit] using hPhysical
    · have hData := mergeGetmem_nonStorageFrame state need
      exact congrArg
        (fun frame =>
          frame.data.entries.toList.map fun entry => entry.value.isSome)
        hData

/-- The concrete allocation embedded in a reviewed `merge_lo` call has the
exact reuse-or-growth event shape; guard rejection is excluded by the
request-bound certificate. -/
theorem mergeLoMemoryCallEvent_getmemValid
    (pre : MergeState κ ν) (scanned i : Nat) (call : MergeAtCall κ ν)
    (execution : TraceResult (MergeLoResult κ ν))
    (result : MergeLoResult κ ν)
    (post : MergeLoSafetyPost pre scanned i call execution result) :
    (mergeLoMemoryCallEvent call result).GetmemValid := by
  simpa only [mergeLoMemoryCallEvent, mergeLoAllocated, GetmemValid] using
    actual_getmemValid (.lo) call.state (BitVec.ofNat 64 call.na)
      call.na call.nb call.left.len call.right.len call.state.listlen
      post.requestFacts.requestWithinLimit

/-- The concrete allocation embedded in a reviewed `merge_hi` call has the
same exact reuse-or-growth shape. -/
theorem mergeHiMemoryCallEvent_getmemValid
    (pre : MergeState κ ν) (scanned i : Nat) (call : MergeAtCall κ ν)
    (execution : TraceResult (MergeHiResult κ ν))
    (result : MergeHiResult κ ν)
    (post : MergeHiSafetyPost pre scanned i call execution result) :
    (mergeHiMemoryCallEvent call result).GetmemValid := by
  simpa only [mergeHiMemoryCallEvent, mergeHiAllocated, GetmemValid] using
    actual_getmemValid (.hi) call.state (BitVec.ofNat 64 call.nb)
      call.na call.nb call.left.len call.right.len call.state.listlen
      post.requestFacts.requestWithinLimit

/-- The merge proper can change main-data order and temporary contents, but
not the allocation metadata installed by `merge_getmem`. -/
def MergeStorageFrame (call : MergeMemoryCallEvent) : Prop :=
  call.afterMerge.backing = call.afterGetmem.backing ∧
    call.afterMerge.hasValues = call.afterGetmem.hasValues ∧
    call.afterMerge.cellsSize = call.afterGetmem.cellsSize ∧
    call.afterMerge.alloced = call.afterGetmem.alloced ∧
    call.afterMerge.physicalSlots = call.afterGetmem.physicalSlots ∧
    call.afterMerge.mainValuePresent.length =
      call.afterGetmem.mainValuePresent.length

/-- A successful allocation certificate packages an active snapshot in the
same values mode as the incoming main array. -/
theorem activeCore_of_getmemStoragePost
    (mode : Bool) (before : MergeState κ ν) (need : PySSize)
    (result : MergeGetmemResult κ ν)
    (post : MergeGetmemStoragePost before need result)
    (hBit : before.a.hasValues = mode)
    (hMode : SortSlice.ValuesModeInvariant before.a.hasValues before.data) :
    (MergeMemorySnapshot.ofState result.state).ActiveCore mode := by
  apply MergeMemorySnapshot.activeCore_ofState mode result.state
    post.invariant post.live (post.valuesMode.trans hBit)
  rw [post.data_eq, post.valuesMode]
  exact hMode

/-- The exact physical-slot equation and request-fit fact exported by
`merge_getmem` put every requested key slot in range. -/
theorem keySlots_of_getmemStoragePost
    (before : MergeState κ ν) (need : PySSize)
    (result : MergeGetmemResult κ ν)
    (post : MergeGetmemStoragePost before need result) :
    ∀ i, i < need.toNat → i < result.state.a.physicalSlots := by
  intro i hi
  have hfit := post.requestFits
  have hslots := post.physicalSlots
  cases hValues : result.state.a.hasValues <;>
    simp [TempStorage.multiplier, hValues] at hslots <;> omega

/-- In keyed mode, the second half of the exact allocation contains one
value slot for every admitted logical request slot. -/
theorem valueSlots_of_getmemStoragePost
    (before : MergeState κ ν) (need : PySSize)
    (result : MergeGetmemResult κ ν)
    (post : MergeGetmemStoragePost before need result)
    (hValues : before.a.hasValues = true) :
    ∀ i, i < need.toNat →
      result.state.alloced.toNat + i < result.state.a.physicalSlots := by
  intro i hi
  have hfit := post.requestFits
  have hResultValues : result.state.a.hasValues = true :=
    post.valuesMode.trans hValues
  have hslots := post.physicalSlots
  simp [TempStorage.multiplier, hResultValues] at hslots
  omega

/-- Reuse transports an incoming physical bound exactly; growth establishes
it from the allocation guard. -/
theorem physicalBound_of_getmemStoragePost
    (before : MergeState κ ν) (need : PySSize)
    (result : MergeGetmemResult κ ν)
    (post : MergeGetmemStoragePost before need result)
    (hBefore : before.a.physicalSlots ≤
      PY_SSIZE_T_MAX / PY_OBJECT_PTR_BYTES) :
    result.state.a.physicalSlots ≤
      PY_SSIZE_T_MAX / PY_OBJECT_PTR_BYTES := by
  rcases post.outcome with hReuse | hGrowth
  · rw [post.reuseAccounting hReuse]
    exact hBefore
  · exact (post.growthAccounting hGrowth).2.2.2.2

/-- Freeing preserves the physical bound: inline storage is unchanged and
every other backing becomes the empty released representation. -/
theorem physicalBound_of_mergeFreemem
    (state : MergeState κ ν)
    (hBefore : (MergeMemorySnapshot.ofState state).PhysicalBound) :
    (MergeMemorySnapshot.ofState (mergeFreemem state)).PhysicalBound := by
  cases hBacking : state.a.backing
  · simpa [MergeMemorySnapshot.PhysicalBound,
      MergeMemorySnapshot.ofState, mergeFreemem, hBacking,
      TempStorage.physicalSlots] using hBefore
  · simp [MergeMemorySnapshot.PhysicalBound,
      MergeMemorySnapshot.ofState, mergeFreemem, hBacking,
      TempStorage.physicalSlots]
  · simp [MergeMemorySnapshot.PhysicalBound,
      MergeMemorySnapshot.ofState, mergeFreemem, hBacking,
      TempStorage.physicalSlots]

/-- All semantic facts required of one actual directional merge record. -/
structure Valid (mode : Bool) (call : MergeMemoryCallEvent) : Prop where
  beforeActive : call.before.ActiveCore mode
  getmemActive : call.afterGetmem.ActiveCore mode
  afterMergeActive : call.afterMerge.ActiveCore mode
  requestWord : call.request = BitVec.ofNat 64 (min call.na call.nb)
  requestNonnegative : call.request.Nonnegative
  directionalRequest :
    (call.direction = .lo ∧ call.request.toNat = call.na ∧
      call.na ≤ call.nb) ∨
    (call.direction = .hi ∧ call.request.toNat = call.nb ∧
      call.nb < call.na)
  trimmingOnlyShrinks :
    call.na + call.nb ≤
      call.sourceLeftLength.toNat + call.sourceRightLength.toNat
  sourceRunsWithinList :
    call.sourceLeftLength.toNat + call.sourceRightLength.toNat ≤
      call.listlen.toNat
  smallerHalf :
    call.request.toNat ≤ (call.na + call.nb) / 2 ∧
      (call.na + call.nb) / 2 ≤ call.listlen.toNat / 2
  keyedLimit : call.before.hasValues = true →
    call.before.allocationLimit =
        PY_SSIZE_T_MAX / PY_OBJECT_PTR_BYTES / 2 ∧
      PY_SSIZE_T_MAX / PY_OBJECT_PTR_BYTES / 2 = 2 ^ 59 - 1
  unkeyedLimit : call.before.hasValues = false →
    call.before.allocationLimit =
        PY_SSIZE_T_MAX / PY_OBJECT_PTR_BYTES ∧
      PY_SSIZE_T_MAX / PY_OBJECT_PTR_BYTES = 2 ^ 60 - 1
  requestWithinLimit : call.request.toNat ≤ call.before.allocationLimit
  getmem : call.GetmemValid
  neverGuardRejected : call.outcome ≠ .guardRejected
  requestFits : call.request.toNat ≤ call.afterGetmem.alloced.toNat
  keySlots : ∀ i, i < call.request.toNat →
    i < call.afterGetmem.physicalSlots
  valueSlots : call.before.hasValues = true →
    ∀ i, i < call.request.toNat →
      call.afterGetmem.alloced.toNat + i <
        call.afterGetmem.physicalSlots
  mergeStorageFrame : call.MergeStorageFrame
  /-- Reuse preserves an already-established bound; growth establishes it
  from the exact allocation guard. -/
  physicalBoundPreserved : call.before.PhysicalBound →
    call.afterGetmem.PhysicalBound ∧ call.afterMerge.PhysicalBound

/-- Anti-vacuity regression for the allocation guard: a raw observation that
claims the rejected outcome cannot satisfy the lifecycle call contract. -/
theorem valid_rejects_guardRejected (mode : Bool)
    (call : MergeMemoryCallEvent) (hRejected : call.outcome = .guardRejected) :
    ¬ call.Valid mode := by
  intro hValid
  exact hValid.neverGuardRejected hRejected

/-- The exported `merge_lo` storage frame is exactly the snapshot frame used
by the lifecycle predicate. -/
theorem mergeLoMemoryCallEvent_mergeStorageFrame
    (pre : MergeState κ ν) (scanned i : Nat) (call : MergeAtCall κ ν)
    (execution : TraceResult (MergeLoResult κ ν))
    (result : MergeLoResult κ ν)
    (post : MergeLoSafetyPost pre scanned i call execution result) :
    (mergeLoMemoryCallEvent call result).MergeStorageFrame := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · simpa [mergeLoMemoryCallEvent, MergeMemorySnapshot.ofState] using
      post.postGetmemStorageFrame.backing
  · simpa [mergeLoMemoryCallEvent, MergeMemorySnapshot.ofState] using
      post.postGetmemStorageFrame.hasValues
  · simpa [mergeLoMemoryCallEvent, MergeMemorySnapshot.ofState] using
      post.postGetmemStorageFrame.cellsSize
  · simpa [mergeLoMemoryCallEvent, MergeMemorySnapshot.ofState] using
      post.postGetmemStorageFrame.alloced
  · simpa [mergeLoMemoryCallEvent, MergeMemorySnapshot.ofState] using
      post.postGetmemStorageFrame.physicalSlots_eq
  · simp only [mergeLoMemoryCallEvent, MergeMemorySnapshot.ofState,
      List.length_map, Array.length_toList]
    rw [post.stableFrame.dataSize, post.allocationPost.data_eq]

/-- The exported `merge_hi` storage frame is exactly the snapshot frame used
by the lifecycle predicate. -/
theorem mergeHiMemoryCallEvent_mergeStorageFrame
    (pre : MergeState κ ν) (scanned i : Nat) (call : MergeAtCall κ ν)
    (execution : TraceResult (MergeHiResult κ ν))
    (result : MergeHiResult κ ν)
    (post : MergeHiSafetyPost pre scanned i call execution result) :
    (mergeHiMemoryCallEvent call result).MergeStorageFrame := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · simpa [mergeHiMemoryCallEvent, MergeMemorySnapshot.ofState] using
      post.postGetmemStorageFrame.backing
  · simpa [mergeHiMemoryCallEvent, MergeMemorySnapshot.ofState] using
      post.postGetmemStorageFrame.hasValues
  · simpa [mergeHiMemoryCallEvent, MergeMemorySnapshot.ofState] using
      post.postGetmemStorageFrame.cellsSize
  · simpa [mergeHiMemoryCallEvent, MergeMemorySnapshot.ofState] using
      post.postGetmemStorageFrame.alloced
  · simpa [mergeHiMemoryCallEvent, MergeMemorySnapshot.ofState] using
      post.postGetmemStorageFrame.physicalSlots_eq
  · simp only [mergeHiMemoryCallEvent, MergeMemorySnapshot.ofState,
      List.length_map, Array.length_toList]
    rw [post.stableFrame.dataSize, post.allocationPost.data_eq]

/-- A literal completed `merge_lo` call satisfies every semantic lifecycle
obligation.  Its directional safety post retains the incoming representation,
liveness, and values-mode facts, so this theorem cannot reconstruct a phantom
pre-state from a successful allocation result. -/
theorem mergeLoMemoryCallEvent_valid
    (mode : Bool) (pre : MergeState κ ν) (scanned i : Nat)
    (call : MergeAtCall κ ν)
    (execution : TraceResult (MergeLoResult κ ν))
    (result : MergeLoResult κ ν)
    (post : MergeLoSafetyPost pre scanned i call execution result)
    (hBit : call.state.a.hasValues = mode) :
    (mergeLoMemoryCallEvent call result).Valid mode := by
  have hDispatch : call.na ≤ call.nb := by
    rcases post.requestFacts.sourceDispatch with hLo | hHi
    · exact hLo.2
    · omega
  have hFinalBit : result.state.a.hasValues = mode :=
    post.stableFrame.tempValuesMode.trans hBit
  refine
    { beforeActive := MergeMemorySnapshot.activeCore_ofState mode call.state
        post.inputTempInvariant post.inputTempLive hBit post.inputValuesMode
      getmemActive := activeCore_of_getmemStoragePost mode call.state
        (BitVec.ofNat 64 call.na) (mergeLoAllocated call)
        post.allocationPost hBit post.inputValuesMode
      afterMergeActive := MergeMemorySnapshot.activeCore_ofState mode
        result.state post.tempInvariant post.tempLive hFinalBit post.valuesMode
      requestWord := ?_
      requestNonnegative := ?_
      directionalRequest := ?_
      trimmingOnlyShrinks := post.requestFacts.runLengthChain.1
      sourceRunsWithinList := ?_
      smallerHalf := ?_
      keyedLimit := ?_
      unkeyedLimit := ?_
      requestWithinLimit := ?_
      getmem := ?_
      neverGuardRejected := ?_
      requestFits := ?_
      keySlots := ?_
      valueSlots := ?_
      mergeStorageFrame := mergeLoMemoryCallEvent_mergeStorageFrame
        pre scanned i call execution result post
      physicalBoundPreserved := ?_ }
  · simpa [mergeLoMemoryCallEvent] using congrArg (BitVec.ofNat 64)
      post.requestFacts.requestIsMinimum
  · simpa [mergeLoMemoryCallEvent] using
      post.requestFacts.requestNonnegative
  · left
    exact ⟨rfl, by simpa [mergeLoMemoryCallEvent] using
      post.requestFacts.requestRoundtrip, hDispatch⟩
  · simp only [mergeLoMemoryCallEvent]
    rw [post.requestFacts.listlenFrame]
    exact post.requestFacts.runLengthChain.2.1.trans
      post.requestFacts.runLengthChain.2.2
  · simp only [mergeLoMemoryCallEvent]
    rw [post.requestFacts.listlenFrame]
    exact post.requestFacts.requestWordHalfChain
  · intro hValues
    simpa only [mergeLoMemoryCallEvent,
      MergeMemorySnapshot.allocationLimit_ofState] using
      post.requestFacts.keyedLimit hValues
  · intro hValues
    simpa only [mergeLoMemoryCallEvent,
      MergeMemorySnapshot.allocationLimit_ofState] using
      post.requestFacts.unkeyedLimit hValues
  · simpa only [mergeLoMemoryCallEvent,
      MergeMemorySnapshot.allocationLimit_ofState] using
      post.requestFacts.requestWithinLimit
  · exact mergeLoMemoryCallEvent_getmemValid
      pre scanned i call execution result post
  · simpa only [mergeLoMemoryCallEvent, mergeLoAllocated] using
      post.requestFacts.guardNotRejected
  · simpa only [mergeLoMemoryCallEvent, MergeMemorySnapshot.ofState] using
      post.allocationPost.requestFits
  · simpa only [mergeLoMemoryCallEvent, MergeMemorySnapshot.ofState] using
      keySlots_of_getmemStoragePost call.state (BitVec.ofNat 64 call.na)
        (mergeLoAllocated call) post.allocationPost
  · intro hValues
    simpa only [mergeLoMemoryCallEvent, MergeMemorySnapshot.ofState] using
      valueSlots_of_getmemStoragePost call.state (BitVec.ofNat 64 call.na)
        (mergeLoAllocated call) post.allocationPost hValues
  · intro hBefore
    have hBefore' : call.state.a.physicalSlots ≤
        PY_SSIZE_T_MAX / PY_OBJECT_PTR_BYTES := by
      simpa [mergeLoMemoryCallEvent, MergeMemorySnapshot.PhysicalBound,
        MergeMemorySnapshot.ofState] using hBefore
    have hAllocated := physicalBound_of_getmemStoragePost call.state
      (BitVec.ofNat 64 call.na) (mergeLoAllocated call)
      post.allocationPost hBefore'
    exact ⟨by simpa [mergeLoMemoryCallEvent,
      MergeMemorySnapshot.PhysicalBound, MergeMemorySnapshot.ofState] using
        hAllocated,
      by simpa [mergeLoMemoryCallEvent, MergeMemorySnapshot.PhysicalBound,
        MergeMemorySnapshot.ofState] using post.physicalSlotsBound hBefore'⟩

/-- Right-to-left counterpart of `mergeLoMemoryCallEvent_valid`.  It consumes
the same representation, liveness, mode, request-bound, and allocation facts;
only the directional request branch differs. -/
theorem mergeHiMemoryCallEvent_valid
    (mode : Bool) (pre : MergeState κ ν) (scanned i : Nat)
    (call : MergeAtCall κ ν)
    (execution : TraceResult (MergeHiResult κ ν))
    (result : MergeHiResult κ ν)
    (post : MergeHiSafetyPost pre scanned i call execution result)
    (hBit : call.state.a.hasValues = mode) :
    (mergeHiMemoryCallEvent call result).Valid mode := by
  have hFinalBit : result.state.a.hasValues = mode :=
    post.stableFrame.tempValuesMode.trans hBit
  refine
    { beforeActive := MergeMemorySnapshot.activeCore_ofState mode call.state
        post.inputTempInvariant post.inputTempLive hBit post.inputValuesMode
      getmemActive := activeCore_of_getmemStoragePost mode call.state
        (BitVec.ofNat 64 call.nb) (mergeHiAllocated call)
        post.allocationPost hBit post.inputValuesMode
      afterMergeActive := MergeMemorySnapshot.activeCore_ofState mode
        result.state post.tempInvariant post.tempLive hFinalBit post.valuesMode
      requestWord := ?_
      requestNonnegative := ?_
      directionalRequest := ?_
      trimmingOnlyShrinks := post.requestFacts.runLengthChain.1
      sourceRunsWithinList := ?_
      smallerHalf := ?_
      keyedLimit := ?_
      unkeyedLimit := ?_
      requestWithinLimit := ?_
      getmem := ?_
      neverGuardRejected := ?_
      requestFits := ?_
      keySlots := ?_
      valueSlots := ?_
      mergeStorageFrame := mergeHiMemoryCallEvent_mergeStorageFrame
        pre scanned i call execution result post
      physicalBoundPreserved := ?_ }
  · simpa [mergeHiMemoryCallEvent] using congrArg (BitVec.ofNat 64)
      post.requestFacts.requestIsMinimum
  · simpa [mergeHiMemoryCallEvent] using
      post.requestFacts.requestNonnegative
  · right
    exact ⟨rfl, by simpa [mergeHiMemoryCallEvent] using
      post.requestFacts.requestRoundtrip, post.directionalDispatch⟩
  · simp only [mergeHiMemoryCallEvent]
    rw [post.requestFacts.listlenFrame]
    exact post.requestFacts.runLengthChain.2.1.trans
      post.requestFacts.runLengthChain.2.2
  · simp only [mergeHiMemoryCallEvent]
    rw [post.requestFacts.listlenFrame]
    exact post.requestFacts.requestWordHalfChain
  · intro hValues
    simpa only [mergeHiMemoryCallEvent,
      MergeMemorySnapshot.allocationLimit_ofState] using
      post.requestFacts.keyedLimit hValues
  · intro hValues
    simpa only [mergeHiMemoryCallEvent,
      MergeMemorySnapshot.allocationLimit_ofState] using
      post.requestFacts.unkeyedLimit hValues
  · simpa only [mergeHiMemoryCallEvent,
      MergeMemorySnapshot.allocationLimit_ofState] using
      post.requestFacts.requestWithinLimit
  · exact mergeHiMemoryCallEvent_getmemValid
      pre scanned i call execution result post
  · simpa only [mergeHiMemoryCallEvent, mergeHiAllocated] using
      post.requestFacts.guardNotRejected
  · simpa only [mergeHiMemoryCallEvent, MergeMemorySnapshot.ofState] using
      post.allocationPost.requestFits
  · simpa only [mergeHiMemoryCallEvent, MergeMemorySnapshot.ofState] using
      keySlots_of_getmemStoragePost call.state (BitVec.ofNat 64 call.nb)
        (mergeHiAllocated call) post.allocationPost
  · intro hValues
    simpa only [mergeHiMemoryCallEvent, MergeMemorySnapshot.ofState] using
      valueSlots_of_getmemStoragePost call.state (BitVec.ofNat 64 call.nb)
        (mergeHiAllocated call) post.allocationPost hValues
  · intro hBefore
    have hBefore' : call.state.a.physicalSlots ≤
        PY_SSIZE_T_MAX / PY_OBJECT_PTR_BYTES := by
      simpa [mergeHiMemoryCallEvent, MergeMemorySnapshot.PhysicalBound,
        MergeMemorySnapshot.ofState] using hBefore
    have hAllocated := physicalBound_of_getmemStoragePost call.state
      (BitVec.ofNat 64 call.nb) (mergeHiAllocated call)
      post.allocationPost hBefore'
    exact ⟨by simpa [mergeHiMemoryCallEvent,
      MergeMemorySnapshot.PhysicalBound, MergeMemorySnapshot.ofState] using
        hAllocated,
      by simpa [mergeHiMemoryCallEvent, MergeMemorySnapshot.PhysicalBound,
        MergeMemorySnapshot.ofState] using post.physicalSlotsBound hBefore'⟩

/-- The stronger per-call projection used once the initializer's physical
bound has been threaded to this call site. -/
def Bounded (call : MergeMemoryCallEvent) : Prop :=
  call.before.PhysicalBound ∧ call.afterGetmem.PhysicalBound ∧
    call.afterMerge.PhysicalBound ∧
    ∀ freed ∈ call.intermediateFree, freed.PhysicalBound

/-- A valid literal `merge_lo` record is bounded once the caller supplies the
bound threaded from `merge_init`.  The optional freed snapshot is checked
against the actual `mergeFreemem` transition rather than discarded. -/
theorem mergeLoMemoryCallEvent_bounded
    (mode : Bool) (call : MergeAtCall κ ν) (result : MergeLoResult κ ν)
    (hValid : (mergeLoMemoryCallEvent call result).Valid mode)
    (hBefore : call.state.a.physicalSlots ≤
      PY_SSIZE_T_MAX / PY_OBJECT_PTR_BYTES) :
    (mergeLoMemoryCallEvent call result).Bounded := by
  have hBeforeSnapshot :
      (MergeMemorySnapshot.ofState call.state).PhysicalBound := by
    simpa [MergeMemorySnapshot.PhysicalBound,
      MergeMemorySnapshot.ofState] using hBefore
  have hAfter := hValid.physicalBoundPreserved (by
    simpa [mergeLoMemoryCallEvent] using hBeforeSnapshot)
  refine ⟨by simpa [mergeLoMemoryCallEvent] using hBeforeSnapshot,
    hAfter.1, hAfter.2, ?_⟩
  intro freed hFreed
  by_cases hReuse :
      (BitVec.ofNat 64 call.na).sle call.state.alloced = true
  · simp [mergeLoMemoryCallEvent, mergeMemoryIntermediateFree,
      hReuse] at hFreed
  · have hReuseFalse :
        (BitVec.ofNat 64 call.na).sle call.state.alloced = false :=
      Bool.eq_false_of_not_eq_true hReuse
    have hFreedEq :
        freed = MergeMemorySnapshot.ofState (mergeFreemem call.state) := by
      symm
      simpa [mergeLoMemoryCallEvent, mergeMemoryIntermediateFree,
        hReuseFalse] using hFreed
    rw [hFreedEq]
    exact physicalBound_of_mergeFreemem call.state hBeforeSnapshot

/-- Right-to-left counterpart of `mergeLoMemoryCallEvent_bounded`. -/
theorem mergeHiMemoryCallEvent_bounded
    (mode : Bool) (call : MergeAtCall κ ν) (result : MergeHiResult κ ν)
    (hValid : (mergeHiMemoryCallEvent call result).Valid mode)
    (hBefore : call.state.a.physicalSlots ≤
      PY_SSIZE_T_MAX / PY_OBJECT_PTR_BYTES) :
    (mergeHiMemoryCallEvent call result).Bounded := by
  have hBeforeSnapshot :
      (MergeMemorySnapshot.ofState call.state).PhysicalBound := by
    simpa [MergeMemorySnapshot.PhysicalBound,
      MergeMemorySnapshot.ofState] using hBefore
  have hAfter := hValid.physicalBoundPreserved (by
    simpa [mergeHiMemoryCallEvent] using hBeforeSnapshot)
  refine ⟨by simpa [mergeHiMemoryCallEvent] using hBeforeSnapshot,
    hAfter.1, hAfter.2, ?_⟩
  intro freed hFreed
  by_cases hReuse :
      (BitVec.ofNat 64 call.nb).sle call.state.alloced = true
  · simp [mergeHiMemoryCallEvent, mergeMemoryIntermediateFree,
      hReuse] at hFreed
  · have hReuseFalse :
        (BitVec.ofNat 64 call.nb).sle call.state.alloced = false :=
      Bool.eq_false_of_not_eq_true hReuse
    have hFreedEq :
        freed = MergeMemorySnapshot.ofState (mergeFreemem call.state) := by
      symm
      simpa [mergeHiMemoryCallEvent, mergeMemoryIntermediateFree,
        hReuseFalse] using hFreed
    rw [hFreedEq]
    exact physicalBound_of_mergeFreemem call.state hBeforeSnapshot

/-- Direct reviewed-post projection of the complete bounded `merge_lo`
record. -/
theorem mergeLoMemoryCallEvent_bounded_of_post
    (mode : Bool) (pre : MergeState κ ν) (scanned i : Nat)
    (call : MergeAtCall κ ν)
    (execution : TraceResult (MergeLoResult κ ν))
    (result : MergeLoResult κ ν)
    (post : MergeLoSafetyPost pre scanned i call execution result)
    (hBit : call.state.a.hasValues = mode)
    (hBefore : call.state.a.physicalSlots ≤
      PY_SSIZE_T_MAX / PY_OBJECT_PTR_BYTES) :
    (mergeLoMemoryCallEvent call result).Bounded :=
  mergeLoMemoryCallEvent_bounded mode call result
    (mergeLoMemoryCallEvent_valid mode pre scanned i call execution result
      post hBit)
    hBefore

/-- Direct reviewed-post projection of the complete bounded `merge_hi`
record. -/
theorem mergeHiMemoryCallEvent_bounded_of_post
    (mode : Bool) (pre : MergeState κ ν) (scanned i : Nat)
    (call : MergeAtCall κ ν)
    (execution : TraceResult (MergeHiResult κ ν))
    (result : MergeHiResult κ ν)
    (post : MergeHiSafetyPost pre scanned i call execution result)
    (hBit : call.state.a.hasValues = mode)
    (hBefore : call.state.a.physicalSlots ≤
      PY_SSIZE_T_MAX / PY_OBJECT_PTR_BYTES) :
    (mergeHiMemoryCallEvent call result).Bounded :=
  mergeHiMemoryCallEvent_bounded mode call result
    (mergeHiMemoryCallEvent_valid mode pre scanned i call execution result
      post hBit)
    hBefore

end MergeMemoryCallEvent

namespace MergeMemoryEvent

/-- Exact snapshot-level cleanup contract, including the intentional stale
metadata exception for released heap storage. -/
def CleanupValid (mode : Bool) (before after : MergeMemorySnapshot) : Prop :=
  before.ActiveCore mode ∧ after.StorageInv ∧ after.ValuesMode mode ∧
    MergeMemoryCallEvent.IsFreedFrom before after

/-- The real terminal `merge_freemem` transition satisfies the cleanup
contract.  The post-state may retain stale `alloced`, but its released payload
is empty and its physical-slot observation is zero. -/
theorem cleanupValid_ofState_mergeFreemem (mode : Bool)
    (state : MergeState κ ν)
    (hInv : TempStorageInv state.a state.alloced)
    (hLive : state.a.Live)
    (hBit : state.a.hasValues = mode)
    (hMode : SortSlice.ValuesModeInvariant state.a.hasValues state.data) :
    CleanupValid mode (MergeMemorySnapshot.ofState state)
      (MergeMemorySnapshot.ofState (mergeFreemem state)) := by
  refine ⟨MergeMemorySnapshot.activeCore_ofState mode state hInv hLive hBit
      hMode, ?_, ?_, MergeMemoryCallEvent.isFreedFrom_ofState_mergeFreemem state⟩
  · exact (MergeMemorySnapshot.storageInv_ofState_iff
      (mergeFreemem state)).2 (mergeFreemem_tempStorageInv state hInv)
  · apply (MergeMemorySnapshot.valuesMode_ofState_iff mode
      (mergeFreemem state)).2
    refine ⟨?_, ?_⟩
    · by_cases hInline : state.a.backing = .inline <;>
        simp [mergeFreemem, hInline, hBit]
    · by_cases hInline : state.a.backing = .inline <;>
        simpa [mergeFreemem, hInline, hBit] using hMode

/-- Semantic validity of a raw event. -/
def Valid (mode : Bool) : MergeMemoryEvent → Prop
  | .initial snapshot => snapshot.ActiveCore mode
  | .mergeCall call => call.Valid mode
  | .cleanup before after => CleanupValid mode before after

/-- The state entering an event. -/
def start : MergeMemoryEvent → MergeMemorySnapshot
  | .initial snapshot => snapshot
  | .mergeCall call => call.before
  | .cleanup before _ => before

/-- The state leaving an event. -/
def finish : MergeMemoryEvent → MergeMemorySnapshot
  | .initial snapshot => snapshot
  | .mergeCall call => call.afterMerge
  | .cleanup _ after => after

end MergeMemoryEvent

namespace AccessTrace

/-- Consecutive directional call records form one real storage-state path.
The endpoints are explicit, so a list with no calls can describe only an
unchanged memory snapshot; no fabricated gap can be hidden between calls. -/
def MergeMemoryCallChain :
    MergeMemorySnapshot → List MergeMemoryCallEvent →
      MergeMemorySnapshot → Prop
  | start, [], final => start = final
  | start, call :: calls, final =>
      call.before = start ∧ MergeMemoryCallChain call.afterMerge calls final

namespace MergeMemoryCallChain

@[simp]
theorem nil_iff (start final : MergeMemorySnapshot) :
    MergeMemoryCallChain start [] final ↔ start = final := by
  rfl

@[simp]
theorem cons_iff (start final : MergeMemorySnapshot)
    (call : MergeMemoryCallEvent) (calls : List MergeMemoryCallEvent) :
    MergeMemoryCallChain start (call :: calls) final ↔
      call.before = start ∧
        MergeMemoryCallChain call.afterMerge calls final := by
  rfl

/-- Storage paths concatenate exactly at their shared concrete snapshot. -/
theorem append {start middle final : MergeMemorySnapshot}
    {earlier later : List MergeMemoryCallEvent}
    (hEarlier : MergeMemoryCallChain start earlier middle)
    (hLater : MergeMemoryCallChain middle later final) :
    MergeMemoryCallChain start (earlier ++ later) final := by
  induction earlier generalizing start with
  | nil =>
      simpa using hEarlier ▸ hLater
  | cons call calls ih =>
      rcases hEarlier with ⟨hStart, hTail⟩
      exact ⟨hStart, ih hTail⟩

/-- Two consecutive raw calls cannot validate as one path if the second call
does not start at the first call's recorded final state.  This is the
anti-vacuity regression for history continuity. -/
theorem rejects_two_call_gap (start final : MergeMemorySnapshot)
    (first second : MergeMemoryCallEvent)
    (hGap : second.before ≠ first.afterMerge) :
    ¬ MergeMemoryCallChain start [first, second] final := by
  intro hChain
  exact hGap hChain.2.1

end MergeMemoryCallChain

/-- Every event in the literal trace is semantically valid in the initialized
values mode. -/
def memoryEventsValid (mode : Bool) (trace : AccessTrace) : Prop :=
  ∀ event ∈ trace.memoryEvents, event.Valid mode

/-- A helper trace contains directional calls only; initialization and final
cleanup are owned exclusively by the top-level evaluator. -/
def onlyMergeMemoryEvents (trace : AccessTrace) : Prop :=
  ∀ event ∈ trace.memoryEvents, ∃ call, event = .mergeCall call

/-- All directional records in a trace carry the selected-platform physical
bound at every retained active boundary. -/
def mergeMemoryEventsBounded (trace : AccessTrace) : Prop :=
  ∀ event ∈ trace.memoryEvents,
    match event with
    | .mergeCall call => call.Bounded
    | _ => True

/-- A helper trace is exactly a continuous sequence of directional calls from
one concrete memory snapshot to another. -/
def MergeMemorySegment (start final : MergeMemorySnapshot)
    (trace : AccessTrace) : Prop :=
  ∃ calls : List MergeMemoryCallEvent,
    trace.memoryEvents = calls.map MergeMemoryEvent.mergeCall ∧
      MergeMemoryCallChain start calls final

/-- The trace segment produced from an active listsort state through its exit
contains a continuous sequence of real merge calls followed by exactly one
terminal cleanup.  Initialization is added only by `listSortImplTraced?`. -/
def MergeMemoryTail (start final : MergeMemorySnapshot)
    (trace : AccessTrace) : Prop :=
  ∃ (calls : List MergeMemoryCallEvent)
      (cleanupBefore : MergeMemorySnapshot),
    trace.memoryEvents =
      calls.map MergeMemoryEvent.mergeCall ++
        [.cleanup cleanupBefore final] ∧
      MergeMemoryCallChain start calls cleanupBefore

@[simp]
theorem memoryEvents_compose (earlier later : AccessTrace) :
    (earlier.compose later).memoryEvents =
      earlier.memoryEvents ++ later.memoryEvents := by
  rfl

@[simp]
theorem memoryEventsValid_empty (mode : Bool) : empty.memoryEventsValid mode := by
  simp [memoryEventsValid, empty]

@[simp]
theorem memoryEventsValid_compose (mode : Bool) (earlier later : AccessTrace) :
    (earlier.compose later).memoryEventsValid mode ↔
      earlier.memoryEventsValid mode ∧ later.memoryEventsValid mode := by
  simp only [memoryEventsValid, memoryEvents_compose, List.mem_append]
  aesop

@[simp]
theorem onlyMergeMemoryEvents_empty : empty.onlyMergeMemoryEvents := by
  simp [onlyMergeMemoryEvents, empty]

@[simp]
theorem onlyMergeMemoryEvents_compose (earlier later : AccessTrace) :
    (earlier.compose later).onlyMergeMemoryEvents ↔
      earlier.onlyMergeMemoryEvents ∧ later.onlyMergeMemoryEvents := by
  simp only [onlyMergeMemoryEvents, memoryEvents_compose, List.mem_append]
  aesop

@[simp]
theorem mergeMemoryEventsBounded_empty : empty.mergeMemoryEventsBounded := by
  simp [mergeMemoryEventsBounded, empty]

@[simp]
theorem mergeMemoryEventsBounded_compose (earlier later : AccessTrace) :
    (earlier.compose later).mergeMemoryEventsBounded ↔
      earlier.mergeMemoryEventsBounded ∧
        later.mergeMemoryEventsBounded := by
  simp only [mergeMemoryEventsBounded, memoryEvents_compose, List.mem_append]
  aesop

/-- Continuous helper segments compose at the exact state handed from the
first evaluator to the second. -/
theorem mergeMemorySegment_compose (earlier later : AccessTrace)
    (start middle final : MergeMemorySnapshot)
    (hearlier : earlier.MergeMemorySegment start middle)
    (hlater : later.MergeMemorySegment middle final) :
    (earlier.compose later).MergeMemorySegment start final := by
  rcases hearlier with ⟨earlierCalls, hearlierEvents, hearlierChain⟩
  rcases hlater with ⟨laterCalls, hlaterEvents, hlaterChain⟩
  refine ⟨earlierCalls ++ laterCalls, ?_,
    MergeMemoryCallChain.append hearlierChain hlaterChain⟩
  simp [AccessTrace.compose, hearlierEvents, hlaterEvents, List.map_append]

/-- Prefixing a terminal lifecycle segment by a continuous helper segment
preserves both exact event order and state-boundary continuity. -/
theorem mergeMemoryTail_compose (earlier later : AccessTrace)
    (start middle final : MergeMemorySnapshot)
    (hearlier : earlier.MergeMemorySegment start middle)
    (hlater : later.MergeMemoryTail middle final) :
    (earlier.compose later).MergeMemoryTail start final := by
  rcases hearlier with ⟨earlierCalls, hearlierEvents, hearlierChain⟩
  rcases hlater with
    ⟨laterCalls, cleanupBefore, hlaterEvents, hlaterChain⟩
  refine ⟨earlierCalls ++ laterCalls, cleanupBefore, ?_,
    MergeMemoryCallChain.append hearlierChain hlaterChain⟩
  simp [AccessTrace.compose, hearlierEvents, hlaterEvents, List.map_append,
    List.append_assoc]

/-- Exact top-level shape: one initializer, zero or more directional calls,
and one terminal cleanup.  `events` is the evaluator's literal trace field;
there is no separately supplied history which could omit a call. -/
def MergeMemoryLifecycle (mode : Bool)
    (initial final : MergeMemorySnapshot) (trace : AccessTrace) : Prop :=
  ∃ (calls : List MergeMemoryCallEvent)
      (cleanupBefore : MergeMemorySnapshot),
    trace.memoryEvents =
      .initial initial ::
        (calls.map MergeMemoryEvent.mergeCall ++
          [.cleanup cleanupBefore final]) ∧
    MergeMemoryCallChain initial calls cleanupBefore ∧
    initial.ActiveCore mode ∧
    (∀ call ∈ calls, call.Valid mode) ∧
    (∀ call ∈ calls, call.Bounded) ∧
    MergeMemoryEvent.CleanupValid mode cleanupBefore final

/-- Assemble the headline lifecycle directly from the real tail trace.  The
tail contributes exact chronology and boundary continuity; validity and the
physical bound are checked over that same literal event list. -/
theorem mergeMemoryLifecycle_prepend_initial (mode : Bool)
    (initial final : MergeMemorySnapshot) (trace : AccessTrace)
    (hTail : trace.MergeMemoryTail initial final)
    (hInitial : initial.ActiveCore mode)
    (hValid : trace.memoryEventsValid mode)
    (hBounded : trace.mergeMemoryEventsBounded) :
    MergeMemoryLifecycle mode initial final
      ((singletonMemoryEvent (.initial initial)).compose trace) := by
  rcases hTail with ⟨calls, cleanupBefore, hEvents, hChain⟩
  refine ⟨calls, cleanupBefore, ?_, hChain, hInitial, ?_, ?_, ?_⟩
  · simp [AccessTrace.compose, singletonMemoryEvent, hEvents]
  · intro call hCall
    apply hValid (.mergeCall call)
    rw [hEvents]
    simp [hCall]
  · intro call hCall
    have hEvent := hBounded (.mergeCall call) (by
      rw [hEvents]
      simp [hCall])
    exact hEvent
  · apply hValid (.cleanup cleanupBefore final)
    rw [hEvents]
    simp

end AccessTrace

end CPythonListsort
