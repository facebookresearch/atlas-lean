/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Code.Assembly.MergeMemoryLifecycle
import Code.Policy.MergeAtPreservation

/-!
# `merge_at` safety

This module instruments the pending-stack updates and the two trimming gallops
performed by `merge_at`, then delegates the selected merge continuation to the
already traced `merge_lo` or `merge_hi` evaluator.  The logical shrink of the
active pending array is not an indexed C access; the indexed reads and writes
which precede it are recorded in source order.
-/

namespace CPythonListsort

universe u v

variable {κ : Type u} {ν : Type v}

/-- Convert a traced `merge_lo` result to the common `merge_at` result. -/
private def mergeAtFromLo (result : MergeLoResult κ ν) : MergeAtResult κ ν :=
  { state := result.state
    returnCode := result.returnCode
    fuelExhausted := result.fuelExhausted }

/-- Convert a traced `merge_hi` result to the common `merge_at` result. -/
private def mergeAtFromHi (result : MergeHiResult κ ν) : MergeAtResult κ ν :=
  { state := result.state
    returnCode := result.returnCode
    fuelExhausted := result.fuelExhausted }

private def mergeAtSuccessResult (state : MergeState κ ν) :
    MergeAtResult κ ν :=
  { state := state, returnCode := 0, fuelExhausted := false }

private def mergeAtOutOfFuelResult (state : MergeState κ ν) :
    MergeAtResult κ ν :=
  { state := state, returnCode := -1, fuelExhausted := true }

/-- The logical pending-stack splice performed by `merge_at`.  The traced
implementation below proves that its physical write sequence computes this
state. -/
private def mergeAtCombinedState (state : MergeState κ ν) (i : Nat)
    (left right : PendingRun) : MergeState κ ν :=
  { state with
    pending :=
      (state.pending.setIfInBounds i
        { left with len := left.len + right.len }).eraseIdxIfInBounds (i + 1) }

/-- Trace the C-level pending writes which install the combined run and, on the
third-last branch, slide the uninvolved last run down one slot.  The returned
state uses the reviewed transcription's single logical splice; the preceding
typed operations establish and record the corresponding physical accesses.
-/
def mergeAtPendingUpdateTraced? (state : MergeState κ ν) (i : Nat)
    (left right : PendingRun) : TraceResult (MergeState κ ν) :=
  let combined : PendingRun := { left with len := left.len + right.len }
  let updated :=
    (TraceResult.pendingRunWrite? state (Int.ofNat i) combined).bind fun written =>
      if i + 3 = state.pending.size then
        (TraceResult.pendingRunRead? written (Int.ofNat (i + 2))).bind fun last =>
          (TraceResult.pendingRunWrite? written (Int.ofNat (i + 1)) last).map
            (fun slid =>
              { slid with pending := slid.pending.eraseIdxIfInBounds (i + 2) })
      else
        TraceResult.pure
          { written with pending := written.pending.eraseIdxIfInBounds (i + 1) }
  updated.recordSuccessPolicyEvent fun _ =>
    .merge
      { index := i
        left := RunSpan.ofPendingRun left
        right := RunSpan.ofPendingRun right }

/-- Pending-stack bookkeeping is access-instrumented but cannot emit a
top-level merge-memory boundary. -/
theorem mergeAtPendingUpdateTraced_memoryEvents_eq_nil
    (state : MergeState κ ν) (i : Nat) (left right : PendingRun) :
    (mergeAtPendingUpdateTraced? state i left right).trace.memoryEvents = [] := by
  unfold mergeAtPendingUpdateTraced?
  rw [TraceResult.memoryEvents_recordSuccessPolicyEvent]
  apply TraceResult.memoryEvents_bind_eq_nil
  · simp [TraceResult.trace_pendingRunWrite, AccessTrace.singletonAccess]
  · intro written
    split
    · apply TraceResult.memoryEvents_bind_eq_nil
      · simp [TraceResult.trace_pendingRunRead, AccessTrace.singletonAccess]
      · intro last
        simp [TraceResult.trace_pendingRunWrite, AccessTrace.singletonAccess]
    · simp [TraceResult.pure, AccessTrace.empty]

/-- Sliding the last pending run over its predecessor and then shrinking the
array is exactly the single splice used by the reviewed transcription. -/
private theorem Array.setNextFromSuccessor_eraseSuccessor
    (xs : Array α) (i : Nat) (h : i + 2 < xs.size) :
    (xs.setIfInBounds (i + 1) xs[i + 2]).eraseIdxIfInBounds (i + 2) =
      xs.eraseIdxIfInBounds (i + 1) := by
  have hiOne : i + 1 < xs.size := by omega
  rw [Array.setIfInBounds_def, dif_pos hiOne]
  have hiTwoSet : i + 2 < (xs.set (i + 1) xs[i + 2]).size := by
    simpa using h
  rw [← Array.eraseIdx_eq_eraseIdxIfInBounds hiTwoSet]
  rw [← Array.eraseIdx_eq_eraseIdxIfInBounds hiOne]
  rw [Array.eraseIdx_set_gt (by omega)]
  exact Array.set_getElem_succ_eraseIdx_succ (xs := xs) (i := i + 1) h

private theorem pendingRunRead_safe (state : MergeState κ ν) (index : Int)
    (hindex : 0 ≤ index ∧ index.toNat < state.pending.size) :
    MovementTraceSafe (TraceResult.pendingRunRead? state index) := by
  constructor
  · simp [TraceResult.trace_pendingRunRead, AccessTrace.singletonAccess]
  · simp [TraceResult.trace_pendingRunRead, AccessTrace.singletonAccess]
  · rw [TraceResult.trace_pendingRunRead]
    simpa [AccessTrace.allAccessesInBounds, AccessTrace.singletonAccess,
      AccessEvent.InBounds] using
        (show 0 ≤ index ∧ index < Int.ofNat state.pending.size from
          ⟨hindex.1, (Int.toNat_lt hindex.1).mp hindex.2⟩)
  · simp [TraceResult.trace_pendingRunRead,
      AccessTrace.tempPayloadAccessesLive, AccessTrace.singletonAccess,
      AccessEvent.TempPayloadLive]

private theorem pendingRunWrite_safe (state : MergeState κ ν) (index : Int)
    (run : PendingRun)
    (hindex : 0 ≤ index ∧ index.toNat < state.pending.size) :
    MovementTraceSafe (TraceResult.pendingRunWrite? state index run) := by
  constructor
  · simp [TraceResult.trace_pendingRunWrite, AccessTrace.singletonAccess]
  · simp [TraceResult.trace_pendingRunWrite, AccessTrace.singletonAccess]
  · rw [TraceResult.trace_pendingRunWrite]
    simpa [AccessTrace.allAccessesInBounds, AccessTrace.singletonAccess,
      AccessEvent.InBounds] using
        (show 0 ≤ index ∧ index < Int.ofNat state.pending.size from
          ⟨hindex.1, (Int.toNat_lt hindex.1).mp hindex.2⟩)
  · simp [TraceResult.trace_pendingRunWrite,
      AccessTrace.tempPayloadAccessesLive, AccessTrace.singletonAccess,
      AccessEvent.TempPayloadLive]

private theorem sortSliceKeysRead_safe (slice : SortSlice κ ν) (index : Int)
    (hindex : SortSlice.IndexInBounds slice index) :
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

/-- A policy-only success record preserves every obligation in the movement
trace safety interface. -/
private theorem movementTraceSafe_recordSuccessPolicyEvent
    (current : TraceResult α) (event : α → PolicyEvent)
    (h : MovementTraceSafe current) :
    MovementTraceSafe (current.recordSuccessPolicyEvent event) := by
  exact
    { fuel := by simpa using h.fuel
      noPushes := by simpa using h.noPushes
      bounds :=
        (TraceResult.allAccessesInBounds_recordSuccessPolicyEvent
          current event).2 h.bounds
      tempLive :=
        (TraceResult.tempPayloadAccessesLive_recordSuccessPolicyEvent
          current event).2 h.tempLive }

private theorem pendingRunRead_result_of_bounds (state : MergeState κ ν)
    (index : Nat) (hindex : index < state.pending.size) :
    (TraceResult.pendingRunRead? state (Int.ofNat index)).result =
      some state.pending[index] := by
  change (TraceResult.pendingRunRead? state (Int.ofNat index)).erase = _
  rw [TraceResult.erase_pendingRunRead]
  have hnonnegative : 0 ≤ Int.ofNat index := Int.natCast_nonneg _
  rw [if_pos hnonnegative]
  have htoi : (Int.ofNat index).toNat = index := rfl
  rw [htoi]
  exact Array.getElem?_eq_getElem hindex

private theorem pendingRunWrite_result_of_bounds (state : MergeState κ ν)
    (index : Nat) (run : PendingRun) (hindex : index < state.pending.size) :
    (TraceResult.pendingRunWrite? state (Int.ofNat index) run).result =
      some { state with pending := state.pending.setIfInBounds index run } := by
  change (TraceResult.pendingRunWrite? state (Int.ofNat index) run).erase = _
  rw [TraceResult.erase_pendingRunWrite]
  have hbounds :
      0 ≤ Int.ofNat index ∧
        (Int.ofNat index).toNat < state.pending.size := by
    exact ⟨Int.natCast_nonneg _, by simpa using hindex⟩
  rw [if_pos hbounds]
  rfl

private theorem sortSliceKeysRead_result_of_eq_some (slice : SortSlice κ ν)
    (index : Int) (entry : SortSliceEntry κ ν)
    (hread : slice.read? index = some entry) :
    (TraceResult.sortSliceKeysRead? slice index).result = some entry := by
  change (TraceResult.sortSliceKeysRead? slice index).erase = some entry
  simpa using hread

private theorem sortSlice_read_ofNat_eq_some (slice : SortSlice κ ν)
    (index : Nat) (hindex : index < slice.entries.size) :
    slice.read? (Int.ofNat index) = some slice.entries[index] := by
  rw [SortSlice.read?]
  have hnonnegative : 0 ≤ Int.ofNat index := Int.natCast_nonneg _
  rw [if_pos hnonnegative]
  have htoi : (Int.ofNat index).toNat = index := rfl
  rw [htoi]
  exact Array.getElem?_eq_getElem hindex

private theorem TraceResult.bind_result_of_eq_some
    (current : TraceResult α) (next : α → TraceResult β) (value : α)
    (hresult : current.result = some value) :
    (current.bind next).result = (next value).result := by
  change (current.bind next).erase = (next value).erase
  rw [TraceResult.erase_bind]
  change current.result.bind (fun item => (next item).result) = _
  rw [hresult]
  rfl

private theorem pySSize_slt_zero_of_nonnegative_positive (x : PySSize)
    (hnonnegative : x.Nonnegative) (hpositive : 0 < x.toNat) :
    (0 : PySSize).slt x := by
  rw [BitVec.slt_eq_decide, decide_eq_true_eq]
  have hmsb : x.msb = false := by
    simpa [PySSize.Nonnegative] using hnonnegative
  rw [BitVec.toInt_eq_toNat_of_msb hmsb]
  norm_num [BitVec.toInt_ofNat]
  exact_mod_cast hpositive

@[simp]
private theorem erase_mergeAtPendingUpdateTraced (state : MergeState κ ν)
    (i : Nat) (left right : PendingRun)
    (hposition : i + 2 = state.pending.size ∨ i + 3 = state.pending.size) :
    (mergeAtPendingUpdateTraced? state i left right).erase =
      some (mergeAtCombinedState state i left right) := by
  unfold mergeAtPendingUpdateTraced?
  rw [TraceResult.erase_recordSuccessPolicyEvent]
  rw [TraceResult.erase_bind]
  have hi : i < state.pending.size := by omega
  rw [TraceResult.erase_pendingRunWrite]
  have hwrite : 0 ≤ Int.ofNat i ∧ (Int.ofNat i).toNat < state.pending.size := by
    simpa using hi
  rw [if_pos hwrite]
  simp only [Option.bind_some]
  split
  · rename_i hthird
    rw [TraceResult.erase_bind, TraceResult.erase_pendingRunRead]
    have hiTwo : i + 2 < state.pending.size := by omega
    have hread : 0 ≤ Int.ofNat (i + 2) := Int.natCast_nonneg _
    rw [if_pos hread]
    have htoi : (Int.ofNat i).toNat = i := rfl
    have htoiTwo : (Int.ofNat (i + 2)).toNat = i + 2 := rfl
    rw [htoi, htoiTwo]
    have hiTwo' : i + 2 <
        (state.pending.setIfInBounds i
          { left with len := left.len + right.len }).size := by
      simpa using hiTwo
    rw [Array.getElem?_eq_getElem hiTwo']
    simp only [Option.bind_some, TraceResult.erase_map,
      TraceResult.erase_pendingRunWrite]
    have hiOne : i + 1 < state.pending.size := by omega
    have hiOne' : i + 1 <
        (state.pending.setIfInBounds i
          { left with len := left.len + right.len }).size := by
      simpa using hiOne
    have hwriteSecond :
        0 ≤ Int.ofNat (i + 1) ∧
          (Int.ofNat (i + 1)).toNat <
            (state.pending.setIfInBounds i
              { left with len := left.len + right.len }).size := by
      constructor
      · exact Int.natCast_nonneg _
      · simpa using hiOne'
    rw [if_pos hwriteSecond]
    simp only [Option.map_some]
    have htoiOne : (Int.ofNat (i + 1)).toNat = i + 1 := rfl
    rw [htoiOne]
    rw [Array.setNextFromSuccessor_eraseSuccessor _ _ hiTwo']
    rfl
  · rfl

/-- A source-positioned pending splice emits exactly one logical merge event,
using the full operands supplied before either trimming gallop runs. -/
theorem mergeAtPendingUpdateTraced_policyEvent
    (state : MergeState κ ν) (i : Nat) (left right : PendingRun)
    (hposition : i + 2 = state.pending.size ∨
      i + 3 = state.pending.size) :
    (mergeAtPendingUpdateTraced? state i left right).trace.policyEvents =
      [.merge
        { index := i
          left := RunSpan.ofPendingRun left
          right := RunSpan.ofPendingRun right }] := by
  let combined : PendingRun := { left with len := left.len + right.len }
  let updated : TraceResult (MergeState κ ν) :=
    (TraceResult.pendingRunWrite? state (Int.ofNat i) combined).bind fun written =>
      if i + 3 = state.pending.size then
        (TraceResult.pendingRunRead? written (Int.ofNat (i + 2))).bind fun last =>
          (TraceResult.pendingRunWrite? written (Int.ofNat (i + 1)) last).map
            (fun slid =>
              { slid with pending := slid.pending.eraseIdxIfInBounds (i + 2) })
      else
        TraceResult.pure
          { written with pending := written.pending.eraseIdxIfInBounds (i + 1) }
  let event : PolicyEvent :=
    .merge
      { index := i
        left := RunSpan.ofPendingRun left
        right := RunSpan.ofPendingRun right }
  have hresult : updated.result =
      some (mergeAtCombinedState state i left right) := by
    have herase :=
      erase_mergeAtPendingUpdateTraced state i left right hposition
    change (updated.recordSuccessPolicyEvent fun _ => event).result =
      some (mergeAtCombinedState state i left right) at herase
    simpa using herase
  have hempty : updated.trace.policyEvents = [] := by
    apply TraceResult.policyEvents_bind_eq_nil
    · simp [TraceResult.trace_pendingRunWrite, AccessTrace.singletonAccess]
    · intro written
      split
      · apply TraceResult.policyEvents_bind_eq_nil
        · simp [TraceResult.trace_pendingRunRead, AccessTrace.singletonAccess]
        · intro last
          simp [TraceResult.policyEvents_map,
            TraceResult.trace_pendingRunWrite, AccessTrace.singletonAccess]
      · simp [TraceResult.pure, AccessTrace.empty]
  change (updated.recordSuccessPolicyEvent fun _ => event).trace.policyEvents =
    [event]
  rw [TraceResult.policyEvents_recordSuccessPolicyEvent_of_eq_some
    updated _ _ hresult, hempty]
  rfl

/-- The concrete pending-stack mutation succeeds and every physical read and
write it records is in bounds. -/
private theorem mergeAtPendingUpdateTraced_safe (state : MergeState κ ν)
    (i : Nat) (left right : PendingRun)
    (hposition : i + 2 = state.pending.size ∨ i + 3 = state.pending.size) :
    MovementTraceSafe (mergeAtPendingUpdateTraced? state i left right) := by
  unfold mergeAtPendingUpdateTraced?
  apply movementTraceSafe_recordSuccessPolicyEvent
  let combined : PendingRun := { left with len := left.len + right.len }
  let written : MergeState κ ν :=
    { state with pending := state.pending.setIfInBounds i combined }
  have hi : i < state.pending.size := by omega
  have hwriteBounds :
      0 ≤ Int.ofNat i ∧ (Int.ofNat i).toNat < state.pending.size := by
    exact ⟨Int.natCast_nonneg _, by simpa using hi⟩
  have hwriteResult :
      (TraceResult.pendingRunWrite? state (Int.ofNat i) combined).result =
        some written := by
    simpa [written] using
      (pendingRunWrite_result_of_bounds state i combined hi)
  have hwriteSafe :
      MovementTraceSafe
        (TraceResult.pendingRunWrite? state (Int.ofNat i) combined) :=
    pendingRunWrite_safe state (Int.ofNat i) combined hwriteBounds
  refine MovementTraceSafe.bind _ _ written hwriteResult hwriteSafe ?_
  split
  · rename_i hthird
    have hiTwo : i + 2 < written.pending.size := by
      simp [written]
      omega
    let last := written.pending[i + 2]
    have hreadBounds :
        0 ≤ Int.ofNat (i + 2) ∧
          (Int.ofNat (i + 2)).toNat < written.pending.size := by
      constructor
      · exact Int.natCast_nonneg _
      · change i + 2 < written.pending.size
        exact hiTwo
    have hreadResult :
        (TraceResult.pendingRunRead? written (Int.ofNat (i + 2))).result =
          some last := by
      simpa [last] using
        (pendingRunRead_result_of_bounds written (i + 2) hiTwo)
    have hreadSafe :
        MovementTraceSafe
          (TraceResult.pendingRunRead? written (Int.ofNat (i + 2))) :=
      pendingRunRead_safe written (Int.ofNat (i + 2)) hreadBounds
    have hiOne : i + 1 < written.pending.size := by omega
    have hwriteSecondBounds :
        0 ≤ Int.ofNat (i + 1) ∧
          (Int.ofNat (i + 1)).toNat < written.pending.size := by
      constructor
      · exact Int.natCast_nonneg _
      · change i + 1 < written.pending.size
        exact hiOne
    have hwriteSecondSafe :
        MovementTraceSafe
          (TraceResult.pendingRunWrite? written (Int.ofNat (i + 1)) last) :=
      pendingRunWrite_safe written (Int.ofNat (i + 1)) last
        hwriteSecondBounds
    refine MovementTraceSafe.bind _ _ last hreadResult hreadSafe ?_
    exact MovementTraceSafe.map _ _ hwriteSecondSafe
  · exact MovementTraceSafe.pure _

/-- On CPython's third-last branch, the pending mutation exposes the physical
write/read/write sequence in source order.  The final logical shrink emits no
indexed event. -/
theorem mergeAtPendingUpdateTraced_thirdLast_access_order
    (state : MergeState κ ν) (i : Nat) (left right : PendingRun)
    (hthird : i + 3 = state.pending.size) :
    (mergeAtPendingUpdateTraced? state i left right).trace.accesses =
      [{ kind := .write, region := .pendingRuns,
          index := Int.ofNat i, extent := state.pending.size },
       { kind := .read, region := .pendingRuns,
          index := Int.ofNat (i + 2), extent := state.pending.size },
       { kind := .write, region := .pendingRuns,
          index := Int.ofNat (i + 1), extent := state.pending.size }] := by
  unfold mergeAtPendingUpdateTraced?
  rw [TraceResult.accesses_recordSuccessPolicyEvent]
  let combined : PendingRun := { left with len := left.len + right.len }
  let written : MergeState κ ν :=
    { state with pending := state.pending.setIfInBounds i combined }
  have hi : i < state.pending.size := by omega
  have hwriteResult :
      (TraceResult.pendingRunWrite? state (Int.ofNat i) combined).result =
        some written := by
    simpa [written] using
      pendingRunWrite_result_of_bounds state i combined hi
  rw [TraceResult.trace_bind, hwriteResult]
  dsimp only
  rw [if_pos hthird]
  have hiTwo : i + 2 < written.pending.size := by
    simp [written]
    omega
  let last := written.pending[i + 2]
  have hreadResult :
      (TraceResult.pendingRunRead? written
        (Int.ofNat (i + 2))).result = some last := by
    simpa [last] using
      pendingRunRead_result_of_bounds written (i + 2) hiTwo
  rw [TraceResult.trace_bind, hreadResult]
  simp [TraceResult.trace_pendingRunRead,
    TraceResult.trace_pendingRunWrite, TraceResult.map,
    AccessTrace.compose, AccessTrace.singletonAccess, written]

/-- On the top-pair branch, the pending mutation performs only the combined
run write; shrinking the logical pending array is not an indexed access. -/
theorem mergeAtPendingUpdateTraced_topPair_access_order
    (state : MergeState κ ν) (i : Nat) (left right : PendingRun)
    (htop : i + 2 = state.pending.size) :
    (mergeAtPendingUpdateTraced? state i left right).trace.accesses =
      [{ kind := .write, region := .pendingRuns,
          index := Int.ofNat i, extent := state.pending.size }] := by
  unfold mergeAtPendingUpdateTraced?
  rw [TraceResult.accesses_recordSuccessPolicyEvent]
  let combined : PendingRun := { left with len := left.len + right.len }
  let written : MergeState κ ν :=
    { state with pending := state.pending.setIfInBounds i combined }
  have hi : i < state.pending.size := by omega
  have hnotThird : ¬ i + 3 = state.pending.size := by omega
  have hwriteResult :
      (TraceResult.pendingRunWrite? state (Int.ofNat i) combined).result =
        some written := by
    simpa [written] using
      pendingRunWrite_result_of_bounds state i combined hi
  rw [TraceResult.trace_bind, hwriteResult]
  dsimp only
  rw [if_neg hnotThird]
  simp [TraceResult.trace_pendingRunWrite, TraceResult.pure,
    AccessTrace.empty, AccessTrace.compose, AccessTrace.singletonAccess,
    written]

private def mergeAtAfterTrimBTraced (call : MergeState κ ν)
    (left right : PendingRun) (firstB lastA : SortSliceEntry κ ν)
    (trimA trimB : GallopResult) : TraceResult (MergeAtPreparation κ ν) :=
  if trimB.fuelExhausted then
    TraceResult.pure (.finished (mergeAtOutOfFuelResult call))
  else if right.len.toNat < trimB.index then
    TraceResult.failure
  else
    let ssa := left.base + trimA.index
    let na := left.len.toNat - trimA.index
    let nb := trimB.index
    if nb = 0 then
      TraceResult.pure (.finished (mergeAtSuccessResult call))
    else if na ≤ nb then
      TraceResult.pure (.mergeLo
        { state := call
          ssa := Int.ofNat ssa
          ssb := Int.ofNat right.base
          na := na
          nb := nb
          left := left
          right := right
          firstB := firstB
          lastA := lastA
          trimA := trimA
          trimB := trimB })
    else
      TraceResult.pure (.mergeHi
        { state := call
          ssa := Int.ofNat ssa
          ssb := Int.ofNat right.base
          na := na
          nb := nb
          left := left
          right := right
          firstB := firstB
          lastA := lastA
          trimA := trimA
          trimB := trimB })

private def mergeAtAfterTrimATraced (call : MergeState κ ν)
    (left right : PendingRun) (firstB : SortSliceEntry κ ν)
    (trimA : GallopResult) : TraceResult (MergeAtPreparation κ ν) :=
  if trimA.fuelExhausted then
    TraceResult.pure (.finished (mergeAtOutOfFuelResult call))
  else if left.len.toNat < trimA.index then
    TraceResult.failure
  else
    let ssa := left.base + trimA.index
    let na := left.len.toNat - trimA.index
    if na = 0 then
      TraceResult.pure (.finished (mergeAtSuccessResult call))
    else
      (TraceResult.sortSliceKeysRead? call.data
        (Int.ofNat (ssa + na - 1))).bind fun lastA =>
        (gallopLeftTraced? call
          (.main call.data (Int.ofNat right.base)) lastA.key
          right.len.toNat (right.len.toNat - 1)).bind fun trimB =>
          mergeAtAfterTrimBTraced call left right firstB lastA trimA trimB

private theorem mergeAtAfterTrimBTraced_memoryEvents_eq_nil
    (call : MergeState κ ν) (left right : PendingRun)
    (firstB lastA : SortSliceEntry κ ν) (trimA trimB : GallopResult) :
    (mergeAtAfterTrimBTraced call left right firstB lastA trimA
      trimB).trace.memoryEvents = [] := by
  unfold mergeAtAfterTrimBTraced
  split
  · rfl
  split
  · rfl
  dsimp only
  split
  · rfl
  split <;> rfl

private theorem mergeAtAfterTrimATraced_memoryEvents_eq_nil
    (call : MergeState κ ν) (left right : PendingRun)
    (firstB : SortSliceEntry κ ν) (trimA : GallopResult) :
    (mergeAtAfterTrimATraced call left right firstB trimA).trace.memoryEvents =
      [] := by
  unfold mergeAtAfterTrimATraced
  split
  · rfl
  split
  · rfl
  dsimp only
  split
  · rfl
  · apply TraceResult.memoryEvents_bind_eq_nil
    · simp [TraceResult.trace_sortSliceKeysRead,
        AccessTrace.singletonAccess]
    · intro lastA
      apply TraceResult.memoryEvents_bind_eq_nil
      · exact gallopLeftTraced_memoryEvents_eq_nil _ _ _ _ _
      · intro trimB
        exact mergeAtAfterTrimBTraced_memoryEvents_eq_nil _ _ _ _ _ _ _

/-- The second trimming tail cannot emit a logical run-policy event. -/
private theorem mergeAtAfterTrimBTraced_policyEvents_eq_nil
    (call : MergeState κ ν) (left right : PendingRun)
    (firstB lastA : SortSliceEntry κ ν) (trimA trimB : GallopResult) :
    (mergeAtAfterTrimBTraced call left right firstB lastA trimA
      trimB).trace.policyEvents = [] := by
  unfold mergeAtAfterTrimBTraced
  split
  · rfl
  split
  · rfl
  dsimp only
  split
  · rfl
  split <;> rfl

/-- Endpoint reads and both trimming gallops are policy-event-free.  Hence
the pending-stack update remains the sole logical event of `merge_at`. -/
private theorem mergeAtAfterTrimATraced_policyEvents_eq_nil
    (call : MergeState κ ν) (left right : PendingRun)
    (firstB : SortSliceEntry κ ν) (trimA : GallopResult) :
    (mergeAtAfterTrimATraced call left right firstB trimA).trace.policyEvents =
      [] := by
  unfold mergeAtAfterTrimATraced
  split
  · rfl
  split
  · rfl
  dsimp only
  split
  · rfl
  · apply TraceResult.policyEvents_bind_eq_nil
    · simp [TraceResult.trace_sortSliceKeysRead,
        AccessTrace.singletonAccess]
    · intro lastA
      apply TraceResult.policyEvents_bind_eq_nil
      · exact gallopLeftTraced_policyEvents_eq_nil _ _ _ _ _
      · intro trimB
        exact mergeAtAfterTrimBTraced_policyEvents_eq_nil _ _ _ _ _ _ _

private structure MergeAtTailSafetyPost (call : MergeState κ ν)
    (execution : TraceResult (MergeAtPreparation κ ν))
    (prepared : MergeAtPreparation κ ν) : Prop where
  resultEq : execution.result = some prepared
  traceSafe : MovementTraceSafe execution
  finishedSuccess : ∀ result, prepared = .finished result →
    result.returnCode = 0 ∧ result.fuelExhausted = false
  stateEq : prepared.state = call

private theorem mergeAtAfterTrimBTraced_safe (call : MergeState κ ν)
    (left right : PendingRun) (firstB lastA : SortSliceEntry κ ν)
    (trimA trimB : GallopResult)
    (hfuel : trimB.fuelExhausted = false)
    (hbound : trimB.index ≤ right.len.toNat) :
    ∃ prepared,
      MergeAtTailSafetyPost call
        (mergeAtAfterTrimBTraced call left right firstB lastA trimA trimB)
        prepared := by
  have hnotPast : ¬ right.len.toNat < trimB.index := by omega
  by_cases hzero : trimB.index = 0
  · let prepared : MergeAtPreparation κ ν :=
      .finished (mergeAtSuccessResult call)
    refine ⟨prepared, ?_⟩
    constructor
    · change (mergeAtAfterTrimBTraced call left right firstB lastA trimA trimB).erase = _
      simp [mergeAtAfterTrimBTraced, hfuel, hzero, prepared]
    · simpa [mergeAtAfterTrimBTraced, hfuel, hnotPast, hzero, prepared]
        using MovementTraceSafe.pure prepared
    · intro result hresult
      change MergeAtPreparation.finished (mergeAtSuccessResult call) =
        MergeAtPreparation.finished result at hresult
      cases hresult
      exact ⟨rfl, rfl⟩
    · rfl
  · by_cases hshorter : left.len.toNat - trimA.index ≤ trimB.index
    · let callsite : MergeAtCall κ ν :=
        { state := call
          ssa := Int.ofNat (left.base + trimA.index)
          ssb := Int.ofNat right.base
          na := left.len.toNat - trimA.index
          nb := trimB.index
          left := left
          right := right
          firstB := firstB
          lastA := lastA
          trimA := trimA
          trimB := trimB }
      let prepared : MergeAtPreparation κ ν := .mergeLo callsite
      refine ⟨prepared, ?_⟩
      constructor
      · change (mergeAtAfterTrimBTraced call left right firstB lastA trimA trimB).erase = _
        simp [mergeAtAfterTrimBTraced, hfuel, hnotPast, hzero, hshorter, prepared,
          callsite]
      · simpa [mergeAtAfterTrimBTraced, hfuel, hnotPast, hzero, hshorter,
          prepared, callsite] using MovementTraceSafe.pure prepared
      · intro result hresult
        change MergeAtPreparation.mergeLo callsite =
          MergeAtPreparation.finished result at hresult
        cases hresult
      · rfl
    · let callsite : MergeAtCall κ ν :=
        { state := call
          ssa := Int.ofNat (left.base + trimA.index)
          ssb := Int.ofNat right.base
          na := left.len.toNat - trimA.index
          nb := trimB.index
          left := left
          right := right
          firstB := firstB
          lastA := lastA
          trimA := trimA
          trimB := trimB }
      let prepared : MergeAtPreparation κ ν := .mergeHi callsite
      refine ⟨prepared, ?_⟩
      constructor
      · change (mergeAtAfterTrimBTraced call left right firstB lastA trimA trimB).erase = _
        simp [mergeAtAfterTrimBTraced, hfuel, hnotPast, hzero, hshorter, prepared,
          callsite]
      · simpa [mergeAtAfterTrimBTraced, hfuel, hnotPast, hzero, hshorter,
          prepared, callsite] using MovementTraceSafe.pure prepared
      · intro result hresult
        change MergeAtPreparation.mergeHi callsite =
          MergeAtPreparation.finished result at hresult
        cases hresult
      · rfl

private theorem mergeAtAfterTrimATraced_safe (call : MergeState κ ν)
    (left right : PendingRun) (firstB : SortSliceEntry κ ν)
    (trimA : GallopResult)
    (hleftEnd : left.base + left.len.toNat ≤ call.data.entries.size)
    (hrightEnd : right.base + right.len.toNat ≤ call.data.entries.size)
    (hrightPositive : 0 < right.len.toNat)
    (hrightMax : right.len.toNat ≤ PY_LIST_MAX)
    (hfuel : trimA.fuelExhausted = false)
    (hbound : trimA.index ≤ left.len.toNat) :
    ∃ prepared,
      MergeAtTailSafetyPost call
        (mergeAtAfterTrimATraced call left right firstB trimA) prepared := by
  have hnotPast : ¬ left.len.toNat < trimA.index := by omega
  let ssa := left.base + trimA.index
  let na := left.len.toNat - trimA.index
  by_cases hzero : na = 0
  · let prepared : MergeAtPreparation κ ν :=
      .finished (mergeAtSuccessResult call)
    refine ⟨prepared, ?_⟩
    constructor
    · change (mergeAtAfterTrimATraced call left right firstB trimA).erase = _
      simp [mergeAtAfterTrimATraced, hfuel, hnotPast, hzero, na, prepared]
    · simpa [mergeAtAfterTrimATraced, hfuel, hnotPast, hzero, na,
        prepared] using MovementTraceSafe.pure prepared
    · intro result hresult
      change MergeAtPreparation.finished (mergeAtSuccessResult call) =
        MergeAtPreparation.finished result at hresult
      cases hresult
      exact ⟨rfl, rfl⟩
    · rfl
  · let lastIndex := ssa + na - 1
    have hlastIndex : lastIndex < call.data.entries.size := by
      dsimp [lastIndex, ssa, na]
      omega
    let lastA := call.data.entries[lastIndex]
    have hlastRead :
        call.data.read? (Int.ofNat lastIndex) = some lastA := by
      simpa [lastA] using
        sortSlice_read_ofNat_eq_some call.data lastIndex hlastIndex
    have hlastResult :
        (TraceResult.sortSliceKeysRead? call.data
          (Int.ofNat lastIndex)).result = some lastA :=
      sortSliceKeysRead_result_of_eq_some call.data (Int.ofNat lastIndex)
        lastA hlastRead
    have hlastBounds :
        SortSlice.IndexInBounds call.data (Int.ofNat lastIndex) := by
      constructor
      · exact Int.natCast_nonneg _
      · exact Int.ofNat_lt.mpr hlastIndex
    have hlastSafe :
        MovementTraceSafe
          (TraceResult.sortSliceKeysRead? call.data
            (Int.ofNat lastIndex)) :=
      sortSliceKeysRead_safe call.data (Int.ofNat lastIndex) hlastBounds
    have hrightValid :
        (GallopKeySource.main call.data
          (Int.ofNat right.base)).ValidRange right.len.toNat :=
      GallopKeySource.main_validRange_of_base_add_le call.data right.base
        right.len.toNat hrightEnd
    rcases gallopLeft_main_safe call call.data (Int.ofNat right.base)
        lastA.key right.len.toNat (right.len.toNat - 1) hrightValid
        hrightPositive (by omega) hrightMax with
      ⟨trimB, htrimBResult, htrimBFuel, htrimBBound, htraceFuel,
        htracePushes, htraceBounds, htraceLive, _htrimBErase⟩
    have htrimBSafe : MovementTraceSafe
        (gallopLeftTraced? call
          (.main call.data (Int.ofNat right.base)) lastA.key
          right.len.toNat (right.len.toNat - 1)) :=
      ⟨htraceFuel, htracePushes, htraceBounds, htraceLive⟩
    rcases mergeAtAfterTrimBTraced_safe call left right firstB lastA
        trimA trimB htrimBFuel htrimBBound with ⟨prepared, htail⟩
    have hgallopChainSafe : MovementTraceSafe
        ((gallopLeftTraced? call
          (.main call.data (Int.ofNat right.base)) lastA.key
          right.len.toNat (right.len.toNat - 1)).bind fun trimB =>
            mergeAtAfterTrimBTraced call left right firstB lastA trimA trimB) :=
      MovementTraceSafe.bind _ _ trimB htrimBResult htrimBSafe htail.traceSafe
    have hreadChainSafe : MovementTraceSafe
        ((TraceResult.sortSliceKeysRead? call.data
          (Int.ofNat lastIndex)).bind fun lastA =>
            (gallopLeftTraced? call
              (.main call.data (Int.ofNat right.base)) lastA.key
              right.len.toNat (right.len.toNat - 1)).bind fun trimB =>
                mergeAtAfterTrimBTraced call left right firstB lastA trimA
                  trimB) :=
      MovementTraceSafe.bind _ _ lastA hlastResult hlastSafe
        hgallopChainSafe
    have hgallopChainResult :
        ((gallopLeftTraced? call
          (.main call.data (Int.ofNat right.base)) lastA.key
          right.len.toNat (right.len.toNat - 1)).bind fun trimB =>
            mergeAtAfterTrimBTraced call left right firstB lastA trimA trimB).result =
          some prepared := by
      change
        ((gallopLeftTraced? call
          (.main call.data (Int.ofNat right.base)) lastA.key
          right.len.toNat (right.len.toNat - 1)).bind fun trimB =>
            mergeAtAfterTrimBTraced call left right firstB lastA trimA
              trimB).erase = some prepared
      rw [TraceResult.erase_bind]
      have htrimBErase :
          (gallopLeftTraced? call
            (.main call.data (Int.ofNat right.base)) lastA.key
            right.len.toNat (right.len.toNat - 1)).erase = some trimB := by
        simpa [TraceResult.erase] using htrimBResult
      rw [htrimBErase]
      change (mergeAtAfterTrimBTraced call left right firstB lastA trimA
        trimB).erase = some prepared
      simpa [TraceResult.erase] using htail.resultEq
    have hreadChainResult :
        ((TraceResult.sortSliceKeysRead? call.data
          (Int.ofNat lastIndex)).bind fun lastA =>
            (gallopLeftTraced? call
              (.main call.data (Int.ofNat right.base)) lastA.key
              right.len.toNat (right.len.toNat - 1)).bind fun trimB =>
                mergeAtAfterTrimBTraced call left right firstB lastA trimA
                  trimB).result = some prepared := by
      change
        ((TraceResult.sortSliceKeysRead? call.data
          (Int.ofNat lastIndex)).bind fun lastA =>
            (gallopLeftTraced? call
              (.main call.data (Int.ofNat right.base)) lastA.key
              right.len.toNat (right.len.toNat - 1)).bind fun trimB =>
                mergeAtAfterTrimBTraced call left right firstB lastA trimA
                  trimB).erase = some prepared
      rw [TraceResult.erase_bind]
      have hlastErase :
          (TraceResult.sortSliceKeysRead? call.data
            (Int.ofNat lastIndex)).erase = some lastA := by
        simpa [TraceResult.erase] using hlastResult
      rw [hlastErase]
      simpa [TraceResult.erase] using hgallopChainResult
    refine ⟨prepared, ?_⟩
    constructor
    · simpa [mergeAtAfterTrimATraced, hfuel, hnotPast, hzero, ssa, na,
        lastIndex] using hreadChainResult
    · simpa [mergeAtAfterTrimATraced, hfuel, hnotPast, hzero, ssa, na,
        lastIndex] using hreadChainSafe
    · exact htail.finishedSuccess
    · exact htail.stateEq

/-- Traced prefix of `merge_at`: pending-stack selection and mutation, both
endpoint reads, both trimming gallops, and the final dispatch decision. -/
def prepareMergeAtTraced? (state : MergeState κ ν) (i : Nat) :
    TraceResult (MergeAtPreparation κ ν) :=
  if 2 ≤ state.pending.size ∧
      (i + 2 = state.pending.size ∨ i + 3 = state.pending.size) then
    (TraceResult.pendingRunRead? state (Int.ofNat i)).bind fun left =>
      (TraceResult.pendingRunRead? state (Int.ofNat (i + 1))).bind fun right =>
        if (0 : PySSize).slt left.len ∧ (0 : PySSize).slt right.len ∧
            left.base + left.len.toNat = right.base then
          (mergeAtPendingUpdateTraced? state i left right).bind fun call =>
            (TraceResult.sortSliceKeysRead? call.data
              (Int.ofNat right.base)).bind fun firstB =>
              (gallopRightTraced? call
                (.main call.data (Int.ofNat left.base)) firstB.key
                left.len.toNat 0).bind fun trimA =>
                mergeAtAfterTrimATraced call left right firstB trimA
        else
          TraceResult.failure
  else
    TraceResult.failure

/-- The trimming and pending-update prefix is memory-history free.  Therefore
the only merge-memory call event in a completed `merge_at` trace is the one
appended by its selected directional continuation. -/
theorem prepareMergeAtTraced_memoryEvents_eq_nil
    (state : MergeState κ ν) (i : Nat) :
    (prepareMergeAtTraced? state i).trace.memoryEvents = [] := by
  unfold prepareMergeAtTraced?
  split
  · apply TraceResult.memoryEvents_bind_eq_nil
    · simp [TraceResult.trace_pendingRunRead, AccessTrace.singletonAccess]
    · intro left
      apply TraceResult.memoryEvents_bind_eq_nil
      · simp [TraceResult.trace_pendingRunRead, AccessTrace.singletonAccess]
      · intro right
        split
        · apply TraceResult.memoryEvents_bind_eq_nil
          · exact mergeAtPendingUpdateTraced_memoryEvents_eq_nil _ _ _ _
          · intro call
            apply TraceResult.memoryEvents_bind_eq_nil
            · simp [TraceResult.trace_sortSliceKeysRead,
                AccessTrace.singletonAccess]
            · intro firstB
              apply TraceResult.memoryEvents_bind_eq_nil
              · exact gallopRightTraced_memoryEvents_eq_nil _ _ _ _ _
              · intro trimA
                exact mergeAtAfterTrimATraced_memoryEvents_eq_nil _ _ _ _ _
        · rfl
  · rfl

/-- On every source-admitted layout, the complete preparation prefix emits
exactly the one logical merge event attached to the concrete pending splice.
The event names the adjacent operands as they existed before either trimming
gallop, including preparations which later return early. -/
theorem prepareMergeAtTraced_policyEvent
    (state : MergeState κ ν) (scanned i : Nat) (left right : PendingRun)
    (hlayout : PendingLayout state scanned)
    (hposition : i + 2 = state.pending.size ∨
      i + 3 = state.pending.size)
    (hleft : state.pending[i]? = some left)
    (hright : state.pending[i + 1]? = some right) :
    (prepareMergeAtTraced? state i).trace.policyEvents =
      [.merge
        { index := i
          left := RunSpan.ofPendingRun left
          right := RunSpan.ofPendingRun right }] := by
  have houter :
      2 ≤ state.pending.size ∧
        (i + 2 = state.pending.size ∨ i + 3 = state.pending.size) := by
    omega
  have hleftResult :
      (TraceResult.pendingRunRead? state (Int.ofNat i)).result =
        some left := by
    change (TraceResult.pendingRunRead? state (Int.ofNat i)).erase = some left
    rw [TraceResult.erase_pendingRunRead]
    have hnonnegative : 0 ≤ Int.ofNat i := Int.natCast_nonneg _
    rw [if_pos hnonnegative]
    have htoi : (Int.ofNat i).toNat = i := rfl
    rw [htoi]
    exact hleft
  have hrightResult :
      (TraceResult.pendingRunRead? state (Int.ofNat (i + 1))).result =
        some right := by
    change
      (TraceResult.pendingRunRead? state
        (Int.ofNat (i + 1))).erase = some right
    rw [TraceResult.erase_pendingRunRead]
    have hnonnegative : 0 ≤ Int.ofNat (i + 1) := Int.natCast_nonneg _
    rw [if_pos hnonnegative]
    have htoi : (Int.ofNat (i + 1)).toNat = i + 1 := rfl
    rw [htoi]
    exact hright
  have hgeometry := hlayout.adjacentPair_geometry hleft hright
  have hadjacent : left.base + left.len.toNat = right.base := by
    simpa [PendingRun.endIndex] using hgeometry.adjacent
  have hguard :
      (0 : PySSize).slt left.len ∧ (0 : PySSize).slt right.len ∧
        left.base + left.len.toNat = right.base :=
    ⟨pySSize_slt_zero_of_nonnegative_positive left.len
        hgeometry.leftNonnegative hgeometry.leftPositive,
      pySSize_slt_zero_of_nonnegative_positive right.len
        hgeometry.rightNonnegative hgeometry.rightPositive,
      hadjacent⟩
  let call := mergeAtCombinedState state i left right
  have hupdateResult :
      (mergeAtPendingUpdateTraced? state i left right).result = some call := by
    change (mergeAtPendingUpdateTraced? state i left right).erase = some call
    simpa [call] using
      erase_mergeAtPendingUpdateTraced state i left right hposition
  have htailFree : ∀ firstB,
      ((gallopRightTraced? call
          (.main call.data (Int.ofNat left.base)) firstB.key
          left.len.toNat 0).bind fun trimA =>
            mergeAtAfterTrimATraced call left right firstB trimA).trace.policyEvents =
        [] := by
    intro firstB
    apply TraceResult.policyEvents_bind_eq_nil
    · exact gallopRightTraced_policyEvents_eq_nil _ _ _ _ _
    · intro trimA
      exact mergeAtAfterTrimATraced_policyEvents_eq_nil _ _ _ _ _
  have hafterUpdateFree :
      ((TraceResult.sortSliceKeysRead? call.data
          (Int.ofNat right.base)).bind fun firstB =>
            (gallopRightTraced? call
              (.main call.data (Int.ofNat left.base)) firstB.key
              left.len.toNat 0).bind fun trimA =>
                mergeAtAfterTrimATraced call left right firstB
                  trimA).trace.policyEvents = [] := by
    apply TraceResult.policyEvents_bind_eq_nil
    · simp [TraceResult.trace_sortSliceKeysRead,
        AccessTrace.singletonAccess]
    · exact htailFree
  unfold prepareMergeAtTraced?
  rw [if_pos houter]
  rw [TraceResult.policyEvents_bind, hleftResult]
  simp only [TraceResult.trace_pendingRunRead, AccessTrace.singletonAccess,
    List.nil_append]
  rw [TraceResult.policyEvents_bind, hrightResult]
  simp only [TraceResult.trace_pendingRunRead, AccessTrace.singletonAccess,
    List.nil_append]
  rw [if_pos hguard]
  rw [TraceResult.policyEvents_bind, hupdateResult]
  rw [mergeAtPendingUpdateTraced_policyEvent state i left right hposition]
  simpa [call] using hafterUpdateFree

/-- The exact source-order trace prefix on a preparation path which reaches a
merge continuation.  The first gallop's result determines the last-A endpoint
read used to start the second gallop. -/
def mergeAtPreparationDispatchTrace (pre : MergeState κ ν) (i : Nat)
    (call : MergeAtCall κ ν) : AccessTrace :=
  (TraceResult.pendingRunRead? pre (Int.ofNat i)).trace.compose
    ((TraceResult.pendingRunRead? pre (Int.ofNat (i + 1))).trace.compose
      ((mergeAtPendingUpdateTraced? pre i call.left call.right).trace.compose
        ((TraceResult.sortSliceKeysRead? call.state.data
          (Int.ofNat call.right.base)).trace.compose
          ((gallopRightTraced? call.state
            (.main call.state.data (Int.ofNat call.left.base)) call.firstB.key
            call.left.len.toNat 0).trace.compose
            ((TraceResult.sortSliceKeysRead? call.state.data
              (Int.ofNat (call.left.base + call.trimA.index + call.na - 1))).trace.compose
              (gallopLeftTraced? call.state
                (.main call.state.data (Int.ofNat call.right.base)) call.lastA.key
                call.right.len.toNat (call.right.len.toNat - 1)).trace)))))

set_option maxHeartbeats 5000000 in
-- The proof follows every nested bind and early-return guard in both dispatch branches.
set_option linter.flexible false in
/-- Every successful non-early preparation trace contains the two trimming
gallops in source order: the right gallop, the last-A endpoint read selected by
its result, and then the left gallop.  The equality also fixes all preceding
pending-stack and first-B observations. -/
theorem prepareMergeAtTraced_dispatch_trace
    (pre : MergeState κ ν) (i : Nat) (call : MergeAtCall κ ν)
    (hdispatch :
      (prepareMergeAtTraced? pre i).result = some (.mergeLo call) ∨
        (prepareMergeAtTraced? pre i).result = some (.mergeHi call)) :
    (prepareMergeAtTraced? pre i).trace =
      mergeAtPreparationDispatchTrace pre i call := by
  rcases hdispatch with hresult | hresult
  all_goals
    simp only [prepareMergeAtTraced?, TraceResult.bind,
      mergeAtAfterTrimATraced, mergeAtAfterTrimBTraced] at hresult
  all_goals try split at hresult <;> try simp at hresult
  all_goals try split at hresult <;> try simp at hresult
  all_goals try split at hresult <;> try simp at hresult
  all_goals try split at hresult <;> try simp at hresult
  all_goals try split at hresult <;> try simp at hresult
  all_goals try split at hresult <;> try simp at hresult
  all_goals try split at hresult <;> try simp at hresult
  all_goals try split at hresult <;> try simp at hresult
  all_goals try split at hresult <;> try simp at hresult
  all_goals try split at hresult <;> try simp at hresult
  all_goals try split at hresult <;> try simp at hresult
  all_goals try split at hresult <;> try simp at hresult
  all_goals try split at hresult <;> try simp at hresult
  all_goals try split at hresult <;> try simp at hresult
  all_goals try split at hresult <;> try simp at hresult
  all_goals try split at hresult <;> try simp at hresult
  all_goals try cases hresult
  all_goals
    simp_all [prepareMergeAtTraced?, mergeAtPreparationDispatchTrace,
      mergeAtAfterTrimATraced, mergeAtAfterTrimBTraced,
      TraceResult.bind, TraceResult.pure, TraceResult.failure]
  all_goals split <;> simp_all
  all_goals try omega
  all_goals split <;> simp_all
  all_goals split <;> simp_all

/-- For every source-admitted position and layout, the preparation trace
starts with the two selected-run reads followed by the concrete pending-update
events.  Later endpoint and gallop events can only extend this prefix. -/
theorem prepareMergeAtTraced_pending_access_prefix
    (state : MergeState κ ν) (scanned i : Nat) (left right : PendingRun)
    (hlayout : PendingLayout state scanned)
    (hposition : i + 2 = state.pending.size ∨
      i + 3 = state.pending.size)
    (hleft : state.pending[i]? = some left)
    (hright : state.pending[i + 1]? = some right) :
    List.IsPrefix
      ([{ kind := .read, region := .pendingRuns,
            index := Int.ofNat i, extent := state.pending.size },
         { kind := .read, region := .pendingRuns,
            index := Int.ofNat (i + 1), extent := state.pending.size }] ++
        (mergeAtPendingUpdateTraced? state i left right).trace.accesses)
      (prepareMergeAtTraced? state i).trace.accesses := by
  have houter :
      2 ≤ state.pending.size ∧
        (i + 2 = state.pending.size ∨ i + 3 = state.pending.size) := by
    omega
  have hleftResult :
      (TraceResult.pendingRunRead? state (Int.ofNat i)).result =
        some left := by
    change (TraceResult.pendingRunRead? state (Int.ofNat i)).erase = some left
    rw [TraceResult.erase_pendingRunRead]
    have hnonnegative : 0 ≤ Int.ofNat i := Int.natCast_nonneg _
    rw [if_pos hnonnegative]
    simpa using hleft
  have hrightResult :
      (TraceResult.pendingRunRead? state
        (Int.ofNat (i + 1))).result = some right := by
    change
      (TraceResult.pendingRunRead? state
        (Int.ofNat (i + 1))).erase = some right
    rw [TraceResult.erase_pendingRunRead]
    have hnonnegative : 0 ≤ Int.ofNat (i + 1) := Int.natCast_nonneg _
    rw [if_pos hnonnegative]
    simpa using hright
  have hgeometry := hlayout.adjacentPair_geometry hleft hright
  have hadjacent : left.base + left.len.toNat = right.base := by
    simpa [PendingRun.endIndex] using hgeometry.adjacent
  have hguard :
      (0 : PySSize).slt left.len ∧
        (0 : PySSize).slt right.len ∧
        left.base + left.len.toNat = right.base :=
    ⟨pySSize_slt_zero_of_nonnegative_positive left.len
        hgeometry.leftNonnegative hgeometry.leftPositive,
      pySSize_slt_zero_of_nonnegative_positive right.len
        hgeometry.rightNonnegative hgeometry.rightPositive,
      hadjacent⟩
  let call := mergeAtCombinedState state i left right
  have hupdateResult :
      (mergeAtPendingUpdateTraced? state i left right).result = some call := by
    change (mergeAtPendingUpdateTraced? state i left right).erase = some call
    simpa [call] using
      erase_mergeAtPendingUpdateTraced state i left right hposition
  unfold prepareMergeAtTraced?
  rw [if_pos houter]
  rw [TraceResult.trace_bind, hleftResult]
  dsimp only
  rw [TraceResult.trace_bind, hrightResult]
  dsimp only
  rw [if_pos hguard]
  rw [TraceResult.trace_bind, hupdateResult]
  dsimp only
  simp only [TraceResult.trace_pendingRunRead, AccessTrace.compose,
    AccessTrace.singletonAccess]
  exact List.prefix_append _ _

set_option maxHeartbeats 5000000 in
-- The proof follows both nested gallops and every early-return branch in lockstep.
set_option linter.flexible false in
set_option maxRecDepth 10000 in
/-- Forgetting the trace of the preparation prefix recovers the reviewed
transcription exactly. -/
@[simp]
theorem erase_prepareMergeAtTraced (state : MergeState κ ν) (i : Nat) :
    (prepareMergeAtTraced? state i).erase = prepareMergeAt? state i := by
  unfold prepareMergeAtTraced? prepareMergeAt?
  split
  · rename_i hposition
    have hi : i < state.pending.size := by omega
    have hiOne : i + 1 < state.pending.size := by omega
    let left := state.pending[i]
    have hleft : state.pending[i]? = some left :=
      Array.getElem?_eq_getElem hi
    rw [TraceResult.erase_bind, TraceResult.erase_pendingRunRead]
    have hiNonnegative : 0 ≤ Int.ofNat i := Int.natCast_nonneg _
    rw [if_pos hiNonnegative]
    have htoi : (Int.ofNat i).toNat = i := rfl
    rw [htoi, hleft]
    simp only [Option.bind_some, mergeAt_bindOptionAcross_some]
    let right := state.pending[i + 1]
    have hright : state.pending[i + 1]? = some right :=
      Array.getElem?_eq_getElem hiOne
    rw [TraceResult.erase_bind, TraceResult.erase_pendingRunRead]
    have hiOneNonnegative : 0 ≤ Int.ofNat (i + 1) := Int.natCast_nonneg _
    rw [if_pos hiOneNonnegative]
    have htoiOne : (Int.ofNat (i + 1)).toNat = i + 1 := rfl
    rw [htoiOne, hright]
    simp only [Option.bind_some, mergeAt_bindOptionAcross_some]
    split
    · rename_i hadjacent
      rw [TraceResult.erase_bind,
        erase_mergeAtPendingUpdateTraced state i left right hposition.2]
      simp only [Option.bind_some, combinePendingAt_eq]
      simp only [mergeAtCombinedState]
      rw [TraceResult.erase_bind, TraceResult.erase_sortSliceKeysRead]
      cases hfirstB : state.data.read? (Int.ofNat right.base) with
      | none => simp
      | some firstB =>
      simp only [Option.bind_some]
      rw [TraceResult.erase_bind, erase_gallopRightTraced_main]
      cases htrimA :
          gallopRight?
            { state with
              pending :=
                (state.pending.setIfInBounds i
                  { left with len := left.len + right.len }).eraseIdxIfInBounds
                    (i + 1) }
            state.data (Int.ofNat left.base) firstB.key left.len.toNat 0 with
      | none => simp
      | some trimA =>
      simp only [Option.bind_some, mergeAt_bindOptionAcross_some,
        mergeAtOutOfFuel_eq, mergeAtSuccess_eq]
      unfold mergeAtAfterTrimATraced
      split <;> try simp [mergeAtOutOfFuelResult]
      split <;> try simp
      split <;> try simp [mergeAtSuccessResult]
      cases hlastA : state.data.read?
          (Int.ofNat (left.base + trimA.index +
            (left.len.toNat - trimA.index) - 1)) with
      | none => simp
      | some lastA =>
      simp only [Option.bind_some]
      rw [gallopLeftFromSource_main]
      cases htrimB :
          gallopLeft?
            { state with
              pending :=
                (state.pending.setIfInBounds i
                  { left with len := left.len + right.len }).eraseIdxIfInBounds
                    (i + 1) }
            state.data (Int.ofNat right.base) lastA.key right.len.toNat
              (right.len.toNat - 1) with
      | none => simp
      | some trimB =>
      simp only [Option.bind_some, mergeAt_bindOptionAcross_some]
      unfold mergeAtAfterTrimBTraced
      split <;> try simp [mergeAtOutOfFuelResult]
      split <;> try simp
      split <;> try simp [mergeAtSuccessResult]
      split <;> simp
    · rfl
  · rfl

/-- A traced preparation result selecting `merge_lo` carries the source branch
inequality and the complete call-site evidence exported by the transcription. -/
theorem prepareMergeAtTraced_lo_callsite_of_result_eq_some
    (pre : MergeState κ ν) (i : Nat) (call : MergeAtCall κ ν)
    (hresult : (prepareMergeAtTraced? pre i).result = some (.mergeLo call)) :
    MergeAtCallsiteEvidence pre i call ∧ call.na ≤ call.nb := by
  apply prepareMergeAt_lo_callsite_of_eq_some pre i call
  rw [← erase_prepareMergeAtTraced]
  exact hresult

/-- A traced preparation result selecting `merge_hi` carries the strict
complementary source branch inequality and the same call-site evidence. -/
theorem prepareMergeAtTraced_hi_callsite_of_result_eq_some
    (pre : MergeState κ ν) (i : Nat) (call : MergeAtCall κ ν)
    (hresult : (prepareMergeAtTraced? pre i).result = some (.mergeHi call)) :
    MergeAtCallsiteEvidence pre i call ∧ call.nb < call.na := by
  apply prepareMergeAt_hi_callsite_of_eq_some pre i call
  rw [← erase_prepareMergeAtTraced]
  exact hresult

/-- State fields which `merge_at` is forbidden to mutate.  The pending stack,
main data contents, temporary allocation, and adaptive `min_gallop` output are
intentionally absent because the operation may change them. -/
structure MergeAtStableFrame (before after : MergeState κ ν) : Prop where
  listlen : after.listlen = before.listlen
  basekeys : after.basekeys = before.basekeys
  dataSize : after.data.entries.size = before.data.entries.size
  tempValuesMode : after.a.hasValues = before.a.hasValues
  comparator : after.key_compare = before.key_compare
  mrCurrent : after.mr_current = before.mr_current
  mrE : after.mr_e = before.mr_e
  mrMask : after.mr_mask = before.mr_mask

namespace MergeAtStableFrame

theorem refl (state : MergeState κ ν) : MergeAtStableFrame state state := by
  constructor <;> rfl

theorem trans {first second third : MergeState κ ν}
    (hfirst : MergeAtStableFrame first second)
    (hsecond : MergeAtStableFrame second third) :
    MergeAtStableFrame first third := by
  exact
    { listlen := hsecond.listlen.trans hfirst.listlen
      basekeys := hsecond.basekeys.trans hfirst.basekeys
      dataSize := hsecond.dataSize.trans hfirst.dataSize
      tempValuesMode := hsecond.tempValuesMode.trans hfirst.tempValuesMode
      comparator := hsecond.comparator.trans hfirst.comparator
      mrCurrent := hsecond.mrCurrent.trans hfirst.mrCurrent
      mrE := hsecond.mrE.trans hfirst.mrE
      mrMask := hsecond.mrMask.trans hfirst.mrMask }

private theorem of_mergeLo {before after : MergeState κ ν}
    (h : MergeLoStableFrame before after) :
    MergeAtStableFrame before after := by
  exact
    { listlen := h.listlen
      basekeys := h.basekeys
      dataSize := h.dataSize
      tempValuesMode := h.tempValuesMode
      comparator := h.comparator
      mrCurrent := h.mrCurrent
      mrE := h.mrE
      mrMask := h.mrMask }

private theorem of_mergeHi {before after : MergeState κ ν}
    (h : MergeHiStableFrame before after) :
    MergeAtStableFrame before after := by
  exact
    { listlen := h.listlen
      basekeys := h.basekeys
      dataSize := h.dataSize
      tempValuesMode := h.tempValuesMode
      comparator := h.comparator
      mrCurrent := h.mrCurrent
      mrE := h.mrE
      mrMask := h.mrMask }

end MergeAtStableFrame

/-- Safety facts at the boundary between `merge_at`'s trimming prefix and its
selected merge continuation. -/
structure MergeAtPreparationSafetyPost (pre : MergeState κ ν) (i : Nat)
    (execution : TraceResult (MergeAtPreparation κ ν))
    (prepared : MergeAtPreparation κ ν) : Prop where
  resultEq : execution.result = some prepared
  traceSafe : MovementTraceSafe execution
  exactErasure : execution.erase = prepareMergeAt? pre i
  finishedSuccess : ∀ result, prepared = .finished result →
    result.returnCode = 0 ∧ result.fuelExhausted = false
  tempInvariant : TempStorageInv prepared.state.a prepared.state.alloced
  tempLive : prepared.state.a.Live
  valuesMode :
    SortSlice.ValuesModeInvariant prepared.state.a.hasValues prepared.state.data
  hasValuesFrame : prepared.state.a.hasValues = pre.a.hasValues
  storageFrame : prepared.state.a = pre.a
  allocedFrame : prepared.state.alloced = pre.alloced
  dataFrame : prepared.state.data = pre.data
  stableFrame : MergeAtStableFrame pre prepared.state

/-- Safety of the complete `merge_at` preparation prefix.  The index premise
is the source control-flow fact for the only two positions accepted by
`merge_at`; all run geometry and data bounds are derived from `PendingLayout`.
-/
theorem prepareMergeAtTraced_safe
    (pre : MergeState κ ν) (scanned i : Nat)
    (hlayout : PendingLayout pre scanned)
    (hmax : pre.listlen.toNat ≤ PY_LIST_MAX)
    (hposition : i + 2 = pre.pending.size ∨
      i + 3 = pre.pending.size)
    (hInv : TempStorageInv pre.a pre.alloced)
    (hLive : pre.a.Live)
    (hMode : SortSlice.ValuesModeInvariant pre.a.hasValues pre.data) :
    ∃ prepared,
      MergeAtPreparationSafetyPost pre i
        (prepareMergeAtTraced? pre i) prepared := by
  have hstack : 2 ≤ pre.pending.size := by omega
  have houter :
      2 ≤ pre.pending.size ∧
        (i + 2 = pre.pending.size ∨ i + 3 = pre.pending.size) :=
    ⟨hstack, hposition⟩
  have hi : i < pre.pending.size := by omega
  have hiOne : i + 1 < pre.pending.size := by omega
  let left := pre.pending[i]
  let right := pre.pending[i + 1]
  have hleft : pre.pending[i]? = some left := by
    simp [left, Array.getElem?_eq_getElem hi]
  have hright : pre.pending[i + 1]? = some right := by
    simp [right, Array.getElem?_eq_getElem hiOne]
  have hgeometry := hlayout.adjacentPair_geometry hleft hright
  have hadjacent : left.base + left.len.toNat = right.base := by
    simpa [PendingRun.endIndex] using hgeometry.adjacent
  have hguard :
      (0 : PySSize).slt left.len ∧
        (0 : PySSize).slt right.len ∧
        left.base + left.len.toNat = right.base :=
    ⟨pySSize_slt_zero_of_nonnegative_positive left.len
        hgeometry.leftNonnegative hgeometry.leftPositive,
      pySSize_slt_zero_of_nonnegative_positive right.len
        hgeometry.rightNonnegative hgeometry.rightPositive,
      hadjacent⟩
  have hleftPositive := hgeometry.leftPositive
  have hrightPositive := hgeometry.rightPositive
  have hpairSpan := hgeometry.pairSpan
  have hscannedBound := hgeometry.scannedBound
  have hleftGuard := hguard.1
  have hrightGuard := hguard.2.1
  have hscanData :
      pre.basekeys + scanned ≤ pre.data.entries.size := by
    exact (Nat.add_le_add_left hgeometry.scannedBound pre.basekeys).trans
      hlayout.2.1
  have hrightEnd :
      right.base + right.len.toNat ≤ pre.data.entries.size := by
    simpa [PendingRun.endIndex] using hgeometry.rightEnd.trans hscanData
  have hleftEnd :
      left.base + left.len.toNat ≤ pre.data.entries.size := by
    rw [hadjacent]
    omega
  have hleftMax : left.len.toNat ≤ PY_LIST_MAX := by
    omega
  have hrightMax : right.len.toNat ≤ PY_LIST_MAX := by
    omega
  have hleftReadResult :
      (TraceResult.pendingRunRead? pre (Int.ofNat i)).result = some left := by
    simpa [left] using pendingRunRead_result_of_bounds pre i hi
  have hleftReadSafe :
      MovementTraceSafe
        (TraceResult.pendingRunRead? pre (Int.ofNat i)) :=
    pendingRunRead_safe pre (Int.ofNat i)
      ⟨Int.natCast_nonneg _, by simpa using hi⟩
  have hrightReadResult :
      (TraceResult.pendingRunRead? pre (Int.ofNat (i + 1))).result =
        some right := by
    simpa [right] using
      pendingRunRead_result_of_bounds pre (i + 1) hiOne
  have hrightReadSafe :
      MovementTraceSafe
        (TraceResult.pendingRunRead? pre (Int.ofNat (i + 1))) :=
    pendingRunRead_safe pre (Int.ofNat (i + 1))
      ⟨Int.natCast_nonneg _, by simpa using hiOne⟩
  let call := mergeAtCombinedState pre i left right
  have hupdateResult :
      (mergeAtPendingUpdateTraced? pre i left right).result = some call := by
    change (mergeAtPendingUpdateTraced? pre i left right).erase = some call
    simpa [call] using
      erase_mergeAtPendingUpdateTraced pre i left right hposition
  have hupdateSafe :
      MovementTraceSafe (mergeAtPendingUpdateTraced? pre i left right) :=
    mergeAtPendingUpdateTraced_safe pre i left right hposition
  have hcallData : call.data = pre.data := rfl
  have hleftEndCall :
      left.base + left.len.toNat ≤ call.data.entries.size := by
    simpa [hcallData] using hleftEnd
  have hrightEndCall :
      right.base + right.len.toNat ≤ call.data.entries.size := by
    simpa [hcallData] using hrightEnd
  have hfirstIndex : right.base < call.data.entries.size := by
    omega
  let firstB := call.data.entries[right.base]
  have hfirstRead :
      call.data.read? (Int.ofNat right.base) = some firstB := by
    simpa [firstB] using
      sortSlice_read_ofNat_eq_some call.data right.base hfirstIndex
  have hfirstResult :
      (TraceResult.sortSliceKeysRead? call.data
        (Int.ofNat right.base)).result = some firstB :=
    sortSliceKeysRead_result_of_eq_some call.data (Int.ofNat right.base)
      firstB hfirstRead
  have hfirstBounds :
      SortSlice.IndexInBounds call.data (Int.ofNat right.base) :=
    ⟨Int.natCast_nonneg _, Int.ofNat_lt.mpr hfirstIndex⟩
  have hfirstSafe :
      MovementTraceSafe
        (TraceResult.sortSliceKeysRead? call.data
          (Int.ofNat right.base)) :=
    sortSliceKeysRead_safe call.data (Int.ofNat right.base) hfirstBounds
  have hleftValid :
      (GallopKeySource.main call.data
        (Int.ofNat left.base)).ValidRange left.len.toNat :=
    GallopKeySource.main_validRange_of_base_add_le call.data left.base
      left.len.toNat hleftEndCall
  rcases gallopRight_main_safe call call.data (Int.ofNat left.base)
      firstB.key left.len.toNat 0 hleftValid hleftPositive
      (by omega) hleftMax with
    ⟨trimA, htrimAResult, htrimAFuel, htrimABound, htrimATraceFuel,
      htrimATracePushes, htrimATraceBounds, htrimATraceLive,
      _htrimAErase⟩
  have htrimASafe : MovementTraceSafe
      (gallopRightTraced? call
        (.main call.data (Int.ofNat left.base)) firstB.key
        left.len.toNat 0) :=
    ⟨htrimATraceFuel, htrimATracePushes, htrimATraceBounds,
      htrimATraceLive⟩
  rcases mergeAtAfterTrimATraced_safe call left right firstB trimA
      hleftEndCall hrightEndCall hrightPositive hrightMax
      htrimAFuel htrimABound with ⟨prepared, htail⟩
  have htrimAChainSafe : MovementTraceSafe
      ((gallopRightTraced? call
        (.main call.data (Int.ofNat left.base)) firstB.key
        left.len.toNat 0).bind fun trimA =>
          mergeAtAfterTrimATraced call left right firstB trimA) :=
    MovementTraceSafe.bind _ _ trimA htrimAResult htrimASafe
      htail.traceSafe
  have htrimAChainResult :
      ((gallopRightTraced? call
        (.main call.data (Int.ofNat left.base)) firstB.key
        left.len.toNat 0).bind fun trimA =>
          mergeAtAfterTrimATraced call left right firstB trimA).result =
        some prepared :=
    (TraceResult.bind_result_of_eq_some _ _ trimA htrimAResult).trans
      htail.resultEq
  have hfirstChainSafe : MovementTraceSafe
      ((TraceResult.sortSliceKeysRead? call.data
        (Int.ofNat right.base)).bind fun firstB =>
          (gallopRightTraced? call
            (.main call.data (Int.ofNat left.base)) firstB.key
            left.len.toNat 0).bind fun trimA =>
              mergeAtAfterTrimATraced call left right firstB trimA) :=
    MovementTraceSafe.bind _ _ firstB hfirstResult hfirstSafe
      htrimAChainSafe
  have hfirstChainResult :
      ((TraceResult.sortSliceKeysRead? call.data
        (Int.ofNat right.base)).bind fun firstB =>
          (gallopRightTraced? call
            (.main call.data (Int.ofNat left.base)) firstB.key
            left.len.toNat 0).bind fun trimA =>
              mergeAtAfterTrimATraced call left right firstB trimA).result =
        some prepared :=
    (TraceResult.bind_result_of_eq_some _ _ firstB hfirstResult).trans
      htrimAChainResult
  have hupdateChainSafe : MovementTraceSafe
      ((mergeAtPendingUpdateTraced? pre i left right).bind fun call =>
        (TraceResult.sortSliceKeysRead? call.data
          (Int.ofNat right.base)).bind fun firstB =>
            (gallopRightTraced? call
              (.main call.data (Int.ofNat left.base)) firstB.key
              left.len.toNat 0).bind fun trimA =>
                mergeAtAfterTrimATraced call left right firstB trimA) :=
    MovementTraceSafe.bind _ _ call hupdateResult hupdateSafe
      hfirstChainSafe
  have hupdateChainResult :
      ((mergeAtPendingUpdateTraced? pre i left right).bind fun call =>
        (TraceResult.sortSliceKeysRead? call.data
          (Int.ofNat right.base)).bind fun firstB =>
            (gallopRightTraced? call
              (.main call.data (Int.ofNat left.base)) firstB.key
              left.len.toNat 0).bind fun trimA =>
                mergeAtAfterTrimATraced call left right firstB trimA).result =
        some prepared :=
    (TraceResult.bind_result_of_eq_some _ _ call hupdateResult).trans
      hfirstChainResult
  have hrightChainSafe : MovementTraceSafe
      ((TraceResult.pendingRunRead? pre (Int.ofNat (i + 1))).bind fun right =>
        if (0 : PySSize).slt left.len ∧ (0 : PySSize).slt right.len ∧
            left.base + left.len.toNat = right.base then
          (mergeAtPendingUpdateTraced? pre i left right).bind fun call =>
            (TraceResult.sortSliceKeysRead? call.data
              (Int.ofNat right.base)).bind fun firstB =>
                (gallopRightTraced? call
                  (.main call.data (Int.ofNat left.base)) firstB.key
                  left.len.toNat 0).bind fun trimA =>
                    mergeAtAfterTrimATraced call left right firstB trimA
    else TraceResult.failure) := by
    apply MovementTraceSafe.bind _ _ right hrightReadResult hrightReadSafe
    rw [if_pos hguard]
    exact hupdateChainSafe
  have hrightChainResult :
      ((TraceResult.pendingRunRead? pre (Int.ofNat (i + 1))).bind fun right =>
        if (0 : PySSize).slt left.len ∧ (0 : PySSize).slt right.len ∧
            left.base + left.len.toNat = right.base then
          (mergeAtPendingUpdateTraced? pre i left right).bind fun call =>
            (TraceResult.sortSliceKeysRead? call.data
              (Int.ofNat right.base)).bind fun firstB =>
                (gallopRightTraced? call
                  (.main call.data (Int.ofNat left.base)) firstB.key
                  left.len.toNat 0).bind fun trimA =>
                    mergeAtAfterTrimATraced call left right firstB trimA
        else TraceResult.failure).result = some prepared := by
    refine (TraceResult.bind_result_of_eq_some _ _ right
      hrightReadResult).trans ?_
    rw [if_pos hguard]
    exact hupdateChainResult
  have hfullSafe : MovementTraceSafe (prepareMergeAtTraced? pre i) := by
    unfold prepareMergeAtTraced?
    rw [if_pos houter]
    apply MovementTraceSafe.bind _ _ left hleftReadResult hleftReadSafe
    simpa [left, right] using hrightChainSafe
  have hfullResult :
      (prepareMergeAtTraced? pre i).result = some prepared := by
    unfold prepareMergeAtTraced?
    rw [if_pos houter]
    exact (TraceResult.bind_result_of_eq_some _ _ left
      hleftReadResult).trans (by simpa [left, right] using hrightChainResult)
  refine ⟨prepared, ?_⟩
  constructor
  · exact hfullResult
  · exact hfullSafe
  · exact erase_prepareMergeAtTraced pre i
  · exact htail.finishedSuccess
  · rw [htail.stateEq]
    simpa [call, mergeAtCombinedState] using hInv
  · rw [htail.stateEq]
    simpa [call, mergeAtCombinedState] using hLive
  · rw [htail.stateEq]
    simpa [call, mergeAtCombinedState] using hMode
  · rw [htail.stateEq]
    rfl
  · rw [htail.stateEq]
    rfl
  · rw [htail.stateEq]
    rfl
  · rw [htail.stateEq]
    rfl
  · rw [htail.stateEq]
    constructor <;> rfl

/-- Execute the traced merge continuation selected by
`prepareMergeAtTraced?`.  A successful directional continuation appends
exactly one raw call record computed from its actual result. -/
def finishMergeAtPreparationTraced? :
    MergeAtPreparation κ ν → TraceResult (MergeAtResult κ ν)
  | .finished result => TraceResult.pure result
  | .mergeLo call =>
      (TraceResult.recordSuccessMemoryEvent
        (mergeLoTraced? call.state call.ssa call.ssb call.na call.nb)
        (fun result =>
          .mergeCall
            (MergeMemoryCallEvent.mergeLoMemoryCallEvent call result))).map
        mergeAtFromLo
  | .mergeHi call =>
      (TraceResult.recordSuccessMemoryEvent
        (mergeHiTraced? call.state call.ssa call.ssb call.na call.nb)
        (fun result =>
          .mergeCall
            (MergeMemoryCallEvent.mergeHiMemoryCallEvent call result))).map
        mergeAtFromHi

/-- The traced finishing stage returns an already-finished preparation without
adding observations. -/
@[simp]
theorem finishMergeAtPreparationTraced_finished (result : MergeAtResult κ ν) :
    finishMergeAtPreparationTraced? (.finished result) =
      TraceResult.pure result := rfl

/-- A prepared `mergeLo` branch invokes exactly the traced `merge_lo`
continuation selected by the preparation stage. -/
@[simp]
theorem finishMergeAtPreparationTraced_mergeLo (call : MergeAtCall κ ν) :
    finishMergeAtPreparationTraced? (.mergeLo call) =
      (TraceResult.recordSuccessMemoryEvent
        (mergeLoTraced? call.state call.ssa call.ssb call.na call.nb)
        (fun result =>
          .mergeCall
            (MergeMemoryCallEvent.mergeLoMemoryCallEvent call result))).map
        mergeAtFromLo := rfl

/-- A prepared `mergeHi` branch invokes exactly the traced `merge_hi`
continuation selected by the preparation stage. -/
@[simp]
theorem finishMergeAtPreparationTraced_mergeHi (call : MergeAtCall κ ν) :
    finishMergeAtPreparationTraced? (.mergeHi call) =
      (TraceResult.recordSuccessMemoryEvent
        (mergeHiTraced? call.state call.ssa call.ssb call.na call.nb)
        (fun result =>
          .mergeCall
            (MergeMemoryCallEvent.mergeHiMemoryCallEvent call result))).map
        mergeAtFromHi := rfl

/-- The finishing stage never creates logical policy events.  Directional
merge traces are event-free on this channel, while the surrounding
`merge_at` preparation already owns the single pre-trim event. -/
theorem finishMergeAtPreparationTraced_policyEvents_eq_nil
    (prepared : MergeAtPreparation κ ν) :
    (finishMergeAtPreparationTraced? prepared).trace.policyEvents = [] := by
  cases prepared with
  | finished result => rfl
  | mergeLo call =>
      simp [finishMergeAtPreparationTraced?,
        mergeLoTraced_policyEvents_empty]
  | mergeHi call =>
      simp [finishMergeAtPreparationTraced?,
        mergeHiTraced_policyEvents_empty]

/-- Fully traced `merge_at` evaluator. -/
def mergeAtTraced? (state : MergeState κ ν) (i : Nat) :
    TraceResult (MergeAtResult κ ν) :=
  (prepareMergeAtTraced? state i).bind finishMergeAtPreparationTraced?

/-- Once preparation succeeds, the complete `merge_at` call has exactly the
same policy history as its preparation prefix. -/
theorem mergeAtTraced_policyEvents_eq_prepare
    (pre : MergeState κ ν) (i : Nat) (prepared : MergeAtPreparation κ ν)
    (hprepared : (prepareMergeAtTraced? pre i).result = some prepared) :
    (mergeAtTraced? pre i).trace.policyEvents =
      (prepareMergeAtTraced? pre i).trace.policyEvents := by
  rw [mergeAtTraced?, TraceResult.policyEvents_bind, hprepared]
  simp only
  rw [finishMergeAtPreparationTraced_policyEvents_eq_nil, List.append_nil]

/-- Full public postcondition for a source-admitted `merge_at` call. -/
structure MergeAtSafetyPost (pre : MergeState κ ν) (scanned i : Nat)
    (execution : TraceResult (MergeAtResult κ ν))
    (result : MergeAtResult κ ν) : Prop where
  resultEq : execution.result = some result
  returnCode : result.returnCode = 0
  resultFuel : result.fuelExhausted = false
  traceFuel : execution.trace.fuelExhausted = false
  accessesInBounds : execution.trace.allAccessesInBounds
  tempAccessesLive : execution.trace.tempPayloadAccessesLive
  noPushes : execution.trace.pushDepths = []
  /-- Every raw lifecycle observation emitted by this `merge_at` invocation is
  validated in the values mode inherited from its caller. -/
  memoryEventsValid : execution.trace.memoryEventsValid pre.a.hasValues
  /-- `merge_at` owns directional call records only; initialization and final
  cleanup remain top-level events. -/
  onlyMergeMemoryEvents : execution.trace.onlyMergeMemoryEvents
  /-- The initialized physical-slot ceiling is threaded through every call
  record rather than reconstructed from raw observations. -/
  memoryEventsBounded :
    (MergeMemorySnapshot.ofState pre).PhysicalBound →
      execution.trace.mergeMemoryEventsBounded
  /-- Exact local event cardinality: an early trimmed exit emits nothing and a
  completed directional merge emits exactly its one call record. -/
  memoryEventShape :
    execution.trace.memoryEvents = [] ∨
      ∃ call, execution.trace.memoryEvents = [.mergeCall call]
  /-- The call records are not merely well-shaped: their concrete storage
  boundaries form one gap-free path from the caller state to the result. -/
  memorySegment : execution.trace.MergeMemorySegment
    (MergeMemorySnapshot.ofState pre)
    (MergeMemorySnapshot.ofState result.state)
  exactErasure : execution.erase = mergeAt? pre i
  tempInvariant : TempStorageInv result.state.a result.state.alloced
  tempLive : result.state.a.Live
  valuesMode :
    SortSlice.ValuesModeInvariant result.state.a.hasValues result.state.data
  hasValuesFrame : result.state.a.hasValues = pre.a.hasValues
  stableFrame : MergeAtStableFrame pre result.state
  pendingLayout : PendingLayout result.state scanned
  /-- The successful full call emits exactly one logical merge event for the
  two selected adjacent runs as they stood before trimming, and the result
  pending array is exactly their source-level splice. -/
  logicalMerge : ∃ left right,
    pre.pending[i]? = some left ∧
      pre.pending[i + 1]? = some right ∧
      result.state.pending =
        (pre.pending.setIfInBounds i
          { left with len := left.len + right.len }).eraseIdxIfInBounds
            (i + 1) ∧
      execution.trace.policyEvents =
        [.merge
          { index := i
            left := RunSpan.ofPendingRun left
            right := RunSpan.ofPendingRun right }]
  physicalSlotsBound :
    (MergeMemorySnapshot.ofState pre).PhysicalBound →
      (MergeMemorySnapshot.ofState result.state).PhysicalBound

/-- The preparation prefix is lifecycle-event-free, so the complete
`merge_at` event list is exactly the selected finishing stage's event list. -/
private theorem mergeAtTraced_memoryEvents_eq_finish
    (pre : MergeState κ ν) (i : Nat) (prepared : MergeAtPreparation κ ν)
    (hprepared : (prepareMergeAtTraced? pre i).result = some prepared) :
    (mergeAtTraced? pre i).trace.memoryEvents =
      (finishMergeAtPreparationTraced? prepared).trace.memoryEvents := by
  rw [mergeAtTraced?, TraceResult.trace_bind, hprepared,
    AccessTrace.memoryEvents_compose,
    prepareMergeAtTraced_memoryEvents_eq_nil]
  rfl

/-- Trimming and pending-stack bookkeeping do not change the memory snapshot
observed by lifecycle events. -/
private theorem mergeAtPreparation_memorySnapshotFrame
    (pre : MergeState κ ν) (i : Nat) (prepared : MergeAtPreparation κ ν)
    (hprep : MergeAtPreparationSafetyPost pre i
      (prepareMergeAtTraced? pre i) prepared) :
    MergeMemorySnapshot.ofState prepared.state =
      MergeMemorySnapshot.ofState pre := by
  simp only [MergeMemorySnapshot.ofState]
  rw [hprep.storageFrame, hprep.allocedFrame, hprep.dataFrame]

private theorem prepareMergeAt_eq_some_of_post
    (pre : MergeState κ ν) (i : Nat) (prepared : MergeAtPreparation κ ν)
    (hprep : MergeAtPreparationSafetyPost pre i
      (prepareMergeAtTraced? pre i) prepared) :
    prepareMergeAt? pre i = some prepared := by
  calc
    prepareMergeAt? pre i = (prepareMergeAtTraced? pre i).erase :=
      hprep.exactErasure.symm
    _ = (prepareMergeAtTraced? pre i).result := rfl
    _ = some prepared := hprep.resultEq

private theorem pendingLayout_of_mergeAtTraced_result
    (pre : MergeState κ ν) (scanned i : Nat) (result : MergeAtResult κ ν)
    (hlayout : PendingLayout pre scanned)
    (hresult : (mergeAtTraced? pre i).result = some result)
    (hexact : (mergeAtTraced? pre i).erase = mergeAt? pre i) :
    PendingLayout result.state scanned := by
  have hmerge : mergeAt? pre i = some result := by
    rw [← hexact]
    simpa [TraceResult.erase] using hresult
  rcases mergeAt_preserves_pendingLayout pre scanned i result hlayout hmerge with
    ⟨_before, _left, _right, _after, _hbefore, _hprePending,
      _hresultPending, _hleftNonnegative, _hleftPositive,
      _hrightNonnegative, _hrightPositive, _hadjacent, _hadd,
      hresultLayout⟩
  exact hresultLayout

/-- Package the exact logical event together with the exact pending-array
splice obtained from the erased successful call.  The event operands come
from the pre-trim pending reads, while the result equation comes from the
reviewed transcription's frame theorem. -/
private theorem mergeAt_logicalMerge_of_result
    (pre : MergeState κ ν) (scanned i : Nat)
    (prepared : MergeAtPreparation κ ν) (result : MergeAtResult κ ν)
    (hlayout : PendingLayout pre scanned)
    (hposition : i + 2 = pre.pending.size ∨
      i + 3 = pre.pending.size)
    (hprepared : (prepareMergeAtTraced? pre i).result = some prepared)
    (hresult : (mergeAtTraced? pre i).result = some result)
    (hexact : (mergeAtTraced? pre i).erase = mergeAt? pre i) :
    ∃ left right,
      pre.pending[i]? = some left ∧
        pre.pending[i + 1]? = some right ∧
        result.state.pending =
          (pre.pending.setIfInBounds i
            { left with len := left.len + right.len }).eraseIdxIfInBounds
              (i + 1) ∧
        (mergeAtTraced? pre i).trace.policyEvents =
          [.merge
            { index := i
              left := RunSpan.ofPendingRun left
              right := RunSpan.ofPendingRun right }] := by
  have hmerge : mergeAt? pre i = some result := by
    rw [← hexact]
    simpa [TraceResult.erase] using hresult
  rcases mergeAt_pending_frame_of_eq_some pre i result hmerge with
    ⟨left, right, hleft, hright, _hlistlen, _hbasekeys, _hdataSize,
      hpending⟩
  have hprepareEvent :=
    prepareMergeAtTraced_policyEvent pre scanned i left right hlayout
      hposition hleft hright
  have hfullEvent :=
    mergeAtTraced_policyEvents_eq_prepare pre i prepared hprepared
  exact ⟨left, right, hleft, hright, hpending, hfullEvent.trans hprepareEvent⟩

private theorem mergeAt_safe_finished
    (pre : MergeState κ ν) (scanned i : Nat) (early : MergeAtResult κ ν)
    (hlayout : PendingLayout pre scanned)
    (hposition : i + 2 = pre.pending.size ∨
      i + 3 = pre.pending.size)
    (hprep : MergeAtPreparationSafetyPost pre i
      (prepareMergeAtTraced? pre i) (.finished early)) :
    ∃ result,
      MergeAtSafetyPost pre scanned i (mergeAtTraced? pre i) result := by
  have hprepareRaw := prepareMergeAt_eq_some_of_post pre i (.finished early) hprep
  have hfinishResult :
      (finishMergeAtPreparationTraced? (.finished early)).result =
        some early := rfl
  have hfullResult : (mergeAtTraced? pre i).result = some early := by
    unfold mergeAtTraced?
    exact (TraceResult.bind_result_of_eq_some _ _
      (MergeAtPreparation.finished early) hprep.resultEq).trans hfinishResult
  have hfinishSafe :
      MovementTraceSafe
        (finishMergeAtPreparationTraced? (MergeAtPreparation.finished early)) :=
    MovementTraceSafe.pure early
  have hfullSafe : MovementTraceSafe (mergeAtTraced? pre i) := by
    unfold mergeAtTraced?
    exact MovementTraceSafe.bind _ _ (MergeAtPreparation.finished early)
      hprep.resultEq hprep.traceSafe hfinishSafe
  have hexact : (mergeAtTraced? pre i).erase = mergeAt? pre i := by
    unfold mergeAtTraced?
    rw [TraceResult.erase_bind, hprep.exactErasure]
    unfold mergeAt?
    rw [hprepareRaw, mergeAt_bindOptionAcross_some]
    rfl
  have hresultLayout := pendingLayout_of_mergeAtTraced_result pre scanned i
    early hlayout hfullResult hexact
  have hsuccess := hprep.finishedSuccess early rfl
  have hMemoryEvents :
      (mergeAtTraced? pre i).trace.memoryEvents = [] := by
    rw [mergeAtTraced_memoryEvents_eq_finish pre i (.finished early)
      hprep.resultEq]
    rfl
  have hPrepSnapshot :=
    mergeAtPreparation_memorySnapshotFrame pre i (.finished early) hprep
  refine ⟨early, ?_⟩
  exact
    { resultEq := hfullResult
      returnCode := hsuccess.1
      resultFuel := hsuccess.2
      traceFuel := hfullSafe.fuel
      accessesInBounds := hfullSafe.bounds
      tempAccessesLive := hfullSafe.tempLive
      noPushes := hfullSafe.noPushes
      memoryEventsValid := by
        simp [AccessTrace.memoryEventsValid, hMemoryEvents]
      onlyMergeMemoryEvents := by
        simp [AccessTrace.onlyMergeMemoryEvents, hMemoryEvents]
      memoryEventsBounded := by
        intro _
        simp [AccessTrace.mergeMemoryEventsBounded, hMemoryEvents]
      memoryEventShape := Or.inl hMemoryEvents
      memorySegment := by
        refine ⟨[], hMemoryEvents, ?_⟩
        simpa [MergeAtPreparation.state] using hPrepSnapshot.symm
      exactErasure := hexact
      tempInvariant := hprep.tempInvariant
      tempLive := hprep.tempLive
      valuesMode := hprep.valuesMode
      hasValuesFrame := hprep.hasValuesFrame
      stableFrame := hprep.stableFrame
      pendingLayout := hresultLayout
      logicalMerge :=
        mergeAt_logicalMerge_of_result pre scanned i (.finished early) early
          hlayout hposition hprep.resultEq hfullResult hexact
      physicalSlotsBound := by
        intro hbound
        have hStorage : early.state.a = pre.a := by
          simpa [MergeAtPreparation.state] using hprep.storageFrame
        simpa [MergeMemorySnapshot.PhysicalBound,
          MergeMemorySnapshot.ofState, hStorage] using hbound }

private theorem mergeAt_safe_mergeLo
    (pre : MergeState κ ν) (scanned i : Nat) (call : MergeAtCall κ ν)
    (hlayout : PendingLayout pre scanned)
    (hposition : i + 2 = pre.pending.size ∨
      i + 3 = pre.pending.size)
    (hmax : pre.listlen.toNat ≤ PY_LIST_MAX)
    (hInv : TempStorageInv pre.a pre.alloced)
    (hLive : pre.a.Live)
    (hMode : SortSlice.ValuesModeInvariant pre.a.hasValues pre.data)
    (hprep : MergeAtPreparationSafetyPost pre i
      (prepareMergeAtTraced? pre i) (.mergeLo call)) :
    ∃ result,
      MergeAtSafetyPost pre scanned i (mergeAtTraced? pre i) result := by
  have hprepareRaw := prepareMergeAt_eq_some_of_post pre i (.mergeLo call) hprep
  rcases mergeLo_safe pre scanned i call hlayout hmax hprepareRaw
      hInv hLive hMode with ⟨loResult, hlo⟩
  let result : MergeAtResult κ ν := mergeAtFromLo loResult
  have hfinishResult :
      (finishMergeAtPreparationTraced? (.mergeLo call)).result =
        some result := by
    simp only [finishMergeAtPreparationTraced?, TraceResult.map,
      TraceResult.result_recordSuccessMemoryEvent]
    rw [hlo.resultEq]
    rfl
  have hloSafe : MovementTraceSafe
      (mergeLoTraced? call.state call.ssa call.ssb call.na call.nb) :=
    ⟨hlo.traceFuel, hlo.noPushes, hlo.accessesInBounds,
      hlo.tempAccessesLive⟩
  have hfinishSafe :
      MovementTraceSafe (finishMergeAtPreparationTraced? (.mergeLo call)) :=
    by
      simpa only [finishMergeAtPreparationTraced?] using
        MovementTraceSafe.map _ _
          (MovementTraceSafe.recordSuccessMemoryEvent _ _ hloSafe)
  have hfullResult : (mergeAtTraced? pre i).result = some result := by
    unfold mergeAtTraced?
    exact (TraceResult.bind_result_of_eq_some _ _
      (MergeAtPreparation.mergeLo call) hprep.resultEq).trans hfinishResult
  have hfullSafe : MovementTraceSafe (mergeAtTraced? pre i) := by
    unfold mergeAtTraced?
    exact MovementTraceSafe.bind _ _ (MergeAtPreparation.mergeLo call)
      hprep.resultEq hprep.traceSafe hfinishSafe
  have hrawLo :
      mergeLo? call.state call.ssa call.ssb call.na call.nb =
        some loResult := by
    rw [← hlo.exactErasure]
    simpa [TraceResult.erase] using hlo.resultEq
  have hexact : (mergeAtTraced? pre i).erase = mergeAt? pre i := by
    unfold mergeAtTraced?
    rw [TraceResult.erase_bind, hprep.exactErasure]
    unfold mergeAt?
    rw [hprepareRaw, mergeAt_bindOptionAcross_some]
    simp [finishMergeAtPreparationTraced?, finishMergeAtPreparation?,
      TraceResult.erase_map, TraceResult.erase_recordSuccessMemoryEvent,
      hlo.exactErasure, hrawLo, mergeAtFromLo,
      fromMergeLo_eq]
  have hresultLayout := pendingLayout_of_mergeAtTraced_result pre scanned i
    result hlayout hfullResult hexact
  have hcallBit : call.state.a.hasValues = pre.a.hasValues := by
    simpa [MergeAtPreparation.state] using hprep.hasValuesFrame
  have hcallValid :
      (MergeMemoryCallEvent.mergeLoMemoryCallEvent call loResult).Valid
        pre.a.hasValues :=
    MergeMemoryCallEvent.mergeLoMemoryCallEvent_valid pre.a.hasValues pre
      scanned i call
      (mergeLoTraced? call.state call.ssa call.ssb call.na call.nb)
      loResult hlo hcallBit
  have hMemoryEvents :
      (mergeAtTraced? pre i).trace.memoryEvents =
        [.mergeCall
          (MergeMemoryCallEvent.mergeLoMemoryCallEvent call loResult)] := by
    rw [mergeAtTraced_memoryEvents_eq_finish pre i (.mergeLo call)
      hprep.resultEq]
    simp only [finishMergeAtPreparationTraced?, TraceResult.memoryEvents_map]
    rw [TraceResult.memoryEvents_recordSuccessMemoryEvent_of_eq_some _ _
      loResult hlo.resultEq, hlo.noMemoryEvents]
    rfl
  have hPrepSnapshot :=
    mergeAtPreparation_memorySnapshotFrame pre i (.mergeLo call) hprep
  refine ⟨result, ?_⟩
  exact
    { resultEq := hfullResult
      returnCode := by simpa [result, mergeAtFromLo] using hlo.returnCode
      resultFuel := by simpa [result, mergeAtFromLo] using hlo.resultFuel
      traceFuel := hfullSafe.fuel
      accessesInBounds := hfullSafe.bounds
      tempAccessesLive := hfullSafe.tempLive
      noPushes := hfullSafe.noPushes
      memoryEventsValid := by
        simp [AccessTrace.memoryEventsValid, hMemoryEvents,
          MergeMemoryEvent.Valid, hcallValid]
      onlyMergeMemoryEvents := by
        simp [AccessTrace.onlyMergeMemoryEvents, hMemoryEvents]
      memoryEventsBounded := by
        intro hBefore
        have hBeforeCall : call.state.a.physicalSlots ≤
            PY_SSIZE_T_MAX / PY_OBJECT_PTR_BYTES := by
          have hStorage : call.state.a = pre.a := by
            simpa [MergeAtPreparation.state] using hprep.storageFrame
          simpa [MergeMemorySnapshot.PhysicalBound,
            MergeMemorySnapshot.ofState, hStorage] using hBefore
        have hBounded :=
          MergeMemoryCallEvent.mergeLoMemoryCallEvent_bounded_of_post
            pre.a.hasValues pre scanned i call
            (mergeLoTraced? call.state call.ssa call.ssb call.na call.nb)
            loResult hlo hcallBit hBeforeCall
        simpa [AccessTrace.mergeMemoryEventsBounded, hMemoryEvents] using
          hBounded
      memoryEventShape := Or.inr ⟨_, hMemoryEvents⟩
      memorySegment := by
        refine ⟨[MergeMemoryCallEvent.mergeLoMemoryCallEvent call loResult],
          hMemoryEvents, ?_⟩
        refine ⟨?_, ?_⟩
        · simpa [MergeMemoryCallEvent.mergeLoMemoryCallEvent,
            MergeAtPreparation.state] using hPrepSnapshot
        · rfl
      exactErasure := hexact
      tempInvariant := by
        simpa [result, mergeAtFromLo] using hlo.tempInvariant
      tempLive := by simpa [result, mergeAtFromLo] using hlo.tempLive
      valuesMode := by simpa [result, mergeAtFromLo] using hlo.valuesMode
      hasValuesFrame := by
        simpa [result, mergeAtFromLo] using
          hlo.stableFrame.tempValuesMode.trans hprep.hasValuesFrame
      stableFrame := by
        simpa [result, mergeAtFromLo] using hprep.stableFrame.trans
          (MergeAtStableFrame.of_mergeLo hlo.stableFrame)
      pendingLayout := hresultLayout
      logicalMerge :=
        mergeAt_logicalMerge_of_result pre scanned i (.mergeLo call) result
          hlayout hposition hprep.resultEq hfullResult hexact
      physicalSlotsBound := by
        intro hBefore
        have hBeforeCall : call.state.a.physicalSlots ≤
            PY_SSIZE_T_MAX / PY_OBJECT_PTR_BYTES := by
          have hStorage : call.state.a = pre.a := by
            simpa [MergeAtPreparation.state] using hprep.storageFrame
          simpa [MergeMemorySnapshot.PhysicalBound,
            MergeMemorySnapshot.ofState, hStorage] using hBefore
        simpa [result, mergeAtFromLo, MergeMemorySnapshot.PhysicalBound,
          MergeMemorySnapshot.ofState] using hlo.physicalSlotsBound hBeforeCall }

private theorem mergeAt_safe_mergeHi
    (pre : MergeState κ ν) (scanned i : Nat) (call : MergeAtCall κ ν)
    (hlayout : PendingLayout pre scanned)
    (hposition : i + 2 = pre.pending.size ∨
      i + 3 = pre.pending.size)
    (hmax : pre.listlen.toNat ≤ PY_LIST_MAX)
    (hInv : TempStorageInv pre.a pre.alloced)
    (hLive : pre.a.Live)
    (hMode : SortSlice.ValuesModeInvariant pre.a.hasValues pre.data)
    (hprep : MergeAtPreparationSafetyPost pre i
      (prepareMergeAtTraced? pre i) (.mergeHi call)) :
    ∃ result,
      MergeAtSafetyPost pre scanned i (mergeAtTraced? pre i) result := by
  have hprepareRaw := prepareMergeAt_eq_some_of_post pre i (.mergeHi call) hprep
  rcases mergeHi_safe pre scanned i call hlayout hmax hprepareRaw
      hInv hLive hMode with ⟨hiResult, hhi⟩
  let result : MergeAtResult κ ν := mergeAtFromHi hiResult
  have hfinishResult :
      (finishMergeAtPreparationTraced? (.mergeHi call)).result =
        some result := by
    simp only [finishMergeAtPreparationTraced?, TraceResult.map,
      TraceResult.result_recordSuccessMemoryEvent]
    rw [hhi.resultEq]
    rfl
  have hhiSafe : MovementTraceSafe
      (mergeHiTraced? call.state call.ssa call.ssb call.na call.nb) :=
    ⟨hhi.traceFuel, hhi.noPushes, hhi.accessesInBounds,
      hhi.tempAccessesLive⟩
  have hfinishSafe :
      MovementTraceSafe (finishMergeAtPreparationTraced? (.mergeHi call)) :=
    by
      simpa only [finishMergeAtPreparationTraced?] using
        MovementTraceSafe.map _ _
          (MovementTraceSafe.recordSuccessMemoryEvent _ _ hhiSafe)
  have hfullResult : (mergeAtTraced? pre i).result = some result := by
    unfold mergeAtTraced?
    exact (TraceResult.bind_result_of_eq_some _ _
      (MergeAtPreparation.mergeHi call) hprep.resultEq).trans hfinishResult
  have hfullSafe : MovementTraceSafe (mergeAtTraced? pre i) := by
    unfold mergeAtTraced?
    exact MovementTraceSafe.bind _ _ (MergeAtPreparation.mergeHi call)
      hprep.resultEq hprep.traceSafe hfinishSafe
  have hrawHi :
      mergeHi? call.state call.ssa call.ssb call.na call.nb =
        some hiResult := by
    rw [← hhi.exactErasure]
    simpa [TraceResult.erase] using hhi.resultEq
  have hexact : (mergeAtTraced? pre i).erase = mergeAt? pre i := by
    unfold mergeAtTraced?
    rw [TraceResult.erase_bind, hprep.exactErasure]
    unfold mergeAt?
    rw [hprepareRaw, mergeAt_bindOptionAcross_some]
    simp [finishMergeAtPreparationTraced?, finishMergeAtPreparation?,
      TraceResult.erase_map, TraceResult.erase_recordSuccessMemoryEvent,
      hhi.exactErasure, hrawHi, mergeAtFromHi,
      fromMergeHi_eq]
  have hresultLayout := pendingLayout_of_mergeAtTraced_result pre scanned i
    result hlayout hfullResult hexact
  have hcallBit : call.state.a.hasValues = pre.a.hasValues := by
    simpa [MergeAtPreparation.state] using hprep.hasValuesFrame
  have hcallValid :
      (MergeMemoryCallEvent.mergeHiMemoryCallEvent call hiResult).Valid
        pre.a.hasValues :=
    MergeMemoryCallEvent.mergeHiMemoryCallEvent_valid pre.a.hasValues pre
      scanned i call
      (mergeHiTraced? call.state call.ssa call.ssb call.na call.nb)
      hiResult hhi hcallBit
  have hMemoryEvents :
      (mergeAtTraced? pre i).trace.memoryEvents =
        [.mergeCall
          (MergeMemoryCallEvent.mergeHiMemoryCallEvent call hiResult)] := by
    rw [mergeAtTraced_memoryEvents_eq_finish pre i (.mergeHi call)
      hprep.resultEq]
    simp only [finishMergeAtPreparationTraced?, TraceResult.memoryEvents_map]
    rw [TraceResult.memoryEvents_recordSuccessMemoryEvent_of_eq_some _ _
      hiResult hhi.resultEq, hhi.noMemoryEvents]
    rfl
  have hPrepSnapshot :=
    mergeAtPreparation_memorySnapshotFrame pre i (.mergeHi call) hprep
  refine ⟨result, ?_⟩
  exact
    { resultEq := hfullResult
      returnCode := by simpa [result, mergeAtFromHi] using hhi.returnCode
      resultFuel := by simpa [result, mergeAtFromHi] using hhi.resultFuel
      traceFuel := hfullSafe.fuel
      accessesInBounds := hfullSafe.bounds
      tempAccessesLive := hfullSafe.tempLive
      noPushes := hfullSafe.noPushes
      memoryEventsValid := by
        simp [AccessTrace.memoryEventsValid, hMemoryEvents,
          MergeMemoryEvent.Valid, hcallValid]
      onlyMergeMemoryEvents := by
        simp [AccessTrace.onlyMergeMemoryEvents, hMemoryEvents]
      memoryEventsBounded := by
        intro hBefore
        have hBeforeCall : call.state.a.physicalSlots ≤
            PY_SSIZE_T_MAX / PY_OBJECT_PTR_BYTES := by
          have hStorage : call.state.a = pre.a := by
            simpa [MergeAtPreparation.state] using hprep.storageFrame
          simpa [MergeMemorySnapshot.PhysicalBound,
            MergeMemorySnapshot.ofState, hStorage] using hBefore
        have hBounded :=
          MergeMemoryCallEvent.mergeHiMemoryCallEvent_bounded_of_post
            pre.a.hasValues pre scanned i call
            (mergeHiTraced? call.state call.ssa call.ssb call.na call.nb)
            hiResult hhi hcallBit hBeforeCall
        simpa [AccessTrace.mergeMemoryEventsBounded, hMemoryEvents] using
          hBounded
      memoryEventShape := Or.inr ⟨_, hMemoryEvents⟩
      memorySegment := by
        refine ⟨[MergeMemoryCallEvent.mergeHiMemoryCallEvent call hiResult],
          hMemoryEvents, ?_⟩
        refine ⟨?_, ?_⟩
        · simpa [MergeMemoryCallEvent.mergeHiMemoryCallEvent,
            MergeAtPreparation.state] using hPrepSnapshot
        · rfl
      exactErasure := hexact
      tempInvariant := by
        simpa [result, mergeAtFromHi] using hhi.tempInvariant
      tempLive := by simpa [result, mergeAtFromHi] using hhi.tempLive
      valuesMode := by simpa [result, mergeAtFromHi] using hhi.valuesMode
      hasValuesFrame := by
        simpa [result, mergeAtFromHi] using
          hhi.stableFrame.tempValuesMode.trans hprep.hasValuesFrame
      stableFrame := by
        simpa [result, mergeAtFromHi] using hprep.stableFrame.trans
          (MergeAtStableFrame.of_mergeHi hhi.stableFrame)
      pendingLayout := hresultLayout
      logicalMerge :=
        mergeAt_logicalMerge_of_result pre scanned i (.mergeHi call) result
          hlayout hposition hprep.resultEq hfullResult hexact
      physicalSlotsBound := by
        intro hBefore
        have hBeforeCall : call.state.a.physicalSlots ≤
            PY_SSIZE_T_MAX / PY_OBJECT_PTR_BYTES := by
          have hStorage : call.state.a = pre.a := by
            simpa [MergeAtPreparation.state] using hprep.storageFrame
          simpa [MergeMemorySnapshot.PhysicalBound,
            MergeMemorySnapshot.ofState, hStorage] using hBefore
        simpa [result, mergeAtFromHi, MergeMemorySnapshot.PhysicalBound,
          MergeMemorySnapshot.ofState] using hhi.physicalSlotsBound hBeforeCall }

/-- End-to-end safety of a source-admitted `merge_at` operation.  The theorem
composes the concrete preparation accesses with the selected traced merge and
exports both temporary-storage liveness and exact agreement with the reviewed
transcription. -/
theorem mergeAt_safe
    (pre : MergeState κ ν) (scanned i : Nat)
    (hlayout : PendingLayout pre scanned)
    (hmax : pre.listlen.toNat ≤ PY_LIST_MAX)
    (hposition : i + 2 = pre.pending.size ∨
      i + 3 = pre.pending.size)
    (hInv : TempStorageInv pre.a pre.alloced)
    (hLive : pre.a.Live)
    (hMode : SortSlice.ValuesModeInvariant pre.a.hasValues pre.data) :
    ∃ result,
      MergeAtSafetyPost pre scanned i (mergeAtTraced? pre i) result := by
  rcases prepareMergeAtTraced_safe pre scanned i hlayout hmax hposition
      hInv hLive hMode with ⟨prepared, hprep⟩
  cases prepared with
  | finished early =>
      exact mergeAt_safe_finished pre scanned i early hlayout hposition hprep
  | mergeLo call =>
      exact mergeAt_safe_mergeLo pre scanned i call hlayout hposition hmax hInv
        hLive hMode hprep
  | mergeHi call =>
      exact mergeAt_safe_mergeHi pre scanned i call hlayout hposition hmax hInv
        hLive hMode hprep

/-! ## Logical-event anti-vacuity regression -/

private def mergeAtPolicyEarlyTrimLeft : PendingRun :=
  { base := 0, len := 1, power := some 4 }

private def mergeAtPolicyEarlyTrimRight : PendingRun :=
  { base := 1, len := 1, power := some 7 }

private def mergeAtPolicyEarlyTrimTail : PendingRun :=
  { base := 2, len := 1, power := none }

private def mergeAtPolicyEarlyTrimState : MergeState Nat Nat :=
  { min_gallop := MIN_GALLOP
    listlen := 3
    basekeys := 0
    data :=
      { entries :=
          #[{ key := 1, value := none },
            { key := 2, value := none },
            { key := 3, value := none }] }
    a := { cells := #[], backing := .inline, hasValues := false }
    alloced := 0
    pending :=
      #[mergeAtPolicyEarlyTrimLeft,
        mergeAtPolicyEarlyTrimRight,
        mergeAtPolicyEarlyTrimTail]
    key_compare := fun left right => decide (left < right)
    mr_current := 0
    mr_e := 0
    mr_mask := 0 }

private def mergeAtPolicyEarlyTrimCall : MergeState Nat Nat :=
  mergeAtCombinedState mergeAtPolicyEarlyTrimState 0
    mergeAtPolicyEarlyTrimLeft mergeAtPolicyEarlyTrimRight

private def mergeAtFinishedSuccessShape
    (prepared : MergeAtPreparation Nat Nat) : Option (Int × Bool) :=
  match prepared with
  | .finished result => some (result.returnCode, result.fuelExhausted)
  | .mergeLo _ | .mergeHi _ => none

/-- This concrete input reaches the `na = 0` early-trim exit: the first gallop
returns the whole left-run length, preparation finishes successfully, and the
complete `merge_at` emits its logical full-run merge even though no directional
merge-memory call occurs.  The proof uses kernel reduction, not native evaluation. -/
theorem mergeAtTraced_earlyTrim_recordsLogicalMerge :
    (gallopRightTraced? mergeAtPolicyEarlyTrimCall
        (.main mergeAtPolicyEarlyTrimCall.data 0) 2 1 0).result =
      some { index := 1, fuelExhausted := false } ∧
    (prepareMergeAtTraced? mergeAtPolicyEarlyTrimState 0).result.bind
        mergeAtFinishedSuccessShape = some (0, false) ∧
    (mergeAtTraced? mergeAtPolicyEarlyTrimState 0).trace.policyEvents =
      [.merge
        { index := 0
          left := { base := 0, len := 1 }
          right := { base := 1, len := 1 } }] ∧
    (mergeAtTraced? mergeAtPolicyEarlyTrimState 0).trace.memoryEvents = [] := by
  decide

end CPythonListsort
