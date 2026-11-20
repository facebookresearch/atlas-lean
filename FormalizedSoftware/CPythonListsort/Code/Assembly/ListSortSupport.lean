/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Code.Assembly.ListSortInputMode
import Code.Assembly.ReverseSliceSafety
import Code.Equivalence.MinrunResults
import Code.Policy.PushRunPreservation

/-!
# Support lemmas for top-level listsort assembly

This module packages the initialized `MergeState`, the adaptive-minrun state
carried by the scan, and the frame facts for the small top-level transitions.
It deliberately does not define a second listsort evaluator: the traced
top-level assembly consumes the public helpers from the reviewed
`ListSortImpl` transcription.
-/

namespace CPythonListsort

universe u v

variable {κ : Type u} {ν : Type v}

/-! ## Selected-platform word facts -/

/-- A source-admitted list length is represented exactly by the selected
64-bit word model. -/
theorem listSizeWord_toNat {size : Nat} (hsize : size ≤ PY_LIST_MAX) :
    (BitVec.ofNat 64 size : PySSize).toNat = size := by
  rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt]
  norm_num [PY_LIST_MAX, PY_SSIZE_T_MAX, PY_OBJECT_PTR_BYTES] at hsize ⊢
  omega

/-- A source-admitted list length remains signed-nonnegative after conversion
to the selected `Py_ssize_t` model. -/
theorem listSizeWord_nonnegative {size : Nat} (hsize : size ≤ PY_LIST_MAX) :
    PySSize.Nonnegative (BitVec.ofNat 64 size) := by
  rw [PySSize.Nonnegative, BitVec.msb_eq_false_iff_two_mul_lt]
  rw [listSizeWord_toNat hsize]
  norm_num [PY_LIST_MAX, PY_SSIZE_T_MAX, PY_OBJECT_PTR_BYTES] at hsize ⊢
  omega

/-- Signed comparison agrees with natural comparison while both modeled
`Py_ssize_t` operands are nonnegative. -/
theorem pySSize_slt_eq_nat_lt (x y : PySSize)
    (hx : x.Nonnegative) (hy : y.Nonnegative) :
    x.slt y = decide (x.toNat < y.toNat) := by
  rw [BitVec.slt_eq_decide]
  rw [BitVec.toInt_eq_toNat_of_msb hx]
  rw [BitVec.toInt_eq_toNat_of_msb hy]
  norm_cast

/-- Any word whose unsigned value is at most `MAX_MINRUN` is also a
nonnegative signed `Py_ssize_t`. -/
theorem pySSize_nonnegative_of_toNat_le_maxMinrun (x : PySSize)
    (hx : x.toNat ≤ MAX_MINRUN.toNat) : x.Nonnegative := by
  rw [PySSize.Nonnegative, BitVec.msb_eq_false_iff_two_mul_lt]
  have hMaxMinrun : MAX_MINRUN.toNat = 64 := by decide
  rw [hMaxMinrun] at hx
  norm_num
  omega

/-! ## Initial state -/

/-- Facts established by `initialMergeState` on a source-admitted raw input.
The explicit `hasValues` equation is retained separately from the entrywise
mode invariant because that invariant is vacuous for an empty slice. -/
structure InitialMergeStatePackage
    (lt : BoolComparator κ) (hasKeyfunc : Bool) (input : SortSlice κ ν)
    (state : MergeState κ ν) : Prop where
  exactState : state = (initialMergeState lt hasKeyfunc input).1
  listlenRoundtrip : state.listlen.toNat = input.entries.size
  listlenNonnegative : state.listlen.Nonnegative
  basekeys : state.basekeys = 0
  data : state.data = input
  pending : state.pending = #[]
  pendingLayout : PendingLayout state 0
  poweredPrefix : PoweredPrefix state
  tempInvariant : TempStorageInv state.a state.alloced
  tempLive : state.a.Live
  logicalCapacity : state.a.cells.size = state.alloced.toNat
  physicalSlotsBound :
    state.a.physicalSlots ≤ PY_SSIZE_T_MAX / PY_OBJECT_PTR_BYTES
  hasValues : state.a.hasValues = hasKeyfunc
  valuesMode : SortSlice.ValuesModeInvariant state.a.hasValues state.data
  comparator : state.key_compare = lt
  minrunState : state.minrunState = minrunInit state.listlen
  minrunStopped : (initialMergeState lt hasKeyfunc input).2 = true

/-- `merge_init` establishes the complete state package needed at the head of
the top-level scan. -/
theorem initialMergeState_package
    (lt : BoolComparator κ) (hasKeyfunc : Bool) (input : SortSlice κ ν)
    (hsize : input.entries.size ≤ PY_LIST_MAX)
    (hMode : SortSlice.ValuesModeInvariant hasKeyfunc input) :
    InitialMergeStatePackage lt hasKeyfunc input
      (initialMergeState lt hasKeyfunc input).1 := by
  let listWord : PySSize := BitVec.ofNat 64 input.entries.size
  have hword : listWord.toNat = input.entries.size :=
    listSizeWord_toNat hsize
  have hnonnegative : listWord.Nonnegative :=
    listSizeWord_nonnegative hsize
  have hwordMax : listWord.toNat ≤ PY_LIST_MAX := by
    simpa [hword] using hsize
  have htempInv := mergeInitTemp_inv (κ := κ) (ν := ν) listWord hasKeyfunc
    hwordMax
  have htempLive :
      (mergeInitTemp (κ := κ) (ν := ν) listWord hasKeyfunc).storage.Live := by
    simp [mergeInitTemp, TempStorage.Live]
  have hstopped := minrunInit_stops_and_exponent_lt_64 listWord hnonnegative
    hwordMax
  refine
    { exactState := rfl
      listlenRoundtrip := ?_
      listlenNonnegative := ?_
      basekeys := ?_
      data := ?_
      pending := ?_
      pendingLayout := ?_
      poweredPrefix := ?_
      tempInvariant := ?_
      tempLive := ?_
      logicalCapacity := ?_
      physicalSlotsBound := ?_
      hasValues := ?_
      valuesMode := ?_
      comparator := ?_
      minrunState := ?_
      minrunStopped := ?_ }
  · simpa [initialMergeState, minrunInitTraced, listWord] using hword
  · simpa [initialMergeState, minrunInitTraced, listWord] using hnonnegative
  · simp [initialMergeState]
  · simp [initialMergeState]
  · simp [initialMergeState]
  · simp [PendingLayout, PendingRunsCover, initialMergeState,
      minrunInitTraced, listWord, hword, hnonnegative]
  · simp [PoweredPrefix, initialMergeState]
  · simpa [initialMergeState, listWord] using htempInv
  · simpa [initialMergeState, listWord] using htempLive
  · exact TempStorageInv.cells_size_eq
      (by simpa [initialMergeState, listWord] using htempInv)
      (by simpa [initialMergeState, listWord] using htempLive)
  · let initialized :=
      mergeInitTemp (κ := κ) (ν := ν) listWord hasKeyfunc
    have hinline : initialized.storage.backing = .inline := by
      simp [initialized, mergeInitTemp]
    have hinitializedInv :
        TempStorageInv initialized.storage initialized.alloced := by
      simpa [initialized] using htempInv
    have hinlineInv :
        initialized.storage.cells.size = initialized.alloced.toNat ∧
          initialized.storage.multiplier * initialized.alloced.toNat ≤
            MERGESTATE_TEMP_SIZE := by
      simpa only [TempStorageInv, hinline] using hinitializedInv
    have hslots :
        initialized.storage.physicalSlots ≤ MERGESTATE_TEMP_SIZE := by
      rw [TempStorage.physicalSlots, hinlineInv.1]
      exact hinlineInv.2
    have hplatform :
        MERGESTATE_TEMP_SIZE ≤
          PY_SSIZE_T_MAX / PY_OBJECT_PTR_BYTES := by
      norm_num [MERGESTATE_TEMP_SIZE, PY_SSIZE_T_MAX, PY_OBJECT_PTR_BYTES]
    simpa [initialMergeState, listWord, initialized] using
      hslots.trans hplatform
  · simp [initialMergeState, mergeInitTemp]
  · simpa [initialMergeState, mergeInitTemp] using hMode
  · simp [initialMergeState]
  · simp [initialMergeState, MergeState.minrunState, minrunInit,
      minrunInitTraced]
  · simpa [initialMergeState, listWord] using hstopped.1

/-! ## Adaptive-minrun scan invariant -/

/-- Repeated `minrun_next` calls compose by running the requested prefix and
then continuing from its final state. -/
theorem minrunNextN_add (first later : Nat) (state : MinrunState) :
    let prior := minrunNextN first state
    let suffix := minrunNextN later prior.state
    (minrunNextN (first + later) state).state = suffix.state ∧
      (minrunNextN (first + later) state).outputs =
        prior.outputs ++ suffix.outputs ∧
      (minrunNextN (first + later) state).assertionsPassed =
        (prior.assertionsPassed && suffix.assertionsPassed) := by
  induction first generalizing state with
  | zero => simp [minrunNextN]
  | succ first ih =>
      simp only [Nat.succ_add, minrunNextN]
      let next := minrunNext state
      rcases ih next.state with ⟨hstate, houtputs, hassertions⟩
      refine ⟨hstate, ?_, ?_⟩
      · simpa only [next, List.cons_append] using
          congrArg (fun outputs => next.result.toNat :: outputs) houtputs
      · change
          (next.assertionPassed &&
              (minrunNextN (first + later) next.state).assertionsPassed) = _
        rw [hassertions]
        exact (Bool.and_assoc _ _ _).symm

/-- Appending one generator call adds exactly its result at the end of the
already-emitted prefix and installs its state. -/
theorem minrunNextN_succ (calls : Nat) (state : MinrunState) :
    let prior := minrunNextN calls state
    let next := minrunNext prior.state
    (minrunNextN (calls + 1) state).state = next.state ∧
      (minrunNextN (calls + 1) state).outputs =
        prior.outputs ++ [next.result.toNat] ∧
      (minrunNextN (calls + 1) state).assertionsPassed =
        (prior.assertionsPassed && next.assertionPassed) := by
  simpa [minrunNextN] using minrunNextN_add calls 1 state

/-- State carried between scan iterations. `emittedLeScanned` records that
every already-emitted minrun target was covered by the actual runs consumed so
far; natural runs may make the inequality strict. -/
structure AdaptiveMinrunScanInvariant
    (listSize : PySSize) (calls scanned : Nat) (state : MinrunState) : Prop where
  listNonnegative : listSize.Nonnegative
  listMax : listSize.toNat ≤ PY_LIST_MAX
  stateEq : state = (minrunNextN calls (minrunInit listSize)).state
  emittedLeScanned :
    (minrunNextN calls (minrunInit listSize)).outputs.sum ≤ scanned
  scannedBound : scanned ≤ listSize.toNat

/-- The initialized generator satisfies the scan invariant before any input is
consumed. -/
theorem adaptiveMinrunScanInvariant_initial
    (listSize : PySSize) (hNonnegative : listSize.Nonnegative)
    (hMax : listSize.toNat ≤ PY_LIST_MAX) :
    AdaptiveMinrunScanInvariant listSize 0 0 (minrunInit listSize) := by
  constructor
  · exact hNonnegative
  · exact hMax
  · rfl
  · simp [minrunNextN]
  · simp

/-- Facts about the next adaptive target on an active valid scan. -/
structure AdaptiveMinrunStepFacts
    (listSize : PySSize) (calls scanned : Nat) (state : MinrunState) : Prop where
  assertionPassed : (minrunNext state).assertionPassed = true
  targetPositive : 1 ≤ (minrunNext state).result.toNat
  targetMax : (minrunNext state).result.toNat ≤ MAX_MINRUN.toNat
  nextState :
    (minrunNext state).state =
      (minrunNextN (calls + 1) (minrunInit listSize)).state
  emittedOutputs :
    (minrunNextN (calls + 1) (minrunInit listSize)).outputs =
      (minrunNextN calls (minrunInit listSize)).outputs ++
        [(minrunNext state).result.toNat]

/-- The next `minrun_next` call on an active valid scan passes its signed
assertion and returns its actual target in `1 .. MAX_MINRUN`. -/
theorem adaptiveMinrun_step_facts
    {listSize : PySSize} {calls scanned : Nat} {state : MinrunState}
    (hInv : AdaptiveMinrunScanInvariant listSize calls scanned state)
    (hActive : scanned < listSize.toNat) :
    AdaptiveMinrunStepFacts listSize calls scanned state := by
  let prior := minrunNextN calls (minrunInit listSize)
  have hstate : state = prior.state := by simpa [prior] using hInv.stateEq
  have hsucc := minrunNextN_succ calls (minrunInit listSize)
  have hnextState :
      (minrunNext state).state =
        (minrunNextN (calls + 1) (minrunInit listSize)).state := by
    rw [hstate]
    exact hsucc.1.symm
  have houtputs :
      (minrunNextN (calls + 1) (minrunInit listSize)).outputs =
        (minrunNextN calls (minrunInit listSize)).outputs ++
          [(minrunNext state).result.toNat] := by
    rw [hstate]
    exact hsucc.2.1
  have hpositive : 0 < listSize.toNat := by omega
  have hbounds := minrunNext_after_init_bounds listSize hInv.listNonnegative
    hInv.listMax hpositive calls
  dsimp only at hbounds
  rw [← hstate] at hbounds
  exact
    { assertionPassed := hbounds.1
      targetPositive := hbounds.2.1
      targetMax := hbounds.2.2
      nextState := hnextState
      emittedOutputs := houtputs }

/-- After the caller consumes at least the emitted target, the updated
generator state satisfies the invariant for the next scan iteration. -/
theorem AdaptiveMinrunScanInvariant.advance
    {listSize : PySSize} {calls scanned consumed : Nat} {state : MinrunState}
    (hInv : AdaptiveMinrunScanInvariant listSize calls scanned state)
    (hActive : scanned < listSize.toNat)
    (hTargetConsumed : (minrunNext state).result.toNat ≤ consumed)
    (hNextScanned : scanned + consumed ≤ listSize.toNat) :
    AdaptiveMinrunScanInvariant listSize (calls + 1) (scanned + consumed)
      (minrunNext state).state := by
  have hstep := adaptiveMinrun_step_facts hInv hActive
  refine
    { listNonnegative := hInv.listNonnegative
      listMax := hInv.listMax
      stateEq := hstep.nextState
      emittedLeScanned := ?_
      scannedBound := hNextScanned }
  rw [hstep.emittedOutputs, List.sum_append]
  simp only [List.sum_singleton]
  exact Nat.add_le_add hInv.emittedLeScanned hTargetConsumed

/-! ## Pending-layout and small-transition frames -/

/-- A positive scanned prefix cannot be represented by an empty pending stack. -/
theorem PendingLayout.pending_nonempty
    {state : MergeState κ ν} {scanned : Nat}
    (hLayout : PendingLayout state scanned) (hScanned : 0 < scanned) :
    state.pending.toList ≠ [] := by
  intro hempty
  have hcover := hLayout.2.2.2
  rw [hempty] at hcover
  simp [PendingRunsCover] at hcover
  omega

/-- Installing adaptive-minrun fields changes no unrelated `MergeState` field
and installs exactly the supplied projection. -/
theorem installMinrunState_frame (state : MergeState κ ν)
    (minrun : MinrunState) :
    let after := installMinrunState state minrun
    after.minrunState = minrun ∧
      after.min_gallop = state.min_gallop ∧
      after.basekeys = state.basekeys ∧
      after.data = state.data ∧
      after.a = state.a ∧
      after.alloced = state.alloced ∧
      after.pending = state.pending ∧
      after.key_compare = state.key_compare := by
  simp [installMinrunState, MergeState.minrunState]

/-- The unconditional pending push changes only the pending array. -/
theorem pushPendingRun_frame (state : MergeState κ ν) (run : PendingRun) :
    let after := pushPendingRun state run
    after.listlen = state.listlen ∧
      after.basekeys = state.basekeys ∧
      after.data = state.data ∧
      after.a = state.a ∧
      after.alloced = state.alloced ∧
      after.key_compare = state.key_compare ∧
      after.minrunState = state.minrunState ∧
      after.pending.toList = state.pending.toList ++ [run] := by
  simp [pushPendingRun, MergeState.minrunState]

/-- Pushing a pending run preserves the active storage and values-mode package
because it mutates only the pending array. -/
theorem pushPendingRun_preserves_activePackage
    (state : MergeState κ ν) (run : PendingRun)
    (hInv : TempStorageInv state.a state.alloced)
    (hLive : state.a.Live)
    (hMode : SortSlice.ValuesModeInvariant state.a.hasValues state.data) :
    TempStorageInv (pushPendingRun state run).a
        (pushPendingRun state run).alloced ∧
      (pushPendingRun state run).a.Live ∧
      SortSlice.ValuesModeInvariant (pushPendingRun state run).a.hasValues
        (pushPendingRun state run).data ∧
      (pushPendingRun state run).a.hasValues = state.a.hasValues := by
  constructor
  · simpa [pushPendingRun] using hInv
  constructor
  · simpa [pushPendingRun] using hLive
  constructor
  · simpa [pushPendingRun] using hMode
  · simp [pushPendingRun]

/-- Final cleanup preserves every non-storage field, the stale capacity and
mode metadata, and the representation invariant. Liveness is deliberately not
claimed after a heap-backed cleanup. -/
theorem mergeFreemem_frame (state : MergeState κ ν)
    (hInv : TempStorageInv state.a state.alloced) :
    let after := mergeFreemem state
    after.listlen = state.listlen ∧
      after.basekeys = state.basekeys ∧
      after.data = state.data ∧
      after.alloced = state.alloced ∧
      after.pending = state.pending ∧
      after.key_compare = state.key_compare ∧
      after.minrunState = state.minrunState ∧
      after.a.hasValues = state.a.hasValues ∧
      TempStorageInv after.a after.alloced := by
  unfold mergeFreemem
  split <;> simp_all [MergeState.minrunState, TempStorageInv]

/-! ## Final-reversal phase selection -/

/-- CPython's final reverse acts on saved values in keyed mode and on the key
array itself in unkeyed mode. -/
def finalReversePhase (hasValues : Bool) : ReverseSlicePhase :=
  if hasValues then .values else .keys

/-- The selected final phase is source-valid for the supplied storage mode. -/
theorem finalReversePhase_sourceValid (hasValues : Bool) :
    finalReversePhase hasValues = .keys ∨ hasValues = true := by
  cases hasValues <;> simp [finalReversePhase]

/-- Forgetting the phase-specific final-reverse trace recovers the reviewed
paired-snapshot reversal result. -/
theorem erase_finalReversePhaseTraced (hasValues : Bool)
    (slice : SortSlice κ ν) (lo hi : Int) :
    (reverseSlicePhaseTraced? (finalReversePhase hasValues)
      slice lo hi).erase = reverseSlice? slice lo hi := by
  exact erase_reverseSlicePhaseTraced _ _ _ _

/-- Safety specialization for the one physical phase used by CPython's final
top-level reversal. -/
theorem finalReversePhase_safe (hasValues : Bool) (slice : SortSlice κ ν)
    (lo hi : Int) (hlo : 0 ≤ lo) (hhi : hi ≤ Int.ofNat slice.entries.size)
    (hordered : lo ≤ hi)
    (hMode : SortSlice.ValuesModeInvariant hasValues slice) :
    ∃ result,
      ReverseSlicePhaseSafetyPost (finalReversePhase hasValues) slice lo hi
        hasValues result := by
  exact reverseSlicePhaseTraced_safe (finalReversePhase hasValues) slice lo hi
    hasValues hlo hhi hordered (finalReversePhase_sourceValid hasValues) hMode

end CPythonListsort
