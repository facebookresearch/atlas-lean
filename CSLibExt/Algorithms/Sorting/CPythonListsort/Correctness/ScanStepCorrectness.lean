/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Code.Assembly.ListSortTermination
import Code.Correctness.BinarysortCorrectness
import Code.Correctness.CountRunCorrectness
import Code.Correctness.FoundNewRunCorrectness
import Code.Correctness.ScanCorrectnessSupport
import Code.Correctness.ScanStepSupport

/-!
# Correctness of one forward scan iteration

This module stops at the recursive-call boundary of `listSortScan?`.  It
combines the already-reviewed safety invariant with pending-run correctness,
the whole-entry unscanned snapshot, and the persistent input permutation.
-/

namespace CPythonListsort

universe u v

variable {α : Type u} {ν : Type v}

/-- Full induction invariant for the occurrence-carrying forward scan. -/
structure ListSortScanCorrectnessInvariant
    (lt : BoolComparator α) (source : SortSlice α ν) (hasKeyfunc : Bool)
    (inputSize : Nat) (state : MergeState (Occurrence α) ν)
    (lo scanned remaining : Nat) : Prop where
  safety : ListSortScanInvariant (occurrenceComparator lt) hasKeyfunc inputSize
    state lo scanned remaining
  pendingRunsCorrect : PendingRunsCorrect lt
    (source.entries.map SortSliceEntry.key) state scanned
  remainderEntries : ScanRemainderEntriesMatch source state scanned
  entrySnapshot : EntrySnapshotPermutation source state.data

/-- Observable result of exactly one nonterminal scan iteration.  The equation
mentions the real raw evaluator and exposes the precise recursive call. -/
structure ListSortScanStepCorrectnessPost
    (lt : BoolComparator α) (source : SortSlice α ν) (hasKeyfunc : Bool)
    (inputSize fuel : Nat) (state : MergeState (Occurrence α) ν)
    (lo scanned remaining : Nat) (reverse : Bool)
    (consumed : Nat) (nextState : MergeState (Occurrence α) ν) : Prop where
  consumedPositive : 0 < consumed
  consumedWithin : consumed ≤ remaining
  consumedPrefixFrame : SortSlice.EqualOutsideRange state.data nextState.data
    state.basekeys (scanned + consumed)
  scanEquation :
    listSortScan? (fuel + 1) state lo remaining reverse inputSize =
      listSortScan? fuel nextState (lo + consumed) (remaining - consumed)
        reverse inputSize
  nextInvariant : ListSortScanCorrectnessInvariant lt source hasKeyfunc
    inputSize nextState (lo + consumed) (scanned + consumed)
      (remaining - consumed)

/-- Abstract form of the `foundNewRun_correct` call used by the step proof.
The concrete public theorem below instantiates this provider; keeping the core
parameterized also makes the merge dependency explicit. -/
private def FoundNewRunCorrectnessProvider
    (lt : BoolComparator α) (input : Array α) (source : SortSlice α ν) : Prop :=
  ∀ (state : MergeState (Occurrence α) ν) (scanned : Nat)
    (newRun : PendingRun),
    PendingRunsCorrect lt input state scanned →
    EntrySnapshotPermutation source state.data →
    state.key_compare = occurrenceComparator lt →
    state.listlen.toNat ≤ PY_LIST_MAX →
    PoweredPrefix state →
    newRun.base = state.basekeys + scanned →
    newRun.len.Nonnegative →
    0 < newRun.len.toNat →
    scanned + newRun.len.toNat ≤ state.listlen.toNat →
    TempStorageInv state.a state.alloced →
    state.a.Live →
    SortSlice.ValuesModeInvariant state.a.hasValues state.data →
    ∃ result,
      FoundNewRunCorrectnessPost lt input source state scanned newRun result

/-- Internal boundary between run formation (`count_run` plus optional
`binarysort`) and the policy/push phase.  The explicit `stable` field is the
whole-target premise/output at the binarysort boundary. -/
private structure ListSortRunFormationPost
    (lt : BoolComparator α) (source : SortSlice α ν) (hasKeyfunc : Bool)
    (inputSize fuel : Nat) (call : MergeState (Occurrence α) ν)
    (lo scanned remaining : Nat) (reverse : Bool)
    (formed : MergeState (Occurrence α) ν) (consumed : Nat) : Prop where
  positive : 0 < consumed
  within : consumed ≤ remaining
  listlen : formed.listlen = call.listlen
  basekeys : formed.basekeys = call.basekeys
  extent : formed.data.entries.size = call.data.entries.size
  hasValues : formed.a.hasValues = call.a.hasValues
  comparator : formed.key_compare = call.key_compare
  tempInvariant : TempStorageInv formed.a formed.alloced
  tempLive : formed.a.Live
  physicalBound :
    (MergeMemorySnapshot.ofState formed).PhysicalBound
  valuesMode : SortSlice.ValuesModeInvariant formed.a.hasValues formed.data
  poweredPrefix : PoweredPrefix formed
  pendingRunsCorrect : PendingRunsCorrect lt
    (source.entries.map SortSliceEntry.key) formed scanned
  entrySnapshot : EntrySnapshotPermutation source formed.data
  frame : SortSlice.EqualOutsideRange call.data formed.data
    (call.basekeys + scanned) consumed
  sorted : Sorted (occurrenceComparator lt)
    (sortSliceRangeKeys formed.data (call.basekeys + scanned) consumed)
  stable : StableOccurrencePermutation lt
    (canonicalOccurrenceSegment (source.entries.map SortSliceEntry.key)
      (call.basekeys + scanned) consumed)
    (sortSliceRangeKeys formed.data
      (call.basekeys + scanned) consumed).toList
  adaptiveAfter : 0 < remaining - consumed →
    ∃ calls, AdaptiveMinrunScanInvariant formed.listlen calls
      (scanned + consumed) formed.minrunState
  scanEquationBeforeFound :
    listSortScan? (fuel + 1) call lo remaining reverse inputSize =
      listSortAfterExtension?
        (fun nextState nextLo nextRemaining =>
          listSortScan? fuel nextState nextLo nextRemaining reverse inputSize)
        lo remaining reverse inputSize (formed, consumed, false)

/-- `count_run` followed by the source-selected optional `binarysort` produces
one positive, sorted, canonically stable run and preserves every global scan
invariant not owned by `found_new_run`. -/
private theorem listSort_form_run_correct
    {lt : BoolComparator α} (horder : BoolStrictWeakOrder lt)
    {source : SortSlice α ν} {hasKeyfunc : Bool} {inputSize fuel : Nat}
    {state : MergeState (Occurrence α) ν} {lo scanned remaining : Nat}
    {reverse : Bool}
    (inv : ListSortScanCorrectnessInvariant lt source hasKeyfunc inputSize state
      lo scanned remaining)
    (hremaining : 0 < remaining) :
    ∃ formed consumed,
      ListSortRunFormationPost lt source hasKeyfunc inputSize fuel state lo
        scanned remaining reverse formed consumed := by
  have hremainingNe : remaining ≠ 0 := Nat.ne_of_gt hremaining
  have hremainingInput : remaining ≤ inputSize := by
    have hpartition := inv.safety.partition
    omega
  have hrange : SortSlice.RangeInBounds state.data (Int.ofNat lo) remaining := by
    constructor
    · exact Int.natCast_nonneg lo
    · rw [inv.safety.dataExtent]
      have hpartition := inv.safety.partition
      have hstop : lo + remaining ≤ inputSize := by
        have hcursor := inv.safety.cursor
        rw [inv.safety.basekeys] at hcursor
        omega
      simpa only [Int.ofNat_eq_natCast, Nat.cast_add] using
        (Int.ofNat_le.mpr hstop)
  have hremainingSsize : remaining ≤ PY_SSIZE_T_MAX := by
    have hMaxLe : PY_LIST_MAX ≤ PY_SSIZE_T_MAX := by
      norm_num [PY_LIST_MAX, PY_SSIZE_T_MAX, PY_OBJECT_PTR_BYTES]
    exact hremainingInput.trans (inv.safety.inputSizeMax.trans hMaxLe)
  have hbaseNat : (Int.ofNat lo).toNat = state.basekeys + scanned := by
    simpa using inv.safety.cursor
  have hstart : lo = state.basekeys + scanned := by
    simpa using inv.safety.cursor
  have hremainingEq : state.listlen.toNat - scanned = remaining := by
    rw [inv.safety.listlen]
    have hpartition := inv.safety.partition
    omega
  have hcanonical : CountRunCanonicalRange lt state.data lo remaining := by
    have hcanonical' := inv.remainderEntries.countRunCanonicalRange (lt := lt)
    simpa [hstart, hremainingEq] using hcanonical'
  rcases countRun_correct lt horder state state.data (Int.ofNat lo) remaining
      inv.safety.comparator hrange hremaining hremainingSsize
      inv.safety.valuesMode hcanonical with
    ⟨counted, hcounted⟩
  have hcountRaw : countRun? state state.data (Int.ofNat lo) remaining =
      some counted := by
    rw [← hcounted.safety.exactErasure]
    simpa [TraceResult.erase] using hcounted.safety.resultEq
  have hscanCount :
      listSortScan? (fuel + 1) state lo remaining reverse inputSize =
        listSortAfterCount?
          (fun nextState nextLo nextRemaining =>
            listSortScan? fuel nextState nextLo nextRemaining reverse inputSize)
          state lo remaining reverse inputSize counted := by
    rw [listSortScan?]
    simp only [hremainingNe, if_false, hcountRaw]
    rfl
  have hcountedValid :
      ¬(counted.length = 0 ∨ remaining < counted.length) := by
    have hpositive := hcounted.lengthBounds.1
    have hwithin := hcounted.lengthBounds.2
    omega
  let countedState : MergeState (Occurrence α) ν :=
    { state with data := counted.slice }
  have hcountFrame : SortSlice.EqualOutsideRange state.data countedState.data
      (state.basekeys + scanned) counted.length := by
    rw [← hbaseNat]
    simpa [countedState] using hcounted.frame
  have hcountPending : PendingRunsCorrect lt
      (source.entries.map SortSliceEntry.key) countedState scanned := by
    exact inv.pendingRunsCorrect.preserve_unscanned_update rfl rfl rfl
      hcountFrame
  have hcountStop : lo + counted.length ≤ state.data.entries.size := by
    rw [inv.safety.dataExtent]
    have hpartition := inv.safety.partition
    have hcursor := inv.safety.cursor
    rw [inv.safety.basekeys] at hcursor
    omega
  have hcountSnapshot : EntrySnapshotPermutation source countedState.data := by
    simpa [countedState] using
      inv.entrySnapshot.preserve_countRun hcounted hcountStop
  rcases inv.safety.adaptive hremaining with ⟨calls, hAdaptive⟩
  have hAdaptiveCounted : AdaptiveMinrunScanInvariant countedState.listlen calls
      scanned countedState.minrunState := by
    simpa [countedState, MergeState.minrunState] using hAdaptive
  have hActive : scanned < countedState.listlen.toNat := by
    simp only [countedState]
    rw [inv.safety.listlen]
    have hpartition := inv.safety.partition
    omega
  have hStep := adaptiveMinrun_step_facts hAdaptiveCounted hActive
  let nextMinrun := minrunNext countedState.minrunState
  let installed := installMinrunState countedState nextMinrun.state
  let target := nextMinrun.result.toNat
  let force := if remaining ≤ target then remaining else target
  have hTargetPositive : 1 ≤ target := by
    simpa [target, nextMinrun] using hStep.targetPositive
  have hTargetMax : target ≤ MAX_MINRUN.toNat := by
    simpa [target, nextMinrun] using hStep.targetMax
  have hForcePositive : 1 ≤ force := by
    dsimp [force]
    split <;> omega
  have hForceRemaining : force ≤ remaining := by
    dsimp [force]
    split <;> omega
  have hForceMax : force ≤ MAX_MINRUN.toNat := by
    dsimp [force]
    split <;> omega
  have hInstalledListlen : installed.listlen = state.listlen := by
    simp [installed, nextMinrun, countedState, installMinrunState,
      minrunNext, MergeState.minrunState]
  have hInstalledBasekeys : installed.basekeys = state.basekeys := by
    simp [installed, countedState, installMinrunState]
  have hInstalledData : installed.data = counted.slice := by
    rfl
  have hInstalledDataSize : installed.data.entries.size =
      state.data.entries.size := by
    simpa [installed, countedState, installMinrunState] using
      hcounted.safety.sizeEq
  have hInstalledPending : installed.pending.toList = state.pending.toList := by
    simp [installed, countedState, installMinrunState]
  have hInstalledCorrect : PendingRunsCorrect lt
      (source.entries.map SortSliceEntry.key) installed scanned := by
    have hframe : SortSlice.EqualOutsideRange countedState.data installed.data
        (countedState.basekeys + scanned) 0 := by
      apply SortSlice.EqualOutsideRange.of_eq
      rfl
    apply hcountPending.preserve_unscanned_update
    · simpa [countedState] using hInstalledListlen
    · rfl
    · rfl
    · exact hframe
  have hInstalledSnapshot : EntrySnapshotPermutation source installed.data := by
    simpa [installed, countedState, installMinrunState] using hcountSnapshot
  have hInstalledPowered : PoweredPrefix installed := by
    have hpowered := inv.safety.poweredPrefix
    unfold PoweredPrefix at hpowered ⊢
    rw [hInstalledListlen, hInstalledBasekeys, hInstalledPending]
    exact hpowered
  have hInstalledInv : TempStorageInv installed.a installed.alloced := by
    simpa [installed, countedState, installMinrunState] using
      inv.safety.tempInvariant
  have hInstalledLive : installed.a.Live := by
    simpa [installed, countedState, installMinrunState] using inv.safety.tempLive
  have hInstalledMode :
      SortSlice.ValuesModeInvariant installed.a.hasValues installed.data := by
    simpa [installed, countedState, installMinrunState] using
      hcounted.safety.valuesMode
  have hInstalledHasValues : installed.a.hasValues = state.a.hasValues := by
    rfl
  have hInstalledComparator : installed.key_compare = state.key_compare := by
    rfl
  have hInstalledMax : installed.listlen.toNat ≤ PY_LIST_MAX := by
    rw [hInstalledListlen, inv.safety.listlen]
    exact inv.safety.inputSizeMax
  have hInstalledBase : lo = installed.basekeys + scanned := by
    rw [hInstalledBasekeys]
    exact inv.safety.cursor
  have hInstalledRange : SortSlice.RangeInBounds installed.data
      (Int.ofNat lo) force := by
    constructor
    · exact Int.natCast_nonneg lo
    · have hstop : lo + force ≤ installed.data.entries.size := by
        rw [hInstalledDataSize, inv.safety.dataExtent]
        have hpartition := inv.safety.partition
        have hcursor := inv.safety.cursor
        rw [inv.safety.basekeys] at hcursor
        omega
      simpa only [Int.ofNat_eq_natCast, Nat.cast_add] using
        (Int.ofNat_le.mpr hstop)
  have hForceRemainder : force ≤ state.listlen.toNat - scanned := by
    rw [hremainingEq]
    exact hForceRemaining
  have hRunWordNonnegative :
      PySSize.Nonnegative (BitVec.ofNat 64 counted.length) := by
    apply listSizeWord_nonnegative
    exact hcounted.lengthBounds.2.trans
      (hremainingInput.trans inv.safety.inputSizeMax)
  have hTargetNonnegative : nextMinrun.result.Nonnegative := by
    apply pySSize_nonnegative_of_toNat_le_maxMinrun
    simpa [target] using hTargetMax
  have hSignedCompare := pySSize_slt_eq_nat_lt
    (BitVec.ofNat 64 counted.length : PySSize) nextMinrun.result
    hRunWordNonnegative hTargetNonnegative
  by_cases hExtend :
      (BitVec.ofNat 64 counted.length : PySSize).slt nextMinrun.result = true
  · have hRunLtTarget : counted.length < target := by
      rw [hSignedCompare,
        listSizeWord_toNat
          (hcounted.lengthBounds.2.trans
            (hremainingInput.trans inv.safety.inputSizeMax))] at hExtend
      exact of_decide_eq_true hExtend
    have hRunForce : counted.length ≤ force := by
      dsimp [force]
      split <;> omega
    have hCountSorted : Sorted (occurrenceComparator lt)
        (sortSliceRangeKeys installed.data lo counted.length) := by
      simpa [hInstalledData] using hcounted.sorted
    have hBinaryStableInput : StableOccurrencePermutation lt
        (canonicalOccurrenceSegment
          (source.entries.map SortSliceEntry.key) lo force)
        (sortSliceRangeKeys installed.data lo force).toList := by
      have hstable := hcounted.stable_for_forced_range inv.remainderEntries
        hbaseNat hRunForce hForceRemainder
      simpa [hInstalledData, hstart] using hstable
    rcases binarysort_correct horder
        (canonicalOccurrenceSegment
          (source.entries.map SortSliceEntry.key) lo force)
        installed (hInstalledComparator.trans inv.safety.comparator) installed.data
        lo force counted.length hForcePositive hRunForce hForceMax
        hInstalledRange hInstalledMode hCountSorted hBinaryStableInput with
      ⟨sorted, hsorted⟩
    have hbinaryRaw : binarysort? installed installed.data (Int.ofNat lo) force
        counted.length = some sorted := by
      rw [← hsorted.safety.exactErasure]
      simpa [TraceResult.erase] using hsorted.safety.resultEq
    let extended : MergeState (Occurrence α) ν :=
      { installed with data := sorted.slice }
    have hbinaryFrame : SortSlice.EqualOutsideRange installed.data extended.data
        (state.basekeys + scanned) force := by
      simpa [extended, hstart] using hsorted.frame
    have hExtendedCorrect : PendingRunsCorrect lt
        (source.entries.map SortSliceEntry.key) extended scanned := by
      exact hInstalledCorrect.preserve_unscanned_update rfl rfl rfl hbinaryFrame
    have hBinaryStop : lo + force ≤ installed.data.entries.size := by
      rcases hInstalledRange with ⟨_, hend⟩
      exact Int.ofNat_le.mp (by simpa only [Int.ofNat_eq_natCast,
        Nat.cast_add] using hend)
    have hExtendedSnapshot : EntrySnapshotPermutation source extended.data := by
      simpa [extended] using
        hInstalledSnapshot.preserve_binarysort hsorted hBinaryStop
    have hCountFrameForced : SortSlice.EqualOutsideRange state.data
        installed.data (state.basekeys + scanned) force := by
      have hwiden := hcountFrame.widen
        (bigStart := state.basekeys + scanned) (bigCount := force)
        le_rfl (by omega)
      simpa [installed, countedState, installMinrunState] using hwiden
    have hExtendedFrame : SortSlice.EqualOutsideRange state.data extended.data
        (state.basekeys + scanned) force :=
      hCountFrameForced.trans hbinaryFrame
    have hExtendedSorted : Sorted (occurrenceComparator lt)
        (sortSliceRangeKeys extended.data (state.basekeys + scanned) force) := by
      simpa [extended, hstart] using hsorted.sorted
    have hExtendedStable : StableOccurrencePermutation lt
        (canonicalOccurrenceSegment
          (source.entries.map SortSliceEntry.key)
          (state.basekeys + scanned) force)
          (sortSliceRangeKeys extended.data
          (state.basekeys + scanned) force).toList := by
      simpa [extended, hstart] using hsorted.stable
    have hExtendedPowered : PoweredPrefix extended := by
      unfold PoweredPrefix at hInstalledPowered ⊢
      simpa [extended] using hInstalledPowered
    have hAdaptiveAfter : 0 < remaining - force →
        ∃ nextCalls, AdaptiveMinrunScanInvariant extended.listlen nextCalls
          (scanned + force) extended.minrunState := by
      intro hStillActive
      refine ⟨calls + 1, ?_⟩
      have hNotClipped : ¬remaining ≤ target := by
        intro hClipped
        have hForceEq : force = remaining := by simp [force, hClipped]
        rw [hForceEq] at hStillActive
        simp at hStillActive
      have hForceEq : force = target := by simp [force, hNotClipped]
      have hTargetConsumed : nextMinrun.result.toNat ≤ force := by
        simpa [target] using hForceEq.symm.le
      have hNextScanned : scanned + force ≤ countedState.listlen.toNat := by
        simp only [countedState]
        rw [inv.safety.listlen]
        have hpartition := inv.safety.partition
        omega
      have hAdvanced := hAdaptiveCounted.advance (consumed := force) hActive
        hTargetConsumed hNextScanned
      have hExtendedMinrun : extended.minrunState = nextMinrun.state := by
        change installed.minrunState = nextMinrun.state
        exact (installMinrunState_frame countedState nextMinrun.state).1
      rw [show extended.listlen = state.listlen by
          simpa [extended] using hInstalledListlen,
        hExtendedMinrun]
      simpa [nextMinrun, countedState] using hAdvanced
    have hformationEquation :
        listSortScan? (fuel + 1) state lo remaining reverse inputSize =
          listSortAfterExtension?
            (fun nextState nextLo nextRemaining =>
              listSortScan? fuel nextState nextLo nextRemaining reverse inputSize)
            lo remaining reverse inputSize (extended, force, false) := by
      rw [hscanCount]
      unfold listSortAfterCount?
      simp only [hcounted.safety.resultFuel, Bool.false_eq_true, if_false,
        hcountedValid]
      dsimp only [countedState, nextMinrun, installed, target, force]
      rw [if_pos hExtend, hbinaryRaw]
      simp only [hsorted.safety.resultFuel]
      rfl
    refine ⟨extended, force, ?_⟩
    exact
      { positive := hForcePositive
        within := hForceRemaining
        listlen := by simpa [extended] using hInstalledListlen
        basekeys := by simpa [extended] using hInstalledBasekeys
        extent := by
          simpa [extended] using hsorted.safety.sizeEq.trans hInstalledDataSize
        hasValues := by simpa [extended] using hInstalledHasValues
        comparator := by simpa [extended] using hInstalledComparator
        tempInvariant := by simpa [extended] using hInstalledInv
        tempLive := by simpa [extended] using hInstalledLive
        physicalBound := by
          simpa [extended, installed, countedState, installMinrunState,
            MergeMemorySnapshot.PhysicalBound,
            MergeMemorySnapshot.ofState] using inv.safety.physicalSlotsBound
        valuesMode := by simpa [extended] using hsorted.safety.valuesMode
        poweredPrefix := hExtendedPowered
        pendingRunsCorrect := hExtendedCorrect
        entrySnapshot := hExtendedSnapshot
        frame := hExtendedFrame
        sorted := hExtendedSorted
        stable := hExtendedStable
        adaptiveAfter := hAdaptiveAfter
        scanEquationBeforeFound := hformationEquation }
  · have hRunNotLtTarget : ¬counted.length < target := by
      intro hlt
      apply hExtend
      rw [hSignedCompare,
        listSizeWord_toNat
          (hcounted.lengthBounds.2.trans
            (hremainingInput.trans inv.safety.inputSizeMax))]
      exact decide_eq_true hlt
    have hTargetRun : target ≤ counted.length := by omega
    have hCountStable : StableOccurrencePermutation lt
        (canonicalOccurrenceSegment
          (source.entries.map SortSliceEntry.key)
          (state.basekeys + scanned) counted.length)
        (sortSliceRangeKeys installed.data
          (state.basekeys + scanned) counted.length).toList := by
      have hstable := hcounted.stable_from_remainder inv.remainderEntries
        hbaseNat (by rw [hremainingEq]; exact hcounted.lengthBounds.2)
      simpa [hInstalledData] using hstable
    have hCountSorted : Sorted (occurrenceComparator lt)
        (sortSliceRangeKeys installed.data
          (state.basekeys + scanned) counted.length) := by
      rw [← hbaseNat]
      simpa [hInstalledData] using hcounted.sorted
    have hAdaptiveAfter : 0 < remaining - counted.length →
        ∃ nextCalls, AdaptiveMinrunScanInvariant installed.listlen nextCalls
          (scanned + counted.length) installed.minrunState := by
      intro _
      refine ⟨calls + 1, ?_⟩
      have hNextScanned : scanned + counted.length ≤
          countedState.listlen.toNat := by
        simp only [countedState]
        rw [inv.safety.listlen]
        have hpartition := inv.safety.partition
        omega
      have hAdvanced := hAdaptiveCounted.advance hActive hTargetRun hNextScanned
      have hInstalledMinrun : installed.minrunState = nextMinrun.state :=
        (installMinrunState_frame countedState nextMinrun.state).1
      rw [hInstalledListlen, hInstalledMinrun]
      simpa [nextMinrun, countedState] using hAdvanced
    have hformationEquation :
        listSortScan? (fuel + 1) state lo remaining reverse inputSize =
          listSortAfterExtension?
            (fun nextState nextLo nextRemaining =>
              listSortScan? fuel nextState nextLo nextRemaining reverse inputSize)
            lo remaining reverse inputSize
            (installed, counted.length, false) := by
      rw [hscanCount]
      unfold listSortAfterCount?
      simp only [hcounted.safety.resultFuel, Bool.false_eq_true, if_false,
        hcountedValid]
      dsimp only [countedState, nextMinrun, installed, target, force]
      rw [if_neg hExtend]
    refine ⟨installed, counted.length, ?_⟩
    exact
      { positive := hcounted.lengthBounds.1
        within := hcounted.lengthBounds.2
        listlen := hInstalledListlen
        basekeys := hInstalledBasekeys
        extent := hInstalledDataSize
        hasValues := hInstalledHasValues
        comparator := hInstalledComparator
        tempInvariant := hInstalledInv
        tempLive := hInstalledLive
        physicalBound := by
          simpa [installed, countedState, installMinrunState,
            MergeMemorySnapshot.PhysicalBound,
            MergeMemorySnapshot.ofState] using inv.safety.physicalSlotsBound
        valuesMode := hInstalledMode
        poweredPrefix := hInstalledPowered
        pendingRunsCorrect := hInstalledCorrect
        entrySnapshot := hInstalledSnapshot
        frame := by
          simpa [installed, countedState, installMinrunState] using hcountFrame
        sorted := hCountSorted
        stable := hCountStable
        adaptiveAfter := hAdaptiveAfter
        scanEquationBeforeFound := hformationEquation }

/-- Assemble the semantic and safety invariants after a correct
`found_new_run` result and the transcription's unconditional push. -/
private theorem scanInvariant_after_correct_push
    {lt : BoolComparator α} {source : SortSlice α ν} {hasKeyfunc : Bool}
    {inputSize : Nat} {call formed : MergeState (Occurrence α) ν}
    {lo scanned remaining consumed : Nat}
    (inv : ListSortScanCorrectnessInvariant lt source hasKeyfunc inputSize call
      lo scanned remaining)
    (found : FoundNewRunResult (Occurrence α) ν)
    (hformedListlen : formed.listlen = call.listlen)
    (hformedBasekeys : formed.basekeys = call.basekeys)
    (hformedExtent : formed.data.entries.size = call.data.entries.size)
    (hformedHasValues : formed.a.hasValues = call.a.hasValues)
    (hformedComparator : formed.key_compare = call.key_compare)
    (hformedPhysical :
      (MergeMemorySnapshot.ofState formed).PhysicalBound)
    (hformedFrame : SortSlice.EqualOutsideRange call.data formed.data
      (call.basekeys + scanned) consumed)
    (hnewSorted : Sorted (occurrenceComparator lt)
      (sortSliceRangeKeys formed.data (call.basekeys + scanned) consumed))
    (hnewStable : StableOccurrencePermutation lt
      (canonicalOccurrenceSegment
        (source.entries.map SortSliceEntry.key)
        (call.basekeys + scanned) consumed)
      (sortSliceRangeKeys formed.data
        (call.basekeys + scanned) consumed).toList)
    (hpositive : 0 < consumed)
    (hwithin : consumed ≤ remaining)
    (hAdaptiveAfter : 0 < remaining - consumed →
      ∃ calls, AdaptiveMinrunScanInvariant formed.listlen calls
        (scanned + consumed) formed.minrunState)
    (hfound : FoundNewRunCorrectnessPost lt
      (source.entries.map SortSliceEntry.key) source formed scanned
      { base := lo, len := BitVec.ofNat 64 consumed, power := none } found) :
    let newRun : PendingRun :=
      { base := lo, len := BitVec.ofNat 64 consumed, power := none }
    let nextState := pushPendingRun found.state newRun
    SortSlice.EqualOutsideRange call.data nextState.data call.basekeys
        (scanned + consumed) ∧
      ListSortScanCorrectnessInvariant lt source hasKeyfunc inputSize nextState
        (lo + consumed) (scanned + consumed) (remaining - consumed) := by
  let newRun : PendingRun :=
    { base := lo, len := BitVec.ofNat 64 consumed, power := none }
  let nextState := pushPendingRun found.state newRun
  have hremainingInput : remaining ≤ inputSize := by
    have hpartition := inv.safety.partition
    omega
  have hconsumedMax : consumed ≤ PY_LIST_MAX := by
    exact hwithin.trans (hremainingInput.trans inv.safety.inputSizeMax)
  have hrunNat : newRun.len.toNat = consumed := by
    simpa [newRun] using listSizeWord_toNat hconsumedMax
  have hnewBaseCall : newRun.base = call.basekeys + scanned := by
    simpa [newRun] using inv.safety.cursor
  have hnewBaseFormed : newRun.base = formed.basekeys + scanned := by
    rw [hformedBasekeys]
    exact hnewBaseCall
  have hfoundRangeKeys := hfound.consumedFrame.keys_eq_of_disjoint
    newRun.base newRun.len.toNat (Or.inr (by rw [hnewBaseFormed]))
  have hnewSortedFound : Sorted (occurrenceComparator lt)
      (pendingRunOccurrenceKeys found.state newRun) := by
    rw [pendingRunOccurrenceKeys_eq_sortSliceRangeKeys]
    rw [← hfoundRangeKeys]
    simpa [hnewBaseCall, hrunNat] using hnewSorted
  have hnewStableFound : StableOccurrencePermutation lt
      (canonicalOccurrenceSegment
        (source.entries.map SortSliceEntry.key)
        (found.state.basekeys + scanned) newRun.len.toNat)
      (pendingRunOccurrenceKeys found.state newRun).toList := by
    rw [pendingRunOccurrenceKeys_eq_sortSliceRangeKeys]
    rw [← hfoundRangeKeys]
    rw [hfound.safety.stableFrame.basekeys, hrunNat, hformedBasekeys]
    simpa [hnewBaseCall] using hnewStable
  have hnextPending := hfound.pendingRunsCorrect.pushPendingRun
    hfound.safety.readyToPush hnewSortedFound hnewStableFound
  have hnextPending' : PendingRunsCorrect lt
      (source.entries.map SortSliceEntry.key) nextState
      (scanned + consumed) := by
    change PendingRunsCorrect lt (source.entries.map SortSliceEntry.key)
      (pushPendingRun found.state newRun) (scanned + consumed)
    rw [← hrunNat]
    exact hnextPending
  have hformedPrefix : SortSlice.EqualOutsideRange call.data formed.data
      call.basekeys (scanned + consumed) := by
    apply hformedFrame.widen
    · omega
    · omega
  have hfoundPrefix : SortSlice.EqualOutsideRange formed.data found.state.data
      call.basekeys (scanned + consumed) := by
    have hwiden := hfound.consumedFrame.widen
      (bigStart := call.basekeys) (bigCount := scanned + consumed)
      (by rw [hformedBasekeys]) (by rw [hformedBasekeys]; omega)
    exact hwiden
  have hprefixFrame : SortSlice.EqualOutsideRange call.data nextState.data
      call.basekeys (scanned + consumed) := by
    have htrans := hformedPrefix.trans hfoundPrefix
    simpa [nextState, pushPendingRun] using htrans
  have hconsumedRemainder :
      consumed ≤ call.listlen.toNat - scanned := by
    rw [inv.safety.listlen]
    have hpartition := inv.safety.partition
    omega
  have hremainderFormed := inv.remainderEntries.advance hconsumedRemainder
    hformedBasekeys hformedListlen hformedFrame
  have hfoundOldPrefix : SortSlice.EqualOutsideRange formed.data found.state.data
      formed.basekeys (scanned + consumed) := by
    exact hfound.consumedFrame.widen le_rfl (by omega)
  have hremainderFound := hremainderFormed.preserve_consumed_update
    hfound.safety.stableFrame.basekeys hfound.safety.stableFrame.listlen
    hfoundOldPrefix
  have hnextRemainder : ScanRemainderEntriesMatch source nextState
      (scanned + consumed) := by
    exact
      { scanned_le := by
          simpa [nextState, pushPendingRun] using hremainderFound.scanned_le
        state_stop_le := by
          simpa [nextState, pushPendingRun] using hremainderFound.state_stop_le
        source_stop_le := by
          simpa [nextState, pushPendingRun] using hremainderFound.source_stop_le
        entries_eq := by
          simpa [nextState, pushPendingRun] using hremainderFound.entries_eq }
  have hnextSnapshot : EntrySnapshotPermutation source nextState.data := by
    simpa [nextState, pushPendingRun] using hfound.entrySnapshot
  have hnextSafety := listSortScanInvariant_after_push
    (occurrenceComparator lt) hasKeyfunc inputSize formed lo scanned remaining
    consumed found inv.safety.inputSizeLower inv.safety.inputSizeMax
    (by rw [hformedListlen, inv.safety.listlen])
    (by rw [hformedListlen]; exact inv.safety.listlenNonnegative)
    (by rw [hformedBasekeys]; exact inv.safety.basekeys)
    (by rw [hformedExtent]; exact inv.safety.dataExtent)
    (by rw [hformedBasekeys]; exact inv.safety.cursor)
    inv.safety.partition hpositive hwithin
    hformedPhysical
    (hformedHasValues.trans inv.safety.hasValues)
    (hformedComparator.trans inv.safety.comparator)
    hAdaptiveAfter hfound.safety
  refine ⟨hprefixFrame, ?_⟩
  exact
    { safety := by simpa [nextState, newRun] using hnextSafety
      pendingRunsCorrect := by
        exact hnextPending'
      remainderEntries := hnextRemainder
      entrySnapshot := hnextSnapshot }

/-- Core one-iteration theorem with the semantic `found_new_run` theorem made
explicit.  The public theorem below supplies the concrete provider. -/
private theorem listSortScan_step_correct_of_provider
    {lt : BoolComparator α} (horder : BoolStrictWeakOrder lt)
    {source : SortSlice α ν} {hasKeyfunc : Bool} {inputSize fuel : Nat}
    {state : MergeState (Occurrence α) ν} {lo scanned remaining : Nat}
    {reverse : Bool}
    (foundCorrect : FoundNewRunCorrectnessProvider lt
      (source.entries.map SortSliceEntry.key) source)
    (inv : ListSortScanCorrectnessInvariant lt source hasKeyfunc inputSize state
      lo scanned remaining)
    (hremaining : 0 < remaining) :
    ∃ consumed nextState,
      ListSortScanStepCorrectnessPost lt source hasKeyfunc inputSize fuel state
        lo scanned remaining reverse consumed nextState := by
  rcases listSort_form_run_correct (fuel := fuel) (reverse := reverse) horder inv
      hremaining with
    ⟨formed, consumed, hformed⟩
  let newRun : PendingRun :=
    { base := lo, len := BitVec.ofNat 64 consumed, power := none }
  have hremainingInput : remaining ≤ inputSize := by
    have hpartition := inv.safety.partition
    omega
  have hconsumedMax : consumed ≤ PY_LIST_MAX :=
    hformed.within.trans (hremainingInput.trans inv.safety.inputSizeMax)
  have hrunNat : newRun.len.toNat = consumed := by
    simpa [newRun] using listSizeWord_toNat hconsumedMax
  have hrunNonnegative : newRun.len.Nonnegative := by
    simpa [newRun] using listSizeWord_nonnegative hconsumedMax
  have hrunPositive : 0 < newRun.len.toNat := by
    rw [hrunNat]
    exact hformed.positive
  have hrunBase : newRun.base = formed.basekeys + scanned := by
    rw [hformed.basekeys]
    simpa [newRun] using inv.safety.cursor
  have hrunWithin : scanned + newRun.len.toNat ≤ formed.listlen.toNat := by
    calc
      scanned + newRun.len.toNat = scanned + consumed := by rw [hrunNat]
      _ ≤ scanned + remaining := Nat.add_le_add_left hformed.within scanned
      _ = inputSize := inv.safety.partition
      _ = formed.listlen.toNat := by
        rw [hformed.listlen, inv.safety.listlen]
  have hformedMax : formed.listlen.toNat ≤ PY_LIST_MAX := by
    rw [hformed.listlen, inv.safety.listlen]
    exact inv.safety.inputSizeMax
  rcases foundCorrect formed scanned newRun hformed.pendingRunsCorrect
      hformed.entrySnapshot
      (hformed.comparator.trans inv.safety.comparator) hformedMax
      hformed.poweredPrefix hrunBase hrunNonnegative hrunPositive hrunWithin
      hformed.tempInvariant hformed.tempLive hformed.valuesMode with
    ⟨found, hfound⟩
  let nextState := pushPendingRun found.state newRun
  have hassembled := scanInvariant_after_correct_push inv found
    hformed.listlen hformed.basekeys hformed.extent hformed.hasValues
    hformed.comparator hformed.physicalBound hformed.frame hformed.sorted hformed.stable
    hformed.positive hformed.within hformed.adaptiveAfter hfound
  have hprefix : SortSlice.EqualOutsideRange state.data nextState.data
      state.basekeys (scanned + consumed) := by
    simpa [nextState, newRun] using hassembled.1
  have hnextInvariant : ListSortScanCorrectnessInvariant lt source hasKeyfunc
      inputSize nextState (lo + consumed) (scanned + consumed)
        (remaining - consumed) := by
    simpa [nextState, newRun] using hassembled.2
  have hfoundRawWord : foundNewRun? formed newRun.len.toNat = some found := by
    rw [← hfound.safety.exactErasure]
    simpa [TraceResult.erase] using hfound.safety.resultEq
  have hfoundRaw : foundNewRun? formed consumed = some found := by
    simpa [hrunNat] using hfoundRawWord
  have hvalid : ¬(consumed = 0 ∨ remaining < consumed) := by
    intro hbad
    rcases hbad with hzero | htooLong
    · exact (Nat.ne_of_gt hformed.positive) hzero
    · exact (Nat.not_lt_of_ge hformed.within) htooLong
  have hscanEquation :
      listSortScan? (fuel + 1) state lo remaining reverse inputSize =
        listSortScan? fuel nextState (lo + consumed) (remaining - consumed)
          reverse inputSize := by
    rw [hformed.scanEquationBeforeFound]
    unfold listSortAfterExtension?
    simp only [Bool.false_eq_true, if_false, hvalid, hfoundRaw,
      hfound.safety.returnCode, hfound.safety.resultFuel, Bool.not_false,
      and_self, if_true]
    rfl
  exact
    ⟨consumed, nextState,
      { consumedPositive := hformed.positive
        consumedWithin := hformed.within
        consumedPrefixFrame := hprefix
        scanEquation := hscanEquation
        nextInvariant := hnextInvariant }⟩

/-- One complete nonterminal iteration of the real `listSortScan?` evaluator.
The returned state is exactly the evaluator's recursive-call state, carries
the full semantic scan invariant, and may include any strict-power merges
performed before the unconditional pending-run push. -/
theorem listSortScan_step_correct
    {lt : BoolComparator α} (horder : BoolStrictWeakOrder lt)
    {source : SortSlice α ν} {hasKeyfunc : Bool} {inputSize fuel : Nat}
    {state : MergeState (Occurrence α) ν} {lo scanned remaining : Nat}
    {reverse : Bool}
    (inv : ListSortScanCorrectnessInvariant lt source hasKeyfunc inputSize state
      lo scanned remaining)
    (hremaining : 0 < remaining) :
    ∃ consumed nextState,
      ListSortScanStepCorrectnessPost lt source hasKeyfunc inputSize fuel state
        lo scanned remaining reverse consumed nextState := by
  apply listSortScan_step_correct_of_provider horder ?_ inv hremaining
  intro formed formedScanned newRun hcorrect hsnapshot hcompare hmax hpowered
    hnewBase hnewNonnegative hnewPositive hnewWithin hInv hLive hMode
  exact foundNewRun_correct horder (source.entries.map SortSliceEntry.key)
    source formed formedScanned newRun hcorrect hsnapshot hcompare hmax hpowered
    hnewBase hnewNonnegative hnewPositive hnewWithin hInv hLive hMode

/-! ## Concrete branch witnesses -/

private def scanStepRegressionLt : BoolComparator Nat :=
  fun left right => decide (left < right)

private def scanStepRegressionEntry (value origin payload : Nat) :
    SortSliceEntry (Occurrence Nat) Nat :=
  { key := { value := value, origin := origin }, value := some payload }

private def scanStepExtensionSlice : SortSlice (Occurrence Nat) Nat :=
  { entries :=
      #[scanStepRegressionEntry 99 0 10,
        scanStepRegressionEntry 3 1 11,
        scanStepRegressionEntry 1 2 12,
        scanStepRegressionEntry 2 3 13,
        scanStepRegressionEntry 0 4 14,
        scanStepRegressionEntry 77 5 15] }

private def scanStepExtensionState : MergeState (Occurrence Nat) Nat :=
  (initialMergeState (occurrenceComparator scanStepRegressionLt) true
    scanStepExtensionSlice).1

private structure ScanStepExtensionRegressionView where
  returnCode : Int
  fuelExhausted : Bool
  pending : List (Nat × Nat)
  entries : List (Nat × Nat × Option Nat)
  deriving DecidableEq, Repr

private def scanStepExtensionRegressionView
    (result : ListSortImplResult (Occurrence Nat) Nat) :
    ScanStepExtensionRegressionView :=
  { returnCode := result.returnCode
    fuelExhausted := result.fuelExhausted
    pending := result.state.pending.toList.map (fun run =>
      (run.base, run.len.toNat))
    entries := result.state.data.entries.toList.map (fun entry =>
      (entry.key.value, entry.key.origin, entry.value)) }

private def scanStepExtensionRegressionExpected :
    ScanStepExtensionRegressionView :=
  { returnCode := 0
    fuelExhausted := false
    pending := [(1, 4)]
    entries :=
      [(99, 0, some 10), (0, 4, some 14), (1, 2, some 12),
       (2, 3, some 13), (3, 1, some 11), (77, 5, some 15)] }

set_option maxRecDepth 100000 in
set_option linter.style.nativeDecide false in
/-- Concrete extension witness through the real scan evaluator.  `count_run`
finds only the descending pair, while the scan sorts the full forced range of
four; the keyed payloads travel with their occurrences and both outside
sentinels remain byte-for-byte observable. -/
theorem listSortScan_short_run_extension_regression :
    (countRun? scanStepExtensionState scanStepExtensionState.data 1 4).map
        (fun counted => counted.length) = some 2 ∧
      (listSortScan? 1 scanStepExtensionState 1 4 false 6).map
        scanStepExtensionRegressionView =
        some scanStepExtensionRegressionExpected := by
  constructor <;> decide

private def scanStepNoExtensionSlice : SortSlice (Occurrence Nat) PUnit :=
  { entries := (Array.range 64).map fun index =>
      ({ key := { value := index, origin := index }, value := none } :
        SortSliceEntry (Occurrence Nat) PUnit) }

private def scanStepNoExtensionState : MergeState (Occurrence Nat) PUnit :=
  let initialized :=
    (initialMergeState (occurrenceComparator scanStepRegressionLt) false
      scanStepNoExtensionSlice).1
  { initialized with
    pending := #[{ base := 0, len := BitVec.ofNat 64 24, power := none }] }

set_option maxRecDepth 100000 in
set_option linter.style.nativeDecide false in
/-- Concrete no-extension witness through the real scan evaluator.  The
natural run has length `40`, strictly above the adaptive target `32`; it is
therefore consumed at its own length, pushed after the existing 24-element
prefix, and the final collapse recovers one unchanged 64-element run. -/
theorem listSortScan_long_run_no_extension_regression :
    (minrunNext scanStepNoExtensionState.minrunState).result.toNat = 32 ∧
      (countRun? scanStepNoExtensionState scanStepNoExtensionState.data 24 40).map
        (fun counted => counted.length) = some 40 ∧
      (listSortScanTraced? 1 scanStepNoExtensionState 24 40 false 64).trace.pushDepths =
        [2] ∧
      (listSortScan? 1 scanStepNoExtensionState 24 40 false 64).map
        (fun result =>
          (result.returnCode, result.fuelExhausted,
            result.state.pending.toList.map (fun run =>
              (run.base, run.len.toNat)),
            decide (result.state.data = scanStepNoExtensionSlice))) =
        some (0, false, [(0, 64)], true) := by
  native_decide

private def scanStepPolicyMergeEntry (value origin : Nat) :
    SortSliceEntry (Occurrence Nat) PUnit :=
  { key := { value := value, origin := origin }, value := none }

private def scanStepPolicyMergeState : MergeState (Occurrence Nat) PUnit :=
  { min_gallop := MIN_GALLOP
    listlen := 3
    basekeys := 0
    data :=
      { entries :=
          #[scanStepPolicyMergeEntry 2 0,
            scanStepPolicyMergeEntry 1 1,
            scanStepPolicyMergeEntry 3 2] }
    a := { cells := #[], backing := .inline, hasValues := false }
    alloced := 0
    pending :=
      #[{ base := 0, len := 1, power := some 3 },
        { base := 1, len := 1, power := none }]
    key_compare := occurrenceComparator scanStepRegressionLt
    mr_current := 0
    mr_e := 0
    mr_mask := 0 }

set_option maxRecDepth 100000 in
set_option linter.style.nativeDecide false in
/-- Concrete policy-merge-then-push witness through the real traced scan.  A
direct push from depth two would record depth three; the observed depth two
therefore pins the preceding strict-power merge before the unconditional
push.  Final collapse then produces the sorted three-element run. -/
theorem listSortScan_policy_merge_then_push_regression :
    (countRun? scanStepPolicyMergeState scanStepPolicyMergeState.data 2 1).map
        (fun counted => counted.length) = some 1 ∧
      (listSortScanTraced? 1 scanStepPolicyMergeState 2 1 false 3).trace.pushDepths =
        [2] ∧
      (listSortScan? 1 scanStepPolicyMergeState 2 1 false 3).map
        (fun result =>
          (result.returnCode, result.fuelExhausted,
            result.state.pending.toList.map (fun run =>
              (run.base, run.len.toNat)),
            result.state.data.entries.toList.map (fun entry =>
              (entry.key.value, entry.key.origin)))) =
        some (0, false, [(0, 3)], [(1, 1), (2, 0), (3, 2)]) := by
  native_decide

end CPythonListsort
