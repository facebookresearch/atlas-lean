/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Code.Assembly.ListSortMergePolicy

namespace CPythonListsort

universe u v
variable {κ : Type u} {ν : Type v}

theorem listSortScan_policyReplay_core :
    ∀ (fuel : Nat) (state : MergeState κ ν) (lo scanned remaining : Nat)
      (reverse : Bool) (inputSize : Nat) (lt : BoolComparator κ)
      (hasKeyfunc : Bool) (input : RunSpan)
      (forest : List SpannedMergeTree),
      ListSortScanInvariant lt hasKeyfunc inputSize state lo scanned remaining →
      remaining ≤ fuel →
      input.base = 0 →
      input.len = inputSize →
      PolicyForestMatches forest state →
      ScanPowerForestInv input forest state →
      ListSortScanStrongPost input forest fuel state lo remaining reverse
        inputSize := by
  intro fuel
  induction fuel with
  | zero =>
      intro state lo scanned remaining reverse inputSize lt hasKeyfunc input
        forest hInv hFuel hInputBase hInputLength hmatch hpowerInv
      have hRemaining : remaining = 0 := by omega
      subst remaining
      exact listSortScan_policyReplay_terminal input forest 0 state lo scanned
        reverse inputSize lt hasKeyfunc hInputLength hmatch hpowerInv hInv
  | succ fuel ih =>
      intro state lo scanned remaining reverse inputSize lt hasKeyfunc input
        forest hInv hFuel hInputBase hInputLength hmatch hpowerInv
      by_cases hRemaining : remaining = 0
      · subst remaining
        exact listSortScan_policyReplay_terminal input forest (fuel + 1) state
          lo scanned reverse inputSize lt hasKeyfunc hInputLength hmatch
          hpowerInv hInv
      · have hRemainingPositive : 0 < remaining := Nat.pos_of_ne_zero hRemaining
        have hLo : lo = scanned := by
          have hCursor := hInv.cursor
          rw [hInv.basekeys] at hCursor
          omega
        have hRemainingInput : remaining ≤ inputSize := by
          have := hInv.partition
          omega
        have hRange : SortSlice.RangeInBounds state.data (Int.ofNat lo)
            remaining := by
          constructor
          · exact Int.natCast_nonneg lo
          · rw [hInv.dataExtent]
            have hNat : lo + remaining ≤ inputSize := by
              have := hInv.partition
              omega
            simpa only [Int.ofNat_eq_natCast, Nat.cast_add] using
              (Int.ofNat_le.mpr hNat)
        have hRemainingSsize : remaining ≤ PY_SSIZE_T_MAX := by
          have hMaxLe : PY_LIST_MAX ≤ PY_SSIZE_T_MAX := by
            norm_num [PY_LIST_MAX, PY_SSIZE_T_MAX, PY_OBJECT_PTR_BYTES]
          exact hRemainingInput.trans (hInv.inputSizeMax.trans hMaxLe)
        rcases countRun_safe state state.data (Int.ofNat lo) remaining hRange
            hRemainingPositive hRemainingSsize hInv.valuesMode with
          ⟨counted, hCounted⟩
        let countedState : MergeState κ ν := { state with data := counted.slice }
        have hCountedLayout : PendingLayout countedState scanned := by
          apply pendingLayout_of_policy_frame state countedState scanned
              hInv.pendingLayout
          · rfl
          · rfl
          · exact hCounted.sizeEq
          · rfl
        have hCountedPowered : PoweredPrefix countedState := by
          exact poweredPrefix_of_policy_frame state countedState
            hInv.poweredPrefix rfl rfl rfl
        rcases hInv.adaptive hRemainingPositive with ⟨calls, hAdaptive⟩
        have hAdaptiveCounted : AdaptiveMinrunScanInvariant
            countedState.listlen calls scanned countedState.minrunState := by
          simpa [countedState, MergeState.minrunState] using hAdaptive
        have hActive : scanned < countedState.listlen.toNat := by
          simp only [countedState]
          rw [hInv.listlen]
          have := hInv.partition
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
        have hInstalledDataSize : installed.data.entries.size =
            state.data.entries.size := by
          simpa [installed, countedState, installMinrunState] using
            hCounted.sizeEq
        have hInstalledPending : installed.pending.toList =
            state.pending.toList := by
          simp [installed, countedState, installMinrunState]
        have hInstalledLayout : PendingLayout installed scanned := by
          exact pendingLayout_of_policy_frame state installed scanned
            hInv.pendingLayout hInstalledListlen hInstalledBasekeys
            hInstalledDataSize hInstalledPending
        have hInstalledPowered : PoweredPrefix installed := by
          exact poweredPrefix_of_policy_frame state installed
            hInv.poweredPrefix hInstalledListlen hInstalledBasekeys
            hInstalledPending
        have hInstalledPower : ScanPowerForestInv input forest installed := by
          exact scanPowerForestInv_of_policy_frame input forest state installed
            hpowerInv hInstalledListlen hInstalledBasekeys hInstalledPending
        have hInstalledInv : TempStorageInv installed.a installed.alloced := by
          simpa [installed, countedState, installMinrunState] using
            hInv.tempInvariant
        have hInstalledLive : installed.a.Live := by
          simpa [installed, countedState, installMinrunState] using
            hInv.tempLive
        have hInstalledPhysical :
            (MergeMemorySnapshot.ofState installed).PhysicalBound := by
          simpa [installed, countedState, installMinrunState,
            MergeMemorySnapshot.PhysicalBound, MergeMemorySnapshot.ofState]
            using hInv.physicalSlotsBound
        have hInstalledMode :
            SortSlice.ValuesModeInvariant installed.a.hasValues installed.data := by
          simpa [installed, countedState, installMinrunState] using
            hCounted.valuesMode
        have hInstalledMax : installed.listlen.toNat ≤ PY_LIST_MAX := by
          rw [hInstalledListlen, hInv.listlen]
          exact hInv.inputSizeMax
        have hInstalledBase : lo = installed.basekeys + scanned := by
          rw [hInstalledBasekeys]
          exact hInv.cursor
        have hInstalledWithin : scanned + force ≤ installed.listlen.toNat := by
          rw [hInstalledListlen, hInv.listlen]
          have := hInv.partition
          omega
        have hCountedWithin : counted.length ≤ remaining :=
          hCounted.lengthBounds.2
        have hRunWordNonnegative :
            PySSize.Nonnegative (BitVec.ofNat 64 counted.length) := by
          apply listSizeWord_nonnegative
          exact hCountedWithin.trans
            (hRemainingInput.trans hInv.inputSizeMax)
        have hTargetNonnegative : nextMinrun.result.Nonnegative := by
          apply pySSize_nonnegative_of_toNat_le_maxMinrun
          simpa [target] using hTargetMax
        have hSignedCompare := pySSize_slt_eq_nat_lt
          (BitVec.ofNat 64 counted.length : PySSize) nextMinrun.result
          hRunWordNonnegative hTargetNonnegative
        by_cases hExtend :
            (BitVec.ofNat 64 counted.length : PySSize).slt nextMinrun.result =
              true
        · have hRunLtTarget : counted.length < target := by
            rw [hSignedCompare,
              listSizeWord_toNat
                (hCountedWithin.trans
                  (hRemainingInput.trans hInv.inputSizeMax))] at hExtend
            exact of_decide_eq_true hExtend
          have hRunForce : counted.length ≤ force := by
            dsimp [force]
            split <;> omega
          have hInstalledRange : SortSlice.RangeInBounds installed.data
              (Int.ofNat lo) force := by
            constructor
            · exact Int.natCast_nonneg lo
            · have hFullRange : SortSlice.RangeInBounds installed.data
                  (Int.ofNat lo) remaining :=
                hRange.of_size_eq hInstalledDataSize
              have hEnd := hFullRange.2
              have hCast : Int.ofNat force ≤ Int.ofNat remaining :=
                Int.ofNat_le.mpr hForceRemaining
              omega
          rcases binarysort_safe installed installed.data (Int.ofNat lo) force
              counted.length hForcePositive hRunForce hForceMax
              hInstalledRange hInstalledMode with ⟨sorted, hSorted⟩
          let extended : MergeState κ ν :=
            { installed with data := sorted.slice }
          have hExtendedLayout : PendingLayout extended scanned := by
            apply pendingLayout_of_policy_frame installed extended scanned
                hInstalledLayout
            · rfl
            · rfl
            · exact hSorted.sizeEq
            · rfl
          have hExtendedPowered : PoweredPrefix extended := by
            exact poweredPrefix_of_policy_frame installed extended
              hInstalledPowered rfl rfl rfl
          have hExtendedPower : ScanPowerForestInv input forest extended := by
            exact scanPowerForestInv_of_policy_frame input forest installed
              extended hInstalledPower rfl rfl rfl
          have hExtendedInv : TempStorageInv extended.a extended.alloced := by
            simpa [extended] using hInstalledInv
          have hExtendedLive : extended.a.Live := by
            simpa [extended] using hInstalledLive
          have hExtendedPhysical :
              (MergeMemorySnapshot.ofState extended).PhysicalBound := by
            simpa [extended, MergeMemorySnapshot.PhysicalBound,
              MergeMemorySnapshot.ofState] using hInstalledPhysical
          have hExtendedMode :
              SortSlice.ValuesModeInvariant extended.a.hasValues
                extended.data := by
            simpa [extended] using hSorted.valuesMode
          have hExtendedBase : lo = extended.basekeys + scanned := by
            simpa [extended] using hInstalledBase
          have hExtendedMax : extended.listlen.toNat ≤ PY_LIST_MAX := by
            simpa [extended] using hInstalledMax
          have hExtendedWithin : scanned + force ≤
              extended.listlen.toNat := by
            simpa [extended] using hInstalledWithin
          have hAdaptiveAfter : 0 < remaining - force →
              ∃ nextCalls, AdaptiveMinrunScanInvariant extended.listlen
                nextCalls (scanned + force) extended.minrunState := by
            intro hStillActive
            refine ⟨calls + 1, ?_⟩
            have hNotClipped : ¬ remaining ≤ target := by
              intro hClipped
              have hForceEq : force = remaining := by
                simp [force, hClipped]
              rw [hForceEq] at hStillActive
              simp at hStillActive
            have hForceEq : force = target := by
              simp [force, hNotClipped]
            have hTargetConsumed : nextMinrun.result.toNat ≤ force := by
              simpa [target] using hForceEq.symm.le
            have hNextScanned : scanned + force ≤
                countedState.listlen.toNat := by
              simp only [countedState]
              rw [hInv.listlen]
              have := hInv.partition
              omega
            have hAdvanced := hAdaptiveCounted.advance (consumed := force)
              hActive hTargetConsumed hNextScanned
            have hExtendedListlen : extended.listlen = state.listlen := by
              simpa [extended] using hInstalledListlen
            have hExtendedMinrun : extended.minrunState = nextMinrun.state := by
              change installed.minrunState = nextMinrun.state
              exact (installMinrunState_frame countedState
                nextMinrun.state).1
            rw [hExtendedListlen, hExtendedMinrun]
            simpa [nextMinrun, countedState] using hAdvanced
          have hExtendedMatch : PolicyForestMatches forest extended := by
            unfold PolicyForestMatches at hmatch ⊢
            simpa [extended, installed, countedState, installMinrunState]
              using hmatch
          have hAfter := listSortAfterExtension_policyReplay input forest
            (fun nextState nextLo nextRemaining =>
              listSortScanTraced? fuel nextState nextLo nextRemaining reverse
                inputSize)
            extended lo scanned remaining force counted.length target reverse
            inputSize
            (by
              calc
                input.base = 0 := hInputBase
                _ = state.basekeys := hInv.basekeys.symm
                _ = extended.basekeys := by
                  simp [extended, hInstalledBasekeys])
            (by simpa [extended, hInstalledListlen, hInv.listlen] using
              hInputLength)
            hExtendedMatch hExtendedMax hExtendedLayout hExtendedPowered
            hExtendedPower hExtendedBase
            (by simpa [extended, hInstalledListlen, hInv.listlen] using
              hInv.partition)
            hForcePositive hExtendedWithin hForceRemaining
            hCounted.lengthBounds.1 hCounted.lengthBounds.2 hTargetPositive
            (Or.inl ⟨hRunLtTarget, by simp [force, Nat.min_def]⟩)
            hExtendedInv hExtendedLive hExtendedMode
            (by
              intro found middleForest
              dsimp only
              intro hFound hMiddleMatch hPushedPower
              let newRun : PendingRun :=
                { base := lo, len := BitVec.ofNat 64 force, power := none }
              have hNextInv := listSortScanInvariant_after_push lt hasKeyfunc
                inputSize extended lo scanned remaining force found
                hInv.inputSizeLower hInv.inputSizeMax
                (by simpa [extended, hInstalledListlen] using
                  (show installed.listlen.toNat = inputSize by
                    rw [hInstalledListlen, hInv.listlen]))
                (by simpa [extended, hInstalledListlen] using
                  hInv.listlenNonnegative)
                (by simpa [extended, hInstalledBasekeys] using hInv.basekeys)
                (by simpa [extended] using
                  (show sorted.slice.entries.size = inputSize by
                    rw [hSorted.sizeEq, hInstalledDataSize, hInv.dataExtent]))
                hExtendedBase hInv.partition hForcePositive hForceRemaining
                hExtendedPhysical
                (by simpa [extended, installed, countedState,
                    installMinrunState] using hInv.hasValues)
                (by simpa [extended, installed, countedState,
                    installMinrunState] using hInv.comparator)
                hAdaptiveAfter hFound
              have hPushedMatch : PolicyForestMatches
                  (middleForest ++
                    [SpannedMergeTree.leaf (RunSpan.ofPendingRun newRun)])
                  (pushPendingRun found.state newRun) := by
                unfold PolicyForestMatches at hMiddleMatch ⊢
                simp only [pushPendingRun, Array.toList_push,
                  List.map_append, List.map_singleton,
                  SpannedMergeTree.leaf]
                rw [hMiddleMatch]
              exact ih
                (state := pushPendingRun found.state newRun)
                (lo := lo + force) (scanned := scanned + force)
                (remaining := remaining - force) (reverse := reverse)
                (inputSize := inputSize) (lt := lt)
                (hasKeyfunc := hasKeyfunc) (input := input)
                (forest := middleForest ++
                  [SpannedMergeTree.leaf (RunSpan.ofPendingRun newRun)])
                hNextInv (by omega) hInputBase hInputLength
                (by simpa [newRun] using hPushedMatch)
                (by simpa [newRun] using hPushedPower))
          have hCountedValid :
              ¬(counted.length = 0 ∨ remaining < counted.length) := by
            rintro (hzero | htooLong)
            · have hpositive := hCounted.lengthBounds.1
              rw [hzero] at hpositive
              omega
            · exact (Nat.not_lt_of_ge hCounted.lengthBounds.2) htooLong
          apply hAfter.of_policyEvents_eq_and_reached
          · have hCountNil := countRunTraced_policyEvents_eq_nil state
              state.data (Int.ofNat lo) remaining
            have hBinaryNil := binarysortTraced_policyEvents_eq_nil installed
              installed.data (Int.ofNat lo) force counted.length
            symm
            rw [listSortScanTraced?, if_neg hRemaining,
              TraceResult.policyEvents_bind, hCounted.resultEq]
            change
              (countRunTraced? state state.data (Int.ofNat lo)
                  remaining).trace.policyEvents ++
                (listSortAfterCountTraced?
                  (fun nextState nextLo nextRemaining =>
                    listSortScanTraced? fuel nextState nextLo nextRemaining
                      reverse inputSize)
                  state lo remaining reverse inputSize counted).trace.policyEvents =
                _
            rw [hCountNil, List.nil_append]
            change
              (listSortAfterCountTraced?
                (fun nextState nextLo nextRemaining =>
                  listSortScanTraced? fuel nextState nextLo nextRemaining
                    reverse inputSize)
                state lo remaining reverse inputSize counted).trace.policyEvents =
              (listSortAfterExtensionTraced?
                (fun nextState nextLo nextRemaining =>
                  listSortScanTraced? fuel nextState nextLo nextRemaining
                    reverse inputSize)
                lo remaining reverse inputSize counted.length target
                (extended, force, false)).trace.policyEvents
            simp only [listSortAfterCountTraced?, hCounted.resultFuel,
              Bool.false_eq_true, if_false]
            rw [if_neg hCountedValid]
            simp only [countedState, nextMinrun, installed, target, force,
              hExtend, if_true, TraceResult.policyEvents_bind,
              hSorted.resultEq, hBinaryNil, List.nil_append, extended,
              hSorted.resultFuel]
          · intro openState collapsed hReached
            have hBinaryReached := ListSortScanReachedCollapse.through_bind
              (binarysortTraced? installed installed.data (Int.ofNat lo)
                force counted.length)
              (fun nextSorted =>
                listSortAfterExtensionTraced?
                  (fun nextState nextLo nextRemaining =>
                    listSortScanTraced? fuel nextState nextLo nextRemaining
                      reverse inputSize)
                  lo remaining reverse inputSize counted.length target
                  ({ installed with data := nextSorted.slice }, force,
                    nextSorted.fuelExhausted))
              sorted hSorted.resultEq (by
                simpa [extended, hSorted.resultFuel] using hReached)
            have hAfterCountReached :
                ListSortScanReachedCollapse reverse inputSize openState
                  collapsed
                  (listSortAfterCountTraced?
                    (fun nextState nextLo nextRemaining =>
                      listSortScanTraced? fuel nextState nextLo nextRemaining
                        reverse inputSize)
                    state lo remaining reverse inputSize counted) := by
              simpa only [listSortAfterCountTraced?, hCounted.resultFuel,
                Bool.false_eq_true, if_false, if_neg hCountedValid,
                countedState, nextMinrun, installed, target, force, hExtend,
                if_true] using hBinaryReached
            have hCountReached := ListSortScanReachedCollapse.through_bind
              (countRunTraced? state state.data (Int.ofNat lo) remaining)
              (fun nextCounted =>
                listSortAfterCountTraced?
                  (fun nextState nextLo nextRemaining =>
                    listSortScanTraced? fuel nextState nextLo nextRemaining
                      reverse inputSize)
                  state lo remaining reverse inputSize nextCounted)
              counted hCounted.resultEq hAfterCountReached
            simpa [listSortScanTraced?, hRemaining] using hCountReached
        · have hRunNotLtTarget : ¬ counted.length < target := by
            intro hlt
            apply hExtend
            rw [hSignedCompare,
              listSizeWord_toNat
                (hCountedWithin.trans
                  (hRemainingInput.trans hInv.inputSizeMax))]
            exact decide_eq_true hlt
          have hTargetRun : target ≤ counted.length := by omega
          have hInstalledRunWithin : scanned + counted.length ≤
              installed.listlen.toNat := by
            rw [hInstalledListlen, hInv.listlen]
            have := hInv.partition
            omega
          have hAdaptiveAfter : 0 < remaining - counted.length →
              ∃ nextCalls, AdaptiveMinrunScanInvariant installed.listlen
                nextCalls (scanned + counted.length)
                  installed.minrunState := by
            intro _hStillActive
            refine ⟨calls + 1, ?_⟩
            have hNextScanned : scanned + counted.length ≤
                countedState.listlen.toNat := by
              simp only [countedState]
              rw [hInv.listlen]
              have := hInv.partition
              omega
            have hAdvanced := hAdaptiveCounted.advance hActive hTargetRun
              hNextScanned
            have hInstalledMinrun :
                installed.minrunState = nextMinrun.state :=
              (installMinrunState_frame countedState nextMinrun.state).1
            rw [hInstalledListlen, hInstalledMinrun]
            simpa [nextMinrun, countedState] using hAdvanced
          have hInstalledMatch : PolicyForestMatches forest installed := by
            unfold PolicyForestMatches at hmatch ⊢
            simpa [installed, countedState, installMinrunState] using hmatch
          have hAfter := listSortAfterExtension_policyReplay input forest
            (fun nextState nextLo nextRemaining =>
              listSortScanTraced? fuel nextState nextLo nextRemaining reverse
                inputSize)
            installed lo scanned remaining counted.length counted.length target
            reverse inputSize
            (by
              calc
                input.base = 0 := hInputBase
                _ = state.basekeys := hInv.basekeys.symm
                _ = installed.basekeys := hInstalledBasekeys.symm)
            (by
              rw [hInstalledListlen, hInv.listlen]
              exact hInputLength)
            hInstalledMatch hInstalledMax hInstalledLayout hInstalledPowered
            hInstalledPower hInstalledBase
            (by rw [hInstalledListlen, hInv.listlen]
                exact hInv.partition)
            hCounted.lengthBounds.1 hInstalledRunWithin
            hCounted.lengthBounds.2 hCounted.lengthBounds.1
            hCounted.lengthBounds.2 hTargetPositive
            (Or.inr ⟨hTargetRun, rfl⟩)
            hInstalledInv hInstalledLive hInstalledMode
            (by
              intro found middleForest
              dsimp only
              intro hFound hMiddleMatch hPushedPower
              let newRun : PendingRun :=
                { base := lo
                  len := BitVec.ofNat 64 counted.length
                  power := none }
              have hNextInv := listSortScanInvariant_after_push lt hasKeyfunc
                inputSize installed lo scanned remaining counted.length found
                hInv.inputSizeLower hInv.inputSizeMax
                (by rw [hInstalledListlen, hInv.listlen])
                (by rw [hInstalledListlen]
                    exact hInv.listlenNonnegative)
                (by rw [hInstalledBasekeys]
                    exact hInv.basekeys)
                (by rw [hInstalledDataSize, hInv.dataExtent])
                hInstalledBase hInv.partition hCounted.lengthBounds.1
                hCounted.lengthBounds.2 hInstalledPhysical
                (by simpa [installed, countedState, installMinrunState]
                  using hInv.hasValues)
                (by simpa [installed, countedState, installMinrunState]
                  using hInv.comparator)
                hAdaptiveAfter hFound
              have hPushedMatch : PolicyForestMatches
                  (middleForest ++
                    [SpannedMergeTree.leaf (RunSpan.ofPendingRun newRun)])
                  (pushPendingRun found.state newRun) := by
                unfold PolicyForestMatches at hMiddleMatch ⊢
                simp only [pushPendingRun, Array.toList_push,
                  List.map_append, List.map_singleton,
                  SpannedMergeTree.leaf]
                rw [hMiddleMatch]
              exact ih
                (state := pushPendingRun found.state newRun)
                (lo := lo + counted.length)
                (scanned := scanned + counted.length)
                (remaining := remaining - counted.length)
                (reverse := reverse) (inputSize := inputSize) (lt := lt)
                (hasKeyfunc := hasKeyfunc) (input := input)
                (forest := middleForest ++
                  [SpannedMergeTree.leaf (RunSpan.ofPendingRun newRun)])
                hNextInv (by omega) hInputBase hInputLength
                (by simpa [newRun] using hPushedMatch)
                (by simpa [newRun] using hPushedPower))
          have hCountedValid :
              ¬(counted.length = 0 ∨ remaining < counted.length) := by
            rintro (hzero | htooLong)
            · have hpositive := hCounted.lengthBounds.1
              rw [hzero] at hpositive
              omega
            · exact (Nat.not_lt_of_ge hCounted.lengthBounds.2) htooLong
          apply hAfter.of_policyEvents_eq_and_reached
          · have hCountNil := countRunTraced_policyEvents_eq_nil state
              state.data (Int.ofNat lo) remaining
            symm
            rw [listSortScanTraced?, if_neg hRemaining,
              TraceResult.policyEvents_bind, hCounted.resultEq]
            change
              (countRunTraced? state state.data (Int.ofNat lo)
                  remaining).trace.policyEvents ++
                (listSortAfterCountTraced?
                  (fun nextState nextLo nextRemaining =>
                    listSortScanTraced? fuel nextState nextLo nextRemaining
                      reverse inputSize)
                  state lo remaining reverse inputSize counted).trace.policyEvents =
                _
            rw [hCountNil, List.nil_append]
            change
              (listSortAfterCountTraced?
                (fun nextState nextLo nextRemaining =>
                  listSortScanTraced? fuel nextState nextLo nextRemaining
                    reverse inputSize)
                state lo remaining reverse inputSize counted).trace.policyEvents =
              (listSortAfterExtensionTraced?
                (fun nextState nextLo nextRemaining =>
                  listSortScanTraced? fuel nextState nextLo nextRemaining
                    reverse inputSize)
                lo remaining reverse inputSize counted.length target
                (installed, counted.length, false)).trace.policyEvents
            simp only [listSortAfterCountTraced?, hCounted.resultFuel,
              Bool.false_eq_true, if_false]
            rw [if_neg hCountedValid]
            simp only [countedState, nextMinrun, installed, target,
              hExtend, Bool.false_eq_true, if_false]
          · intro openState collapsed hReached
            have hAfterCountReached :
                ListSortScanReachedCollapse reverse inputSize openState
                  collapsed
                  (listSortAfterCountTraced?
                    (fun nextState nextLo nextRemaining =>
                      listSortScanTraced? fuel nextState nextLo nextRemaining
                        reverse inputSize)
                    state lo remaining reverse inputSize counted) := by
              simpa only [listSortAfterCountTraced?, hCounted.resultFuel,
                Bool.false_eq_true, if_false, if_neg hCountedValid,
                countedState, nextMinrun, installed, target, hExtend] using
                hReached
            have hCountReached := ListSortScanReachedCollapse.through_bind
              (countRunTraced? state state.data (Int.ofNat lo) remaining)
              (fun nextCounted =>
                listSortAfterCountTraced?
                  (fun nextState nextLo nextRemaining =>
                    listSortScanTraced? fuel nextState nextLo nextRemaining
                      reverse inputSize)
                  state lo remaining reverse inputSize nextCounted)
              counted hCounted.resultEq hAfterCountReached
            simpa [listSortScanTraced?, hRemaining] using hCountReached

end CPythonListsort
