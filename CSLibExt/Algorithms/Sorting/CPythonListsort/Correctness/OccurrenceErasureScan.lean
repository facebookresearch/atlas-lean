/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Code.Correctness.OccurrenceErasureMerges

/-!
# Occurrence erasure through merge policy and the top-level scan

This module continues structural occurrence erasure through `merge_at`, the
PowerSort policy, final collapse, cleanup, and the complete listsort evaluator.
-/

namespace CPythonListsort

universe u v

variable {alpha : Type u} {nu : Type v}

def eraseOccurrenceMergeAtResult
    (result : MergeAtResult (Occurrence alpha) nu) : MergeAtResult alpha nu :=
  { result with state := eraseOccurrenceMergeState result.state }

def eraseOccurrenceMergeAtCall
    (call : MergeAtCall (Occurrence alpha) nu) : MergeAtCall alpha nu :=
  { call with
    state := eraseOccurrenceMergeState call.state
    firstB := eraseOccurrenceEntry call.firstB
    lastA := eraseOccurrenceEntry call.lastA }

def eraseOccurrenceMergeAtPreparation :
    MergeAtPreparation (Occurrence alpha) nu → MergeAtPreparation alpha nu
  | .finished result => .finished (eraseOccurrenceMergeAtResult result)
  | .mergeLo call => .mergeLo (eraseOccurrenceMergeAtCall call)
  | .mergeHi call => .mergeHi (eraseOccurrenceMergeAtCall call)

def eraseOccurrenceFoundNewRunResult
    (result : FoundNewRunResult (Occurrence alpha) nu) :
    FoundNewRunResult alpha nu :=
  { result with state := eraseOccurrenceMergeState result.state }

def eraseOccurrenceMergeForceCollapseResult
    (result : MergeForceCollapseResult (Occurrence alpha) nu) :
    MergeForceCollapseResult alpha nu :=
  { result with state := eraseOccurrenceMergeState result.state }

@[simp] theorem eraseOccurrenceMergeAtResult_state
    (result : MergeAtResult (Occurrence alpha) nu) :
    (eraseOccurrenceMergeAtResult result).state =
      eraseOccurrenceMergeState result.state := rfl

@[simp] theorem eraseOccurrenceMergeAtResult_returnCode
    (result : MergeAtResult (Occurrence alpha) nu) :
    (eraseOccurrenceMergeAtResult result).returnCode = result.returnCode := rfl

@[simp] theorem eraseOccurrenceMergeAtResult_fuelExhausted
    (result : MergeAtResult (Occurrence alpha) nu) :
    (eraseOccurrenceMergeAtResult result).fuelExhausted =
      result.fuelExhausted := rfl

@[simp] theorem eraseOccurrenceMergeAtCall_state
    (call : MergeAtCall (Occurrence alpha) nu) :
    (eraseOccurrenceMergeAtCall call).state =
      eraseOccurrenceMergeState call.state := rfl

@[simp] theorem eraseOccurrenceMergeAtCall_firstB
    (call : MergeAtCall (Occurrence alpha) nu) :
    (eraseOccurrenceMergeAtCall call).firstB =
      eraseOccurrenceEntry call.firstB := rfl

@[simp] theorem eraseOccurrenceMergeAtCall_lastA
    (call : MergeAtCall (Occurrence alpha) nu) :
    (eraseOccurrenceMergeAtCall call).lastA =
      eraseOccurrenceEntry call.lastA := rfl

@[simp] theorem eraseOccurrenceMergeAtCall_ssa
    (call : MergeAtCall (Occurrence alpha) nu) :
    (eraseOccurrenceMergeAtCall call).ssa = call.ssa := rfl

@[simp] theorem eraseOccurrenceMergeAtCall_ssb
    (call : MergeAtCall (Occurrence alpha) nu) :
    (eraseOccurrenceMergeAtCall call).ssb = call.ssb := rfl

@[simp] theorem eraseOccurrenceMergeAtCall_na
    (call : MergeAtCall (Occurrence alpha) nu) :
    (eraseOccurrenceMergeAtCall call).na = call.na := rfl

@[simp] theorem eraseOccurrenceMergeAtCall_nb
    (call : MergeAtCall (Occurrence alpha) nu) :
    (eraseOccurrenceMergeAtCall call).nb = call.nb := rfl

@[simp] theorem eraseOccurrenceMergeAtPreparation_state
    (preparation : MergeAtPreparation (Occurrence alpha) nu) :
    (eraseOccurrenceMergeAtPreparation preparation).state =
      eraseOccurrenceMergeState preparation.state := by
  cases preparation <;> rfl

@[simp] theorem eraseOccurrenceFoundNewRunResult_state
    (result : FoundNewRunResult (Occurrence alpha) nu) :
    (eraseOccurrenceFoundNewRunResult result).state =
      eraseOccurrenceMergeState result.state := rfl

@[simp] theorem eraseOccurrenceFoundNewRunResult_returnCode
    (result : FoundNewRunResult (Occurrence alpha) nu) :
    (eraseOccurrenceFoundNewRunResult result).returnCode =
      result.returnCode := rfl

@[simp] theorem eraseOccurrenceFoundNewRunResult_fuelExhausted
    (result : FoundNewRunResult (Occurrence alpha) nu) :
    (eraseOccurrenceFoundNewRunResult result).fuelExhausted =
      result.fuelExhausted := rfl

@[simp] theorem eraseOccurrenceMergeForceCollapseResult_state
    (result : MergeForceCollapseResult (Occurrence alpha) nu) :
    (eraseOccurrenceMergeForceCollapseResult result).state =
      eraseOccurrenceMergeState result.state := rfl

@[simp] theorem eraseOccurrenceMergeForceCollapseResult_returnCode
    (result : MergeForceCollapseResult (Occurrence alpha) nu) :
    (eraseOccurrenceMergeForceCollapseResult result).returnCode =
      result.returnCode := rfl

@[simp] theorem eraseOccurrenceMergeForceCollapseResult_fuelExhausted
    (result : MergeForceCollapseResult (Occurrence alpha) nu) :
    (eraseOccurrenceMergeForceCollapseResult result).fuelExhausted =
      result.fuelExhausted := rfl

@[simp]
theorem eraseOccurrenceSetTopPower (power : Nat)
    (state : MergeState (Occurrence alpha) nu) :
    setTopPower? (eraseOccurrenceMergeState state) power =
      (setTopPower? state power).map eraseOccurrenceMergeState := by
  simp only [eraseOccurrenceMergeState]
  unfold setTopPower?
  by_cases hempty : state.pending.isEmpty
  · simp [hempty]
  · rw [if_neg hempty, if_neg hempty]
    cases htop : state.pending[state.pending.size - 1]? with
    | none => simp [htop]
    | some top => simp [htop, eraseOccurrenceMergeState]

@[simp]
theorem eraseOccurrenceForceCollapseIndex
    (state : MergeState (Occurrence alpha) nu) :
    forceCollapseIndex? (eraseOccurrenceMergeState state) =
      forceCollapseIndex? state := by
  simp [forceCollapseIndex?, eraseOccurrenceMergeState]

theorem eraseOccurrencePrepareMergeAt
    (lt : BoolComparator alpha)
    (state : MergeState (Occurrence alpha) nu) (i : Nat)
    (hcompare : state.key_compare = occurrenceComparator lt) :
    prepareMergeAt? (eraseOccurrenceMergeState state) i =
      (prepareMergeAt? state i).map eraseOccurrenceMergeAtPreparation := by
  simp only [eraseOccurrenceMergeState]
  unfold prepareMergeAt?
  by_cases hposition :
      2 ≤ state.pending.size ∧
        (i + 2 = state.pending.size ∨ i + 3 = state.pending.size)
  · rw [if_pos hposition, if_pos hposition]
    cases hleft : state.pending[i]? with
    | none => simp
    | some left =>
        simp only [mergeAt_bindOptionAcross_some]
        cases hright : state.pending[i + 1]? with
        | none => simp
        | some right =>
            simp only [mergeAt_bindOptionAcross_some]
            by_cases hgeometry :
                (0 : PySSize).slt left.len ∧
                  (0 : PySSize).slt right.len ∧
                  left.base + left.len.toNat = right.base
            · rw [if_pos hgeometry, if_pos hgeometry]
              simp only [combinePendingAt_eq]
              let call : MergeState (Occurrence alpha) nu :=
                { state with
                  pending :=
                    (state.pending.setIfInBounds i
                      { left with len := left.len + right.len }).eraseIdxIfInBounds
                        (i + 1) }
              have heraseCall :
                  { eraseOccurrenceMergeState state with
                    pending :=
                      (state.pending.setIfInBounds i
                        { left with len := left.len + right.len }).eraseIdxIfInBounds
                          (i + 1) } = eraseOccurrenceMergeState call := rfl
              have heraseCall' := heraseCall
              simp only [eraseOccurrenceMergeState] at heraseCall'
              rw [heraseCall']
              have hcallCompare :
                  call.key_compare = occurrenceComparator lt := hcompare
              have hcallData : call.data = state.data := rfl
              rw [← hcallData]
              rw [eraseOccurrenceSlice_read]
              cases hfirst : call.data.read? (Int.ofNat right.base) with
              | none => simp
              | some firstB =>
                  simp only [Option.map_some]
                  have hgallopRight :
                      gallopRight? (eraseOccurrenceMergeState call)
                          (eraseOccurrenceSlice call.data)
                          (Int.ofNat left.base) firstB.key.value
                          left.len.toNat 0 =
                        gallopRight? call call.data (Int.ofNat left.base)
                          firstB.key left.len.toNat 0 := by
                    simpa [call] using
                      (eraseOccurrenceGallopRight lt call call.data
                        (Int.ofNat left.base) firstB.key left.len.toNat 0
                        hcallCompare)
                  simp only [eraseOccurrenceEntry_key]
                  simp only [eraseOccurrenceMergeState] at hgallopRight
                  rw [hgallopRight]
                  cases htrimA : gallopRight? call call.data
                      (Int.ofNat left.base) firstB.key left.len.toNat 0 with
                  | none => simp
                  | some trimA =>
                      simp only [mergeAt_bindOptionAcross_some]
                      by_cases htrimAFuel : trimA.fuelExhausted
                      · simp [htrimAFuel, eraseOccurrenceMergeAtPreparation,
                          eraseOccurrenceMergeAtResult,
                          eraseOccurrenceMergeState, call]
                      · rw [if_neg htrimAFuel, if_neg htrimAFuel]
                        by_cases htrimABounds : left.len.toNat < trimA.index
                        · simp [htrimABounds]
                        · rw [if_neg htrimABounds, if_neg htrimABounds]
                          by_cases hemptyA : left.len.toNat - trimA.index = 0
                          · simp [hemptyA,
                              eraseOccurrenceMergeAtPreparation,
                              eraseOccurrenceMergeAtResult,
                              eraseOccurrenceMergeState, call]
                          · rw [if_neg hemptyA, if_neg hemptyA]
                            rw [eraseOccurrenceSlice_read]
                            cases hlast : call.data.read?
                                (Int.ofNat
                                  (left.base + trimA.index +
                                    (left.len.toNat - trimA.index) - 1)) with
                            | none => simp
                            | some lastA =>
                                simp only [Option.map_some]
                                have hgallopLeft :
                                    gallopLeft?
                                        (eraseOccurrenceMergeState call)
                                        (eraseOccurrenceSlice call.data)
                                        (Int.ofNat right.base) lastA.key.value
                                        right.len.toNat
                                        (right.len.toNat - 1) =
                                      gallopLeft? call call.data
                                        (Int.ofNat right.base) lastA.key
                                        right.len.toNat
                                        (right.len.toNat - 1) := by
                                  simpa [call] using
                                    (eraseOccurrenceGallopLeft lt call call.data
                                      (Int.ofNat right.base) lastA.key
                                      right.len.toNat (right.len.toNat - 1)
                                      hcallCompare)
                                simp only [eraseOccurrenceEntry_key]
                                simp only [eraseOccurrenceMergeState] at hgallopLeft
                                rw [hgallopLeft]
                                cases htrimB : gallopLeft? call call.data
                                    (Int.ofNat right.base) lastA.key
                                    right.len.toNat (right.len.toNat - 1) with
                                | none => simp
                                | some trimB =>
                                    simp only [mergeAt_bindOptionAcross_some]
                                    by_cases htrimBFuel : trimB.fuelExhausted
                                    · simp [htrimBFuel,
                                        eraseOccurrenceMergeAtPreparation,
                                        eraseOccurrenceMergeAtResult,
                                        eraseOccurrenceMergeState, call]
                                    · rw [if_neg htrimBFuel,
                                        if_neg htrimBFuel]
                                      by_cases htrimBBounds :
                                          right.len.toNat < trimB.index
                                      · simp [htrimBBounds]
                                      · rw [if_neg htrimBBounds,
                                          if_neg htrimBBounds]
                                        by_cases hemptyB : trimB.index = 0
                                        · simp [hemptyB,
                                            eraseOccurrenceMergeAtPreparation,
                                            eraseOccurrenceMergeAtResult,
                                            eraseOccurrenceMergeState, call]
                                        · rw [if_neg hemptyB, if_neg hemptyB]
                                          by_cases hlo :
                                              left.len.toNat - trimA.index ≤
                                                trimB.index
                                          · simp [hlo,
                                              eraseOccurrenceMergeAtPreparation,
                                              eraseOccurrenceMergeAtCall,
                                              eraseOccurrenceMergeState, call]
                                          · simp [hlo,
                                              eraseOccurrenceMergeAtPreparation,
                                              eraseOccurrenceMergeAtCall,
                                              eraseOccurrenceMergeState, call]
            · rw [if_neg hgeometry, if_neg hgeometry]
              rfl
  · simp [hposition]

theorem eraseOccurrenceFinishMergeAtPreparation
    (lt : BoolComparator alpha)
    (preparation : MergeAtPreparation (Occurrence alpha) nu)
    (hcompare : preparation.state.key_compare = occurrenceComparator lt) :
    finishMergeAtPreparation?
        (eraseOccurrenceMergeAtPreparation preparation) =
      (finishMergeAtPreparation? preparation).map
        eraseOccurrenceMergeAtResult := by
  cases preparation with
  | finished result => rfl
  | mergeLo call =>
      simp only [eraseOccurrenceMergeAtPreparation,
        finishMergeAtPreparation?, eraseOccurrenceMergeAtCall_state,
        eraseOccurrenceMergeAtCall_ssa, eraseOccurrenceMergeAtCall_ssb,
        eraseOccurrenceMergeAtCall_na, eraseOccurrenceMergeAtCall_nb]
      rw [eraseOccurrenceMergeLo lt call.state call.ssa call.ssb call.na
        call.nb hcompare]
      cases hmerge : mergeLo? call.state call.ssa call.ssb call.na call.nb with
      | none => rfl
      | some result =>
          simp [eraseOccurrenceMergeAtResult,
            eraseOccurrenceMergeLoResult]
  | mergeHi call =>
      simp only [eraseOccurrenceMergeAtPreparation,
        finishMergeAtPreparation?, eraseOccurrenceMergeAtCall_state,
        eraseOccurrenceMergeAtCall_ssa, eraseOccurrenceMergeAtCall_ssb,
        eraseOccurrenceMergeAtCall_na, eraseOccurrenceMergeAtCall_nb]
      rw [eraseOccurrenceMergeHi lt call.state call.ssa call.ssb call.na
        call.nb hcompare]
      cases hmerge : mergeHi? call.state call.ssa call.ssb call.na call.nb with
      | none => rfl
      | some result =>
          simp [eraseOccurrenceMergeAtResult,
            eraseOccurrenceMergeHiResult]

@[simp]
theorem eraseOccurrenceMergeAt
    (lt : BoolComparator alpha)
    (state : MergeState (Occurrence alpha) nu) (i : Nat)
    (hcompare : state.key_compare = occurrenceComparator lt) :
    mergeAt? (eraseOccurrenceMergeState state) i =
      (mergeAt? state i).map eraseOccurrenceMergeAtResult := by
  unfold mergeAt?
  rw [eraseOccurrencePrepareMergeAt lt state i hcompare]
  cases hprepare : prepareMergeAt? state i with
  | none => rfl
  | some preparation =>
      simp only [Option.map_some, mergeAt_bindOptionAcross_some]
      apply eraseOccurrenceFinishMergeAtPreparation lt preparation
      rw [prepareMergeAt?_key_compare_of_eq_some state i preparation hprepare]
      exact hcompare

@[simp]
theorem eraseOccurrenceInitialMergeState
    (lt : BoolComparator alpha) (hasKeyfunc : Bool)
    (input : SortSlice alpha nu) :
    eraseOccurrenceMergeState
        (initialMergeState (occurrenceComparator lt) hasKeyfunc
          (tagSortSliceOccurrences input)).1 =
      (initialMergeState lt hasKeyfunc input).1 := by
  simp [initialMergeState, eraseOccurrenceMergeState,
    eraseOccurrenceTempStorage, mergeInitTemp]

@[simp]
theorem initialMergeState_occurrence_stopped
    (lt : BoolComparator alpha) (hasKeyfunc : Bool)
    (input : SortSlice alpha nu) :
    (initialMergeState (occurrenceComparator lt) hasKeyfunc
        (tagSortSliceOccurrences input)).2 =
      (initialMergeState lt hasKeyfunc input).2 := by
  simp [initialMergeState, tagSortSliceOccurrences]

@[simp]
theorem eraseOccurrenceFinishListSort
    (state : MergeState (Occurrence alpha) nu) (reverse : Bool)
    (inputSize : Nat) (returnCode : Int) (fuelExhausted : Bool) :
    finishListSort? (eraseOccurrenceMergeState state) reverse inputSize
        returnCode fuelExhausted =
      (finishListSort? state reverse inputSize returnCode fuelExhausted).map
        eraseOccurrenceListSortImplResult := by
  unfold finishListSort?
  by_cases hreverse : reverse && decide (1 < inputSize)
  · rw [if_pos hreverse, if_pos hreverse]
    simp only [eraseOccurrenceMergeState_data]
    rw [eraseOccurrenceSortsliceReverse]
    cases hreversed : sortsliceReverse? state.data 0 inputSize with
    | none => simp
    | some reversed =>
        simp only [Option.map_some, bind, Option.bind,
          eraseOccurrenceReverseSliceResult]
        rw [eraseOccurrenceMergeState_setData, eraseOccurrenceMergeFreemem]
        rfl
  · rw [if_neg hreverse, if_neg hreverse]
    simp only [bind, Option.bind]
    rw [eraseOccurrenceMergeFreemem]
    rfl

@[simp]
theorem eraseOccurrenceFailFromFoundNewRun
    (result : FoundNewRunResult (Occurrence alpha) nu) (reverse : Bool)
    (inputSize : Nat) :
    failFromFoundNewRun? (eraseOccurrenceFoundNewRunResult result) reverse
        inputSize =
      (failFromFoundNewRun? result reverse inputSize).map
        eraseOccurrenceListSortImplResult := by
  simp [failFromFoundNewRun?]

@[simp]
theorem eraseOccurrenceFailFromCollapse
    (result : MergeForceCollapseResult (Occurrence alpha) nu) (reverse : Bool)
    (inputSize : Nat) :
    failFromCollapse? (eraseOccurrenceMergeForceCollapseResult result) reverse
        inputSize =
      (failFromCollapse? result reverse inputSize).map
        eraseOccurrenceListSortImplResult := by
  simp [failFromCollapse?]

private def listSortScanAfterExtension? {kappa : Type u} (fuel : Nat)
    (state : MergeState kappa nu) (lo remaining : Nat)
    (reverse : Bool) (inputSize runLength : Nat) (extensionFuel : Bool) :
    Option (ListSortImplResult kappa nu) :=
  let runLength := runLength
  let extensionFuel := extensionFuel
  if extensionFuel then
    finishListSort? state reverse inputSize (-1) true
  else if runLength = 0 ∨ remaining < runLength then
    none
  else
    match foundNewRun? state runLength with
    | none => none
    | some found =>
        if found.returnCode = 0 ∧ !found.fuelExhausted then
          let newRun : PendingRun :=
            { base := lo
              len := BitVec.ofNat 64 runLength
              power := none }
          let state := pushPendingRun found.state newRun
          listSortScan? fuel state (lo + runLength) (remaining - runLength)
            reverse inputSize
        else
          failFromFoundNewRun? found reverse inputSize

private def listSortScanAfterCount? {kappa : Type u} (fuel : Nat)
    (state : MergeState kappa nu) (lo remaining : Nat)
    (reverse : Bool) (inputSize : Nat)
    (counted : CountRunResult kappa nu) :
    Option (ListSortImplResult kappa nu) :=
  let state := { state with data := counted.slice }
  if counted.fuelExhausted then
    finishListSort? state reverse inputSize (-1) true
  else if counted.length = 0 ∨ remaining < counted.length then
    none
  else do
    let nextMinrun := minrunNext state.minrunState
    let state := installMinrunState state nextMinrun.state
    let runLength := counted.length
    let target := nextMinrun.result.toNat
    let force := if remaining ≤ target then remaining else target
    let extended ←
      if (BitVec.ofNat 64 runLength : PySSize).slt nextMinrun.result then
        match binarysort? state state.data (Int.ofNat lo) force runLength with
        | none => none
        | some sorted => some (sorted.slice, force, sorted.fuelExhausted)
      else
        some (state.data, runLength, false)
    let state := { state with data := extended.1 }
    listSortScanAfterExtension? fuel state lo remaining reverse inputSize
      extended.2.1 extended.2.2

private theorem listSortScan_succ_of_remaining_ne_zero {kappa : Type u}
    (fuel : Nat) (state : MergeState kappa nu)
    (lo remaining : Nat) (reverse : Bool) (inputSize : Nat)
    (hremaining : remaining ≠ 0) :
    listSortScan? (fuel + 1) state lo remaining reverse inputSize = (do
      let counted ← countRun? state state.data (Int.ofNat lo) remaining
      listSortScanAfterCount? fuel state lo remaining reverse inputSize
        counted) := by
  unfold listSortScan?
  rw [if_neg hremaining]
  unfold listSortScanAfterCount? listSortScanAfterExtension?
  apply Option.bind_congr
  intro counted _
  by_cases hcountFuel : counted.fuelExhausted
  · simp [hcountFuel]
  · simp only [hcountFuel]
    by_cases hcountBad : counted.length = 0 ∨ remaining < counted.length
    · simp [hcountBad]
    · simp only [hcountBad, if_false]
      let countedState : MergeState kappa nu :=
        { state with data := counted.slice }
      let nextMinrun := minrunNext countedState.minrunState
      let nextState := installMinrunState countedState nextMinrun.state
      let runLength := counted.length
      let target := nextMinrun.result.toNat
      by_cases hextend :
          (BitVec.ofNat 64 runLength : PySSize).slt nextMinrun.result
      · have hextendBase :
            (BitVec.ofNat 64 counted.length : PySSize).slt
              (minrunNext
                ({ state with data := counted.slice } :
                  MergeState kappa nu).minrunState).result := by
            simpa only [runLength, nextMinrun, countedState] using hextend
        simp only [hextendBase, if_true]
        by_cases hforce : remaining ≤ target
        · have hforceBase :
              remaining ≤
                (minrunNext
                  ({ state with data := counted.slice } :
                    MergeState kappa nu).minrunState).result.toNat := by
              simpa only [target, nextMinrun, countedState] using hforce
          simp only [hforceBase, if_true]
          cases hsorted : binarysort? nextState nextState.data (Int.ofNat lo)
              remaining runLength with
          | none => simp
          | some sorted =>
              simp [hremaining]
              split <;> simp_all
              split <;> simp_all
        · have hforceBase :
              ¬ remaining ≤
                (minrunNext
                  ({ state with data := counted.slice } :
                    MergeState kappa nu).minrunState).result.toNat := by
              simpa only [target, nextMinrun, countedState] using hforce
          simp only [hforceBase, if_false]
          cases hsorted : binarysort? nextState nextState.data (Int.ofNat lo)
              target runLength with
          | none => simp
          | some sorted =>
              simp
              split <;> simp_all
              split <;> simp_all
              split <;> simp_all
      · have hextendBase :
            ¬ (BitVec.ofNat 64 counted.length : PySSize).slt
              (minrunNext
                ({ state with data := counted.slice } :
                  MergeState kappa nu).minrunState).result := by
            simpa only [runLength, nextMinrun, countedState] using hextend
        simp [hextendBase, hcountBad]
        split <;> simp_all

private theorem eraseOccurrenceFoundNewRunLoop_of_mergeAt
    (lt : BoolComparator alpha) (fuel : Nat)
    (state : MergeState (Occurrence alpha) nu) (power : Nat)
    (hcompare : state.key_compare = occurrenceComparator lt)
    (hmergeAt : ∀ (next : MergeState (Occurrence alpha) nu) (i : Nat),
      next.key_compare = occurrenceComparator lt →
        mergeAt? (eraseOccurrenceMergeState next) i =
          (mergeAt? next i).map eraseOccurrenceMergeAtResult) :
    foundNewRunLoop? fuel (eraseOccurrenceMergeState state) power =
      (foundNewRunLoop? fuel state power).map
        eraseOccurrenceFoundNewRunResult := by
  induction fuel generalizing state with
  | zero =>
      simp [foundNewRunLoop?, foundNewRunOutOfFuel_eq,
        eraseOccurrenceFoundNewRunResult, eraseOccurrenceMergeState]
  | succ fuel ih =>
      simp only [eraseOccurrenceMergeState]
      simp only [foundNewRunLoop?]
      by_cases hdepth : 1 < state.pending.size
      · rw [if_pos hdepth, if_pos hdepth]
        cases hpreceding : state.pending[state.pending.size - 2]? with
        | none => simp
        | some preceding =>
            simp only
            cases hpower : preceding.power with
            | none => simp
            | some precedingPower =>
                simp only
                by_cases hcollapse : power < precedingPower
                · rw [if_pos hcollapse, if_pos hcollapse]
                  have heraseMerge := hmergeAt state
                    (state.pending.size - 2) hcompare
                  simp only [eraseOccurrenceMergeState] at heraseMerge
                  rw [heraseMerge]
                  cases hmerge : mergeAt? state
                      (state.pending.size - 2) with
                  | none => simp
                  | some merged =>
                      simp only [Option.map_some,
                        eraseOccurrenceMergeAtResult_returnCode,
                        eraseOccurrenceMergeAtResult_fuelExhausted]
                      simp only [eraseOccurrenceMergeAtResult]
                      split
                      · rename_i hok
                        simp only [hok]
                        apply ih
                        exact
                          (mergeAt?_key_compare_of_eq_some state
                            (state.pending.size - 2) merged hmerge).trans
                            hcompare
                      · rename_i hok
                        simp only [hok, if_false]
                        simp [foundNewRunFromMergeAt_eq,
                          eraseOccurrenceFoundNewRunResult]
                · rw [if_neg hcollapse, if_neg hcollapse]
                  have heraseSet := eraseOccurrenceSetTopPower power state
                  simp only [eraseOccurrenceMergeState] at heraseSet
                  rw [heraseSet]
                  cases hset : setTopPower? state power with
                  | none => simp
                  | some updated =>
                      simp [foundNewRunSuccess_eq,
                        eraseOccurrenceFoundNewRunResult]
      · rw [if_neg hdepth, if_neg hdepth]
        have heraseSet := eraseOccurrenceSetTopPower power state
        simp only [eraseOccurrenceMergeState] at heraseSet
        rw [heraseSet]
        cases hset : setTopPower? state power with
        | none => simp
        | some updated =>
            simp [foundNewRunSuccess_eq, eraseOccurrenceFoundNewRunResult]

private theorem eraseOccurrenceFoundNewRun_of_mergeAt
    (lt : BoolComparator alpha)
    (state : MergeState (Occurrence alpha) nu) (n2 : Nat)
    (hcompare : state.key_compare = occurrenceComparator lt)
    (hmergeAt : ∀ (next : MergeState (Occurrence alpha) nu) (i : Nat),
      next.key_compare = occurrenceComparator lt →
        mergeAt? (eraseOccurrenceMergeState next) i =
          (mergeAt? next i).map eraseOccurrenceMergeAtResult) :
    foundNewRun? (eraseOccurrenceMergeState state) n2 =
      (foundNewRun? state n2).map eraseOccurrenceFoundNewRunResult := by
  simp only [eraseOccurrenceMergeState]
  unfold foundNewRun?
  by_cases hempty : state.pending.isEmpty
  · simp [hempty, foundNewRunSuccess_eq,
      eraseOccurrenceFoundNewRunResult, eraseOccurrenceMergeState]
  · rw [if_neg hempty, if_neg hempty]
    cases htop : state.pending[state.pending.size - 1]? with
    | none => simp
    | some top =>
        simp only
        split
        · rename_i hguard
          let traced := powerloopTraced
            (BitVec.ofNat 64 (top.base - state.basekeys)) top.len
            (BitVec.ofNat 64 n2) state.listlen
          by_cases hstopped : !traced.stopped
          · simp [traced, hstopped, foundNewRunOutOfFuel_eq,
              eraseOccurrenceFoundNewRunResult, eraseOccurrenceMergeState]
          · rw [if_neg hstopped, if_neg hstopped]
            have hloop := eraseOccurrenceFoundNewRunLoop_of_mergeAt lt
              state.pending.size state traced.result hcompare hmergeAt
            simpa [traced, eraseOccurrenceMergeState] using hloop
        · rename_i hguard
          simp only [Option.map_none]

private theorem eraseOccurrenceMergeForceCollapseLoop_of_mergeAt
    (lt : BoolComparator alpha) (fuel : Nat)
    (state : MergeState (Occurrence alpha) nu)
    (hcompare : state.key_compare = occurrenceComparator lt)
    (hmergeAt : ∀ (next : MergeState (Occurrence alpha) nu) (i : Nat),
      next.key_compare = occurrenceComparator lt →
        mergeAt? (eraseOccurrenceMergeState next) i =
          (mergeAt? next i).map eraseOccurrenceMergeAtResult) :
    mergeForceCollapseLoop? fuel (eraseOccurrenceMergeState state) =
      (mergeForceCollapseLoop? fuel state).map
        eraseOccurrenceMergeForceCollapseResult := by
  induction fuel generalizing state with
  | zero =>
      simp only [eraseOccurrenceMergeState]
      simp only [mergeForceCollapseLoop?]
      split <;> rfl
  | succ fuel ih =>
      simp only [eraseOccurrenceMergeState]
      simp only [mergeForceCollapseLoop?]
      by_cases hdepth : 1 < state.pending.size
      · rw [if_pos hdepth, if_pos hdepth]
        have heraseIndex := eraseOccurrenceForceCollapseIndex state
        simp only [eraseOccurrenceMergeState] at heraseIndex
        rw [heraseIndex]
        cases hindex : forceCollapseIndex? state with
        | none => simp
        | some i =>
            simp only
            have heraseMerge := hmergeAt state i hcompare
            simp only [eraseOccurrenceMergeState] at heraseMerge
            rw [heraseMerge]
            cases hmerge : mergeAt? state i with
            | none => simp
            | some merged =>
                simp only [Option.map_some,
                  eraseOccurrenceMergeAtResult_returnCode,
                  eraseOccurrenceMergeAtResult_fuelExhausted]
                simp only [eraseOccurrenceMergeAtResult]
                split
                · rename_i hok
                  simp only [hok]
                  apply ih
                  exact
                    (mergeAt?_key_compare_of_eq_some state i merged
                      hmerge).trans hcompare
                · rename_i hok
                  simp only [hok, if_false]
                  rfl
      · rw [if_neg hdepth, if_neg hdepth]
        rfl

private theorem eraseOccurrenceMergeForceCollapse_of_mergeAt
    (lt : BoolComparator alpha)
    (state : MergeState (Occurrence alpha) nu)
    (hcompare : state.key_compare = occurrenceComparator lt)
    (hmergeAt : ∀ (next : MergeState (Occurrence alpha) nu) (i : Nat),
      next.key_compare = occurrenceComparator lt →
        mergeAt? (eraseOccurrenceMergeState next) i =
          (mergeAt? next i).map eraseOccurrenceMergeAtResult) :
    mergeForceCollapse? (eraseOccurrenceMergeState state) =
      (mergeForceCollapse? state).map
        eraseOccurrenceMergeForceCollapseResult := by
  unfold mergeForceCollapse?
  rw [eraseOccurrenceMergeState_pending]
  exact eraseOccurrenceMergeForceCollapseLoop_of_mergeAt lt
    state.pending.size state hcompare hmergeAt

private theorem eraseOccurrenceListSortScanAfterExtension_of_mergeAt
    (lt : BoolComparator alpha) (fuel : Nat)
    (state : MergeState (Occurrence alpha) nu) (lo remaining : Nat)
    (reverse : Bool) (inputSize runLength : Nat) (extensionFuel : Bool)
    (hcompare : state.key_compare = occurrenceComparator lt)
    (hmergeAt : ∀ (next : MergeState (Occurrence alpha) nu) (i : Nat),
      next.key_compare = occurrenceComparator lt →
        mergeAt? (eraseOccurrenceMergeState next) i =
          (mergeAt? next i).map eraseOccurrenceMergeAtResult)
    (hscan : ∀ (nextState : MergeState (Occurrence alpha) nu)
        (nextLo nextRemaining : Nat),
      nextState.key_compare = occurrenceComparator lt →
        listSortScan? fuel (eraseOccurrenceMergeState nextState) nextLo
            nextRemaining reverse inputSize =
          (listSortScan? fuel nextState nextLo nextRemaining reverse
            inputSize).map eraseOccurrenceListSortImplResult) :
    listSortScanAfterExtension? fuel (eraseOccurrenceMergeState state) lo
        remaining reverse inputSize runLength extensionFuel =
      (listSortScanAfterExtension? fuel state lo remaining reverse inputSize
        runLength extensionFuel).map eraseOccurrenceListSortImplResult := by
  unfold listSortScanAfterExtension?
  by_cases hextFuel : extensionFuel
  · rw [if_pos hextFuel, if_pos hextFuel]
    exact eraseOccurrenceFinishListSort state reverse inputSize (-1) true
  · rw [if_neg hextFuel, if_neg hextFuel]
    by_cases hbad : runLength = 0 ∨ remaining < runLength
    · simp [hbad]
    · rw [if_neg hbad, if_neg hbad]
      rw [eraseOccurrenceFoundNewRun_of_mergeAt lt state runLength hcompare
        hmergeAt]
      cases hfound : foundNewRun? state runLength with
      | none => simp
      | some found =>
          simp only [Option.map_some,
            eraseOccurrenceFoundNewRunResult_returnCode,
            eraseOccurrenceFoundNewRunResult_fuelExhausted]
          simp only [eraseOccurrenceFoundNewRunResult]
          split
          · rename_i hok
            simp only [hok, eraseOccurrencePushPendingRun]
            apply hscan
            exact
              (foundNewRun?_key_compare_of_eq_some state runLength found
                hfound).trans hcompare
          · rename_i hok
            simp only [hok, if_false]
            exact eraseOccurrenceFailFromFoundNewRun found reverse inputSize

private theorem eraseOccurrenceListSortScanAfterCount_of_mergeAt
    (lt : BoolComparator alpha) (fuel : Nat)
    (state : MergeState (Occurrence alpha) nu) (lo remaining : Nat)
    (reverse : Bool) (inputSize : Nat)
    (counted : CountRunResult (Occurrence alpha) nu)
    (hcompare : state.key_compare = occurrenceComparator lt)
    (hmergeAt : ∀ (next : MergeState (Occurrence alpha) nu) (i : Nat),
      next.key_compare = occurrenceComparator lt →
        mergeAt? (eraseOccurrenceMergeState next) i =
          (mergeAt? next i).map eraseOccurrenceMergeAtResult)
    (hscan : ∀ (nextState : MergeState (Occurrence alpha) nu)
        (nextLo nextRemaining : Nat),
      nextState.key_compare = occurrenceComparator lt →
        listSortScan? fuel (eraseOccurrenceMergeState nextState) nextLo
            nextRemaining reverse inputSize =
          (listSortScan? fuel nextState nextLo nextRemaining reverse
            inputSize).map eraseOccurrenceListSortImplResult) :
    listSortScanAfterCount? fuel (eraseOccurrenceMergeState state) lo remaining
        reverse inputSize (eraseOccurrenceCountRunResult counted) =
      (listSortScanAfterCount? fuel state lo remaining reverse inputSize
        counted).map eraseOccurrenceListSortImplResult := by
  unfold listSortScanAfterCount?
  simp only [eraseOccurrenceCountRunResult_slice,
    eraseOccurrenceCountRunResult_length, eraseOccurrenceCountRunResult_fuel,
    eraseOccurrenceMergeState_setData]
  set countedState : MergeState (Occurrence alpha) nu :=
    { state with data := counted.slice }
  have hcountedCompare :
      countedState.key_compare = occurrenceComparator lt := hcompare
  by_cases hcountFuel : counted.fuelExhausted
  · rw [if_pos hcountFuel, if_pos hcountFuel]
    exact eraseOccurrenceFinishListSort countedState reverse inputSize (-1) true
  · rw [if_neg hcountFuel, if_neg hcountFuel]
    by_cases hcountBad : counted.length = 0 ∨ remaining < counted.length
    · simp [hcountBad]
    · rw [if_neg hcountBad, if_neg hcountBad]
      let nextMinrun := minrunNext countedState.minrunState
      let nextState := installMinrunState countedState nextMinrun.state
      have hnextCompare :
          nextState.key_compare = occurrenceComparator lt := hcountedCompare
      let runLength := counted.length
      let target := nextMinrun.result.toNat
      let force := if remaining ≤ target then remaining else target
      by_cases hextend :
          (BitVec.ofNat 64 runLength : PySSize).slt nextMinrun.result
      · have hextendBase :
            (BitVec.ofNat 64 counted.length : PySSize).slt
              (minrunNext countedState.minrunState).result := by
            simpa only [runLength, nextMinrun] using hextend
        have hextendErased :
            (BitVec.ofNat 64 counted.length : PySSize).slt
              (minrunNext
                (eraseOccurrenceMergeState countedState).minrunState).result := by
            simpa only [eraseOccurrenceMergeState_minrunState] using hextendBase
        rw [if_pos hextendErased, if_pos hextendBase]
        by_cases hforce : remaining ≤ target
        · have hforceBase :
              remaining ≤
                (minrunNext countedState.minrunState).result.toNat := by
              simpa only [target, nextMinrun] using hforce
          have hforceErased :
              remaining ≤ (minrunNext
                (eraseOccurrenceMergeState countedState).minrunState).result.toNat := by
              simpa only [eraseOccurrenceMergeState_minrunState] using hforceBase
          simp only [if_pos hforceErased, if_pos hforceBase]
          simp only [eraseOccurrenceMergeState_minrunState,
            eraseOccurrenceInstallMinrunState,
            eraseOccurrenceMergeState_data]
          rw [eraseOccurrenceBinarysort lt nextState nextState.data
            (Int.ofNat lo) remaining runLength hnextCompare]
          cases hsorted : binarysort? nextState nextState.data (Int.ofNat lo)
              remaining runLength with
          | none => simp
          | some sorted =>
              simp only [Option.map_some, bind, Option.bind,
                eraseOccurrenceBinarysortResult_slice,
                eraseOccurrenceBinarysortResult_fuel,
                eraseOccurrenceMergeState_setData]
              exact eraseOccurrenceListSortScanAfterExtension_of_mergeAt lt
                fuel { nextState with data := sorted.slice } lo remaining
                reverse inputSize remaining sorted.fuelExhausted hnextCompare
                hmergeAt hscan
        · have hforceBase :
              ¬ remaining ≤
                (minrunNext countedState.minrunState).result.toNat := by
              simpa only [target, nextMinrun] using hforce
          have hforceErased :
              ¬ remaining ≤ (minrunNext
                (eraseOccurrenceMergeState countedState).minrunState).result.toNat := by
              simpa only [eraseOccurrenceMergeState_minrunState] using hforceBase
          simp only [if_neg hforceErased, if_neg hforceBase]
          simp only [eraseOccurrenceMergeState_minrunState,
            eraseOccurrenceInstallMinrunState,
            eraseOccurrenceMergeState_data]
          rw [eraseOccurrenceBinarysort lt nextState nextState.data
            (Int.ofNat lo) target runLength hnextCompare]
          cases hsorted : binarysort? nextState nextState.data (Int.ofNat lo)
              target runLength with
          | none => simp
          | some sorted =>
              simp only [Option.map_some, bind, Option.bind,
                eraseOccurrenceBinarysortResult_slice,
                eraseOccurrenceBinarysortResult_fuel,
                eraseOccurrenceMergeState_setData]
              exact eraseOccurrenceListSortScanAfterExtension_of_mergeAt lt
                fuel { nextState with data := sorted.slice } lo remaining
                reverse inputSize target sorted.fuelExhausted hnextCompare
                hmergeAt hscan
      · have hextendBase :
            ¬ (BitVec.ofNat 64 counted.length : PySSize).slt
              (minrunNext countedState.minrunState).result := by
            simpa only [runLength, nextMinrun] using hextend
        have hextendErased :
            ¬ (BitVec.ofNat 64 counted.length : PySSize).slt
              (minrunNext
                (eraseOccurrenceMergeState countedState).minrunState).result := by
            simpa only [eraseOccurrenceMergeState_minrunState] using hextendBase
        rw [if_neg hextendErased, if_neg hextendBase]
        simp only [eraseOccurrenceMergeState_minrunState,
          eraseOccurrenceInstallMinrunState, eraseOccurrenceMergeState_data,
          bind, Option.bind, eraseOccurrenceMergeState_setData]
        exact eraseOccurrenceListSortScanAfterExtension_of_mergeAt lt fuel
          { nextState with data := nextState.data } lo remaining reverse
          inputSize runLength false hnextCompare hmergeAt hscan

private theorem eraseOccurrenceListSortScan_of_mergeAt
    (lt : BoolComparator alpha) (fuel : Nat)
    (state : MergeState (Occurrence alpha) nu) (lo remaining : Nat)
    (reverse : Bool) (inputSize : Nat)
    (hcompare : state.key_compare = occurrenceComparator lt)
    (hmergeAt : ∀ (next : MergeState (Occurrence alpha) nu) (i : Nat),
      next.key_compare = occurrenceComparator lt →
        mergeAt? (eraseOccurrenceMergeState next) i =
          (mergeAt? next i).map eraseOccurrenceMergeAtResult) :
    listSortScan? fuel (eraseOccurrenceMergeState state) lo remaining reverse
        inputSize =
      (listSortScan? fuel state lo remaining reverse inputSize).map
        eraseOccurrenceListSortImplResult := by
  induction fuel generalizing state lo remaining with
  | zero =>
      simp only [listSortScan?]
      by_cases hremaining : remaining = 0
      · rw [if_pos hremaining, if_pos hremaining]
        have heraseCollapse :=
          eraseOccurrenceMergeForceCollapse_of_mergeAt lt state hcompare
            hmergeAt
        rw [heraseCollapse]
        cases hcollapse : mergeForceCollapse? state with
        | none => simp
        | some collapsed =>
            simp only [Option.map_some,
              eraseOccurrenceMergeForceCollapseResult_returnCode,
              eraseOccurrenceMergeForceCollapseResult_fuelExhausted]
            simp only [eraseOccurrenceMergeForceCollapseResult]
            split
            · rename_i hok
              simp only [hok]
              exact eraseOccurrenceFinishListSort collapsed.state reverse
                inputSize 0 false
            · rename_i hok
              simp only [hok, if_false]
              exact eraseOccurrenceFailFromCollapse collapsed reverse inputSize
      · rw [if_neg hremaining, if_neg hremaining]
        exact eraseOccurrenceFinishListSort state reverse inputSize (-1) true
  | succ fuel ih =>
      by_cases hremaining : remaining = 0
      · simp only [listSortScan?]
        rw [if_pos hremaining, if_pos hremaining]
        have heraseCollapse :=
          eraseOccurrenceMergeForceCollapse_of_mergeAt lt state hcompare
            hmergeAt
        rw [heraseCollapse]
        cases hcollapse : mergeForceCollapse? state with
        | none => simp
        | some collapsed =>
            simp only [Option.map_some,
              eraseOccurrenceMergeForceCollapseResult_returnCode,
              eraseOccurrenceMergeForceCollapseResult_fuelExhausted]
            simp only [eraseOccurrenceMergeForceCollapseResult]
            split
            · rename_i hok
              simp only [hok]
              exact eraseOccurrenceFinishListSort collapsed.state reverse
                inputSize 0 false
            · rename_i hok
              simp only [hok, if_false]
              exact eraseOccurrenceFailFromCollapse collapsed reverse inputSize
      · have herasedStep :=
          listSortScan_succ_of_remaining_ne_zero fuel
            (eraseOccurrenceMergeState state) lo remaining reverse inputSize
            hremaining
        have hbaseStep :=
          listSortScan_succ_of_remaining_ne_zero fuel state lo remaining
            reverse inputSize hremaining
        rw [herasedStep, hbaseStep]
        have heraseCount := eraseOccurrenceCountRun lt state state.data
          (Int.ofNat lo) remaining hcompare
        rw [eraseOccurrenceMergeState_data]
        rw [heraseCount]
        cases hcount : countRun? state state.data (Int.ofNat lo) remaining with
        | none => simp
        | some counted =>
            simp only [Option.map_some, bind, Option.bind]
            have htail := eraseOccurrenceListSortScanAfterCount_of_mergeAt lt
              fuel state lo remaining reverse inputSize counted hcompare
              hmergeAt
              (fun nextState nextLo nextRemaining hnextCompare =>
                ih nextState nextLo nextRemaining hnextCompare)
            exact htail

@[simp]
theorem eraseOccurrenceFoundNewRun
    (lt : BoolComparator alpha)
    (state : MergeState (Occurrence alpha) nu) (n2 : Nat)
    (hcompare : state.key_compare = occurrenceComparator lt) :
    foundNewRun? (eraseOccurrenceMergeState state) n2 =
      (foundNewRun? state n2).map eraseOccurrenceFoundNewRunResult := by
  exact eraseOccurrenceFoundNewRun_of_mergeAt lt state n2 hcompare
    (fun next i hnext => eraseOccurrenceMergeAt lt next i hnext)

@[simp]
theorem eraseOccurrenceMergeForceCollapse
    (lt : BoolComparator alpha)
    (state : MergeState (Occurrence alpha) nu)
    (hcompare : state.key_compare = occurrenceComparator lt) :
    mergeForceCollapse? (eraseOccurrenceMergeState state) =
      (mergeForceCollapse? state).map
        eraseOccurrenceMergeForceCollapseResult := by
  exact eraseOccurrenceMergeForceCollapse_of_mergeAt lt state hcompare
    (fun next i hnext => eraseOccurrenceMergeAt lt next i hnext)

@[simp]
theorem eraseOccurrenceListSortScan
    (lt : BoolComparator alpha) (fuel : Nat)
    (state : MergeState (Occurrence alpha) nu) (lo remaining : Nat)
    (reverse : Bool) (inputSize : Nat)
    (hcompare : state.key_compare = occurrenceComparator lt) :
    listSortScan? fuel (eraseOccurrenceMergeState state) lo remaining reverse
        inputSize =
      (listSortScan? fuel state lo remaining reverse inputSize).map
        eraseOccurrenceListSortImplResult := by
  exact eraseOccurrenceListSortScan_of_mergeAt lt fuel state lo remaining
    reverse inputSize hcompare
    (fun next i hnext => eraseOccurrenceMergeAt lt next i hnext)

theorem eraseOccurrenceListSortImpl
    (lt : BoolComparator alpha) (reverse hasKeyfunc : Bool)
    (input : SortSlice alpha nu) :
    listSortImpl? lt reverse hasKeyfunc input =
      (listSortImpl? (occurrenceComparator lt) reverse hasKeyfunc
        (tagSortSliceOccurrences input)).map
          eraseOccurrenceListSortImplResult := by
  unfold listSortImpl?
  simp only [tagSortSliceOccurrences_size]
  by_cases hmax : input.entries.size ≤ PY_LIST_MAX
  · rw [if_pos hmax, if_pos hmax]
    rw [← eraseOccurrenceInitialMergeState lt hasKeyfunc input]
    rw [← initialMergeState_occurrence_stopped lt hasKeyfunc input]
    set taggedState :=
      (initialMergeState (occurrenceComparator lt) hasKeyfunc
        (tagSortSliceOccurrences input)).1
    set stopped :=
      (initialMergeState (occurrenceComparator lt) hasKeyfunc
        (tagSortSliceOccurrences input)).2
    have hcompare : taggedState.key_compare = occurrenceComparator lt := by
      simp [taggedState, initialMergeState]
    by_cases hstop : (!stopped) = true
    · rw [if_pos hstop, if_pos hstop]
      exact eraseOccurrenceFinishListSort taggedState reverse
        input.entries.size (-1) true
    · rw [if_neg hstop, if_neg hstop]
      by_cases hsmall : input.entries.size < 2
      · rw [if_pos hsmall, if_pos hsmall]
        exact eraseOccurrenceFinishListSort taggedState reverse
          input.entries.size 0 false
      · rw [if_neg hsmall, if_neg hsmall]
        by_cases hreverse : reverse = true
        · rw [if_pos hreverse, if_pos hreverse]
          rw [eraseOccurrenceMergeState_data,
            eraseOccurrenceSortsliceReverse]
          cases hreversed : sortsliceReverse? taggedState.data 0
              input.entries.size with
          | none => simp
          | some reversed =>
              simp only [Option.map_some,
                eraseOccurrenceReverseSliceResult]
              rw [eraseOccurrenceMergeState_setData]
              by_cases hexhausted : reversed.fuelExhausted = true
              · rw [if_pos hexhausted, if_pos hexhausted]
                exact eraseOccurrenceFinishListSort
                  { taggedState with data := reversed.slice } reverse
                  input.entries.size (-1) true
              · rw [if_neg hexhausted, if_neg hexhausted]
                apply eraseOccurrenceListSortScan lt input.entries.size
                  { taggedState with data := reversed.slice } 0
                  input.entries.size reverse input.entries.size
                exact hcompare
        · rw [if_neg hreverse, if_neg hreverse]
          exact eraseOccurrenceListSortScan lt input.entries.size taggedState
            0 input.entries.size reverse input.entries.size hcompare
  · simp [hmax]

/-- Full occurrence-erasure bridge for the validated public evaluator. -/
theorem eraseOccurrenceListSort
    (lt : BoolComparator alpha) (reverse : Bool)
    (input : ListSortInput alpha nu) :
    listSort? lt reverse input =
      (listSort? (occurrenceComparator lt) reverse
        input.withOccurrenceKeys).map eraseOccurrenceListSortImplResult := by
  unfold listSort?
  simpa only [ListSortInput.withOccurrenceKeys] using
    eraseOccurrenceListSortImpl lt reverse input.hasKeyfunc input.slice

end CPythonListsort
