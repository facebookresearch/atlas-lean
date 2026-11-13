/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Code.Correctness.OriginRelabelMerges
import Code.Correctness.ScanLoopCorrectness

/-!
# Origin relabeling through policy and scan evaluators

This module continues `OriginRelabelMerges` through the raw `merge_at`,
PowerSort-policy, final-collapse, cleanup, and scan evaluators.  Occurrence
origins are proof metadata: every executable comparison observes only the
underlying value, so uniformly mirroring origins commutes with these
evaluators when the state's comparator is the lifted value comparator.

The statements here are deliberately about the raw, untraced evaluator.  The
trace model records concrete entries and therefore needs its own separately
reviewed transport argument.
-/

namespace CPythonListsort

universe u v

variable {alpha : Type u} {nu : Type v}

/-! ## Result and continuation relabelings -/

/-- Relabel the occurrence-bearing state returned by `merge_at`. -/
def mirrorMergeAtResult (size : Nat)
    (result : MergeAtResult (Occurrence alpha) nu) :
    MergeAtResult (Occurrence alpha) nu :=
  { result with state := mirrorMergeState size result.state }

/-- Relabel the occurrence-bearing fields retained at a `merge_at` callsite. -/
def mirrorMergeAtCall (size : Nat)
    (call : MergeAtCall (Occurrence alpha) nu) :
    MergeAtCall (Occurrence alpha) nu :=
  { call with
    state := mirrorMergeState size call.state
    firstB := mirrorSortSliceEntry size call.firstB
    lastA := mirrorSortSliceEntry size call.lastA }

/-- Relabel any continuation selected by `prepareMergeAt?`. -/
def mirrorMergeAtPreparation (size : Nat) :
    MergeAtPreparation (Occurrence alpha) nu →
      MergeAtPreparation (Occurrence alpha) nu
  | .finished result => .finished (mirrorMergeAtResult size result)
  | .mergeLo call => .mergeLo (mirrorMergeAtCall size call)
  | .mergeHi call => .mergeHi (mirrorMergeAtCall size call)

/-- Relabel the occurrence-bearing state returned by `foundNewRun?`. -/
def mirrorFoundNewRunResult (size : Nat)
    (result : FoundNewRunResult (Occurrence alpha) nu) :
    FoundNewRunResult (Occurrence alpha) nu :=
  { result with state := mirrorMergeState size result.state }

/-- Relabel the occurrence-bearing state returned by final collapse. -/
def mirrorMergeForceCollapseResult (size : Nat)
    (result : MergeForceCollapseResult (Occurrence alpha) nu) :
    MergeForceCollapseResult (Occurrence alpha) nu :=
  { result with state := mirrorMergeState size result.state }

/-- Relabel the occurrence-bearing state returned by the top-level scan. -/
def mirrorListSortImplResult (size : Nat)
    (result : ListSortImplResult (Occurrence alpha) nu) :
    ListSortImplResult (Occurrence alpha) nu :=
  { result with state := mirrorMergeState size result.state }

@[simp] theorem mirrorMergeAtResult_state (size : Nat)
    (result : MergeAtResult (Occurrence alpha) nu) :
    (mirrorMergeAtResult size result).state =
      mirrorMergeState size result.state := rfl

@[simp] theorem mirrorMergeAtResult_returnCode (size : Nat)
    (result : MergeAtResult (Occurrence alpha) nu) :
    (mirrorMergeAtResult size result).returnCode = result.returnCode := rfl

@[simp] theorem mirrorMergeAtResult_fuelExhausted (size : Nat)
    (result : MergeAtResult (Occurrence alpha) nu) :
    (mirrorMergeAtResult size result).fuelExhausted =
      result.fuelExhausted := rfl

@[simp] theorem mirrorMergeAtCall_state (size : Nat)
    (call : MergeAtCall (Occurrence alpha) nu) :
    (mirrorMergeAtCall size call).state = mirrorMergeState size call.state := rfl

@[simp] theorem mirrorMergeAtCall_firstB (size : Nat)
    (call : MergeAtCall (Occurrence alpha) nu) :
    (mirrorMergeAtCall size call).firstB =
      mirrorSortSliceEntry size call.firstB := rfl

@[simp] theorem mirrorMergeAtCall_lastA (size : Nat)
    (call : MergeAtCall (Occurrence alpha) nu) :
    (mirrorMergeAtCall size call).lastA =
      mirrorSortSliceEntry size call.lastA := rfl

@[simp] theorem mirrorMergeAtCall_ssa (size : Nat)
    (call : MergeAtCall (Occurrence alpha) nu) :
    (mirrorMergeAtCall size call).ssa = call.ssa := rfl

@[simp] theorem mirrorMergeAtCall_ssb (size : Nat)
    (call : MergeAtCall (Occurrence alpha) nu) :
    (mirrorMergeAtCall size call).ssb = call.ssb := rfl

@[simp] theorem mirrorMergeAtCall_na (size : Nat)
    (call : MergeAtCall (Occurrence alpha) nu) :
    (mirrorMergeAtCall size call).na = call.na := rfl

@[simp] theorem mirrorMergeAtCall_nb (size : Nat)
    (call : MergeAtCall (Occurrence alpha) nu) :
    (mirrorMergeAtCall size call).nb = call.nb := rfl

@[simp] theorem mirrorMergeAtPreparation_state (size : Nat)
    (preparation : MergeAtPreparation (Occurrence alpha) nu) :
    (mirrorMergeAtPreparation size preparation).state =
      mirrorMergeState size preparation.state := by
  cases preparation <;> rfl

@[simp] theorem mirrorFoundNewRunResult_state (size : Nat)
    (result : FoundNewRunResult (Occurrence alpha) nu) :
    (mirrorFoundNewRunResult size result).state =
      mirrorMergeState size result.state := rfl

@[simp] theorem mirrorFoundNewRunResult_returnCode (size : Nat)
    (result : FoundNewRunResult (Occurrence alpha) nu) :
    (mirrorFoundNewRunResult size result).returnCode = result.returnCode := rfl

@[simp] theorem mirrorFoundNewRunResult_fuelExhausted (size : Nat)
    (result : FoundNewRunResult (Occurrence alpha) nu) :
    (mirrorFoundNewRunResult size result).fuelExhausted =
      result.fuelExhausted := rfl

@[simp] theorem mirrorMergeForceCollapseResult_state (size : Nat)
    (result : MergeForceCollapseResult (Occurrence alpha) nu) :
    (mirrorMergeForceCollapseResult size result).state =
      mirrorMergeState size result.state := rfl

@[simp] theorem mirrorMergeForceCollapseResult_returnCode (size : Nat)
    (result : MergeForceCollapseResult (Occurrence alpha) nu) :
    (mirrorMergeForceCollapseResult size result).returnCode =
      result.returnCode := rfl

@[simp] theorem mirrorMergeForceCollapseResult_fuelExhausted (size : Nat)
    (result : MergeForceCollapseResult (Occurrence alpha) nu) :
    (mirrorMergeForceCollapseResult size result).fuelExhausted =
      result.fuelExhausted := rfl

@[simp] theorem mirrorListSortImplResult_state (size : Nat)
    (result : ListSortImplResult (Occurrence alpha) nu) :
    (mirrorListSortImplResult size result).state =
      mirrorMergeState size result.state := rfl

@[simp] theorem mirrorListSortImplResult_returnCode (size : Nat)
    (result : ListSortImplResult (Occurrence alpha) nu) :
    (mirrorListSortImplResult size result).returnCode = result.returnCode := rfl

@[simp] theorem mirrorListSortImplResult_fuelExhausted (size : Nat)
    (result : ListSortImplResult (Occurrence alpha) nu) :
    (mirrorListSortImplResult size result).fuelExhausted =
      result.fuelExhausted := rfl

@[simp] theorem mirrorMergeAtResult_involutive (size : Nat)
    (result : MergeAtResult (Occurrence alpha) nu) :
    mirrorMergeAtResult size (mirrorMergeAtResult size result) = result := by
  cases result
  simp [mirrorMergeAtResult]

@[simp] theorem mirrorMergeAtCall_involutive (size : Nat)
    (call : MergeAtCall (Occurrence alpha) nu) :
    mirrorMergeAtCall size (mirrorMergeAtCall size call) = call := by
  cases call
  simp [mirrorMergeAtCall]

@[simp] theorem mirrorMergeAtPreparation_involutive (size : Nat)
    (preparation : MergeAtPreparation (Occurrence alpha) nu) :
    mirrorMergeAtPreparation size
        (mirrorMergeAtPreparation size preparation) = preparation := by
  cases preparation <;> simp [mirrorMergeAtPreparation]

@[simp] theorem mirrorFoundNewRunResult_involutive (size : Nat)
    (result : FoundNewRunResult (Occurrence alpha) nu) :
    mirrorFoundNewRunResult size (mirrorFoundNewRunResult size result) =
      result := by
  cases result
  simp [mirrorFoundNewRunResult]

@[simp] theorem mirrorMergeForceCollapseResult_involutive (size : Nat)
    (result : MergeForceCollapseResult (Occurrence alpha) nu) :
    mirrorMergeForceCollapseResult size
        (mirrorMergeForceCollapseResult size result) = result := by
  cases result
  simp [mirrorMergeForceCollapseResult]

@[simp] theorem mirrorListSortImplResult_involutive (size : Nat)
    (result : ListSortImplResult (Occurrence alpha) nu) :
    mirrorListSortImplResult size (mirrorListSortImplResult size result) =
      result := by
  cases result
  simp [mirrorListSortImplResult]

/-! ## State-only policy helpers -/

@[simp]
theorem mirrorPushPendingRun (size : Nat)
    (state : MergeState (Occurrence alpha) nu) (run : PendingRun) :
    pushPendingRun (mirrorMergeState size state) run =
      mirrorMergeState size (pushPendingRun state run) := by
  rfl

@[simp]
theorem mirrorInstallMinrunState (size : Nat)
    (state : MergeState (Occurrence alpha) nu) (minrun : MinrunState) :
    installMinrunState (mirrorMergeState size state) minrun =
      mirrorMergeState size (installMinrunState state minrun) := by
  rfl

@[simp]
theorem mirrorMergeState_setData (size : Nat)
    (state : MergeState (Occurrence alpha) nu)
    (data : SortSlice (Occurrence alpha) nu) :
    { mirrorMergeState size state with data := mirrorSortSlice size data } =
      mirrorMergeState size { state with data := data } := by
  rfl

@[simp]
theorem mirrorMergeState_setPending (size : Nat)
    (state : MergeState (Occurrence alpha) nu) (pending : Array PendingRun) :
    { mirrorMergeState size state with pending := pending } =
      mirrorMergeState size { state with pending := pending } := by
  rfl

@[simp]
theorem mirrorSetTopPower (size power : Nat)
    (state : MergeState (Occurrence alpha) nu) :
    setTopPower? (mirrorMergeState size state) power =
      (setTopPower? state power).map (mirrorMergeState size) := by
  simp only [mirrorMergeState]
  unfold setTopPower?
  by_cases hempty : state.pending.isEmpty
  · simp [hempty]
  · rw [if_neg hempty, if_neg hempty]
    cases htop : state.pending[state.pending.size - 1]? with
    | none => simp [htop]
    | some top => simp [htop, mirrorMergeState]

@[simp]
theorem mirrorForceCollapseIndex (size : Nat)
    (state : MergeState (Occurrence alpha) nu) :
    forceCollapseIndex? (mirrorMergeState size state) =
      forceCollapseIndex? state := by
  simp [forceCollapseIndex?, mirrorMergeState]

/-! ## `merge_at` -/

/-- The stack splice and both trimming searches commute with mirrored-origin
relabeling.  In particular, the retained endpoint entries in a selected call
are relabeled along with the state; all numeric geometry and gallop results
are identical. -/
theorem mirrorPrepareMergeAt (lt : BoolComparator alpha) (size : Nat)
    (state : MergeState (Occurrence alpha) nu) (i : Nat)
    (hcompare : state.key_compare = occurrenceComparator lt) :
    prepareMergeAt? (mirrorMergeState size state) i =
      (prepareMergeAt? state i).map (mirrorMergeAtPreparation size) := by
  simp only [mirrorMergeState]
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
              have hmirrorCall :
                  { mirrorMergeState size state with
                    pending :=
                      (state.pending.setIfInBounds i
                        { left with len := left.len + right.len }).eraseIdxIfInBounds
                          (i + 1) } = mirrorMergeState size call := rfl
              have hmirrorCall' := hmirrorCall
              simp only [mirrorMergeState] at hmirrorCall'
              rw [hmirrorCall']
              have hcallCompare :
                  call.key_compare = occurrenceComparator lt := hcompare
              have hcallData : call.data = state.data := rfl
              rw [← hcallData]
              rw [mirrorSortSlice_read]
              cases hfirst : call.data.read? (Int.ofNat right.base) with
              | none => simp
              | some firstB =>
                  simp only [Option.map_some]
                  have hgallopRight :
                      gallopRight? (mirrorMergeState size call)
                          (mirrorSortSlice size call.data)
                          (Int.ofNat left.base)
                          (mirrorOccurrence size firstB.key) left.len.toNat 0 =
                        gallopRight? call call.data (Int.ofNat left.base)
                          firstB.key left.len.toNat 0 := by
                    simpa [call] using
                      (mirrorGallopRight lt size call call.data
                        (Int.ofNat left.base) firstB.key left.len.toNat 0
                        hcallCompare)
                  simp only [mirrorSortSliceEntry_key]
                  simp only [mirrorMergeState] at hgallopRight
                  rw [hgallopRight]
                  cases htrimA : gallopRight? call call.data
                      (Int.ofNat left.base) firstB.key left.len.toNat 0 with
                  | none => simp
                  | some trimA =>
                      simp only [mergeAt_bindOptionAcross_some]
                      by_cases htrimAFuel : trimA.fuelExhausted
                      · simp [htrimAFuel, mirrorMergeAtPreparation,
                          mirrorMergeAtResult, mirrorMergeState, call]
                      · rw [if_neg htrimAFuel, if_neg htrimAFuel]
                        by_cases htrimABounds : left.len.toNat < trimA.index
                        · simp [htrimABounds]
                        · rw [if_neg htrimABounds, if_neg htrimABounds]
                          by_cases hemptyA : left.len.toNat - trimA.index = 0
                          · simp [hemptyA, mirrorMergeAtPreparation,
                              mirrorMergeAtResult, mirrorMergeState, call]
                          · rw [if_neg hemptyA, if_neg hemptyA]
                            rw [mirrorSortSlice_read]
                            cases hlast : call.data.read?
                                (Int.ofNat
                                  (left.base + trimA.index +
                                    (left.len.toNat - trimA.index) - 1)) with
                            | none => simp
                            | some lastA =>
                                simp only [Option.map_some]
                                have hgallopLeft :
                                    gallopLeft? (mirrorMergeState size call)
                                        (mirrorSortSlice size call.data)
                                        (Int.ofNat right.base)
                                        (mirrorOccurrence size lastA.key)
                                        right.len.toNat
                                        (right.len.toNat - 1) =
                                      gallopLeft? call call.data
                                        (Int.ofNat right.base) lastA.key
                                        right.len.toNat
                                        (right.len.toNat - 1) := by
                                  simpa [call] using
                                    (mirrorGallopLeft lt size call call.data
                                      (Int.ofNat right.base) lastA.key
                                      right.len.toNat (right.len.toNat - 1)
                                      hcallCompare)
                                simp only [mirrorSortSliceEntry_key]
                                simp only [mirrorMergeState] at hgallopLeft
                                rw [hgallopLeft]
                                cases htrimB : gallopLeft? call call.data
                                    (Int.ofNat right.base) lastA.key
                                    right.len.toNat (right.len.toNat - 1) with
                                | none => simp
                                | some trimB =>
                                    simp only [mergeAt_bindOptionAcross_some]
                                    by_cases htrimBFuel : trimB.fuelExhausted
                                    · simp [htrimBFuel,
                                        mirrorMergeAtPreparation,
                                        mirrorMergeAtResult, mirrorMergeState,
                                        call]
                                    · rw [if_neg htrimBFuel, if_neg htrimBFuel]
                                      by_cases htrimBBounds :
                                          right.len.toNat < trimB.index
                                      · simp [htrimBBounds]
                                      · rw [if_neg htrimBBounds,
                                          if_neg htrimBBounds]
                                        by_cases hemptyB : trimB.index = 0
                                        · simp [hemptyB,
                                            mirrorMergeAtPreparation,
                                            mirrorMergeAtResult,
                                            mirrorMergeState, call]
                                        · rw [if_neg hemptyB, if_neg hemptyB]
                                          by_cases hlo :
                                              left.len.toNat - trimA.index ≤
                                                trimB.index
                                          · simp [hlo,
                                              mirrorMergeAtPreparation,
                                              mirrorMergeAtCall,
                                              mirrorMergeState, call]
                                          · simp [hlo,
                                              mirrorMergeAtPreparation,
                                              mirrorMergeAtCall,
                                              mirrorMergeState, call]
            · rw [if_neg hgeometry, if_neg hgeometry]
              rfl
  · simp [hposition]

/- Preparation mutates only the pending stack and occurrence-bearing stores;
it never replaces the comparator.  This raw frame lemma is what lets the
explicit comparator premise flow into the selected merge continuation. -/
theorem prepareMergeAt?_key_compare_of_eq_some
    (state : MergeState (Occurrence alpha) nu) (i : Nat)
    (preparation : MergeAtPreparation (Occurrence alpha) nu)
    (hresult : prepareMergeAt? state i = some preparation) :
    preparation.state.key_compare = state.key_compare := by
  unfold prepareMergeAt? at hresult
  by_cases hposition :
      2 ≤ state.pending.size ∧
        (i + 2 = state.pending.size ∨ i + 3 = state.pending.size)
  · rw [if_pos hposition] at hresult
    cases hleft : state.pending[i]? with
    | none => simp [hleft] at hresult
    | some left =>
        simp only [hleft, mergeAt_bindOptionAcross_some] at hresult
        cases hright : state.pending[i + 1]? with
        | none => simp [hright] at hresult
        | some right =>
            simp only [hright, mergeAt_bindOptionAcross_some] at hresult
            by_cases hgeometry :
                (0 : PySSize).slt left.len ∧
                  (0 : PySSize).slt right.len ∧
                  left.base + left.len.toNat = right.base
            · rw [if_pos hgeometry] at hresult
              simp only [combinePendingAt_eq] at hresult
              let call : MergeState (Occurrence alpha) nu :=
                { state with
                  pending :=
                    (state.pending.setIfInBounds i
                      { left with len := left.len + right.len }).eraseIdxIfInBounds
                        (i + 1) }
              have hcallEq :
                  ({ state with
                    pending :=
                      (state.pending.setIfInBounds i
                        { left with len := left.len + right.len }).eraseIdxIfInBounds
                          (i + 1) } : MergeState (Occurrence alpha) nu) = call :=
                rfl
              simp only [hcallEq] at hresult
              cases hfirst : state.data.read? (Int.ofNat right.base) with
              | none =>
                  rw [hfirst] at hresult
                  simp at hresult
              | some firstB =>
                  rw [hfirst] at hresult
                  simp only at hresult
                  cases htrimA : gallopRight? call state.data
                      (Int.ofNat left.base) firstB.key left.len.toNat 0 with
                  | none =>
                      rw [htrimA] at hresult
                      simp at hresult
                  | some trimA =>
                      rw [htrimA] at hresult
                      simp only [mergeAt_bindOptionAcross_some] at hresult
                      by_cases htrimAFuel : trimA.fuelExhausted
                      · rw [if_pos htrimAFuel] at hresult
                        simp at hresult
                        subst preparation
                        rfl
                      · rw [if_neg htrimAFuel] at hresult
                        by_cases htrimABounds : left.len.toNat < trimA.index
                        · simp [htrimABounds] at hresult
                        · rw [if_neg htrimABounds] at hresult
                          by_cases hemptyA : left.len.toNat - trimA.index = 0
                          · rw [if_pos hemptyA] at hresult
                            simp at hresult
                            subst preparation
                            rfl
                          · rw [if_neg hemptyA] at hresult
                            cases hlast : state.data.read?
                                (Int.ofNat
                                  (left.base + trimA.index +
                                    (left.len.toNat - trimA.index) - 1)) with
                            | none =>
                                rw [hlast] at hresult
                                simp at hresult
                            | some lastA =>
                                rw [hlast] at hresult
                                simp only at hresult
                                cases htrimB : gallopLeft? call state.data
                                    (Int.ofNat right.base) lastA.key
                                    right.len.toNat (right.len.toNat - 1) with
                                | none =>
                                    rw [htrimB] at hresult
                                    simp at hresult
                                | some trimB =>
                                    rw [htrimB] at hresult
                                    simp only [mergeAt_bindOptionAcross_some]
                                      at hresult
                                    by_cases htrimBFuel : trimB.fuelExhausted
                                    · rw [if_pos htrimBFuel] at hresult
                                      simp at hresult
                                      subst preparation
                                      rfl
                                    · rw [if_neg htrimBFuel] at hresult
                                      by_cases htrimBBounds :
                                          right.len.toNat < trimB.index
                                      · simp [htrimBBounds] at hresult
                                      · rw [if_neg htrimBBounds] at hresult
                                        by_cases hemptyB : trimB.index = 0
                                        · rw [if_pos hemptyB] at hresult
                                          simp at hresult
                                          subst preparation
                                          rfl
                                        · rw [if_neg hemptyB] at hresult
                                          split at hresult <;>
                                            simp at hresult <;>
                                            subst preparation <;> rfl
            · rw [if_neg hgeometry] at hresult
              simp at hresult
  · simp [hposition] at hresult

/-- Executing an already selected merge continuation commutes with origin
relabeling.  The comparator equation remains explicit because both merge
implementations make executable comparison observations. -/
theorem mirrorFinishMergeAtPreparation (lt : BoolComparator alpha)
    (size : Nat) (preparation : MergeAtPreparation (Occurrence alpha) nu)
    (hcompare : preparation.state.key_compare = occurrenceComparator lt) :
    finishMergeAtPreparation? (mirrorMergeAtPreparation size preparation) =
      (finishMergeAtPreparation? preparation).map (mirrorMergeAtResult size) := by
  cases preparation with
  | finished result => rfl
  | mergeLo call =>
      simp only [mirrorMergeAtPreparation, finishMergeAtPreparation?,
        mirrorMergeAtCall_state, mirrorMergeAtCall_ssa,
        mirrorMergeAtCall_ssb, mirrorMergeAtCall_na, mirrorMergeAtCall_nb]
      rw [mirrorMergeLo lt size call.state call.ssa call.ssb call.na call.nb
        hcompare]
      cases hmerge : mergeLo? call.state call.ssa call.ssb call.na call.nb with
      | none => rfl
      | some result =>
          simp [mirrorMergeAtResult, mirrorMergeLoResult]
  | mergeHi call =>
      simp only [mirrorMergeAtPreparation, finishMergeAtPreparation?,
        mirrorMergeAtCall_state, mirrorMergeAtCall_ssa,
        mirrorMergeAtCall_ssb, mirrorMergeAtCall_na, mirrorMergeAtCall_nb]
      rw [mirrorMergeHi lt size call.state call.ssa call.ssb call.na call.nb
        hcompare]
      cases hmerge : mergeHi? call.state call.ssa call.ssb call.na call.nb with
      | none => rfl
      | some result =>
          simp [mirrorMergeAtResult, mirrorMergeHiResult]

/-- A completed selected continuation retains the comparator stored in its
input preparation. -/
theorem finishMergeAtPreparation?_key_compare_of_eq_some
    (preparation : MergeAtPreparation (Occurrence alpha) nu)
    (result : MergeAtResult (Occurrence alpha) nu)
    (hresult : finishMergeAtPreparation? preparation = some result) :
    result.state.key_compare = preparation.state.key_compare := by
  cases preparation with
  | finished prepared =>
      simp only [finishMergeAtPreparation?, Option.some.injEq] at hresult
      subst result
      rfl
  | mergeLo call =>
      simp only [finishMergeAtPreparation?] at hresult
      cases hmerge : mergeLo? call.state call.ssa call.ssb call.na call.nb with
      | none => simp [hmerge] at hresult
      | some merged =>
          simp [hmerge] at hresult
          subst result
          simpa only [MergeAtPreparation.state] using
            (mergeLo?_key_compare_of_eq_some hmerge)
  | mergeHi call =>
      simp only [finishMergeAtPreparation?] at hresult
      cases hmerge : mergeHi? call.state call.ssa call.ssb call.na call.nb with
      | none => simp [hmerge] at hresult
      | some merged =>
          simp [hmerge] at hresult
          subst result
          simpa only [MergeAtPreparation.state] using
            (mergeHi?_key_compare_of_eq_some hmerge)

/-- The complete raw `merge_at` evaluator commutes with mirrored-origin
relabeling. -/
@[simp]
theorem mirrorMergeAt (lt : BoolComparator alpha) (size : Nat)
    (state : MergeState (Occurrence alpha) nu) (i : Nat)
    (hcompare : state.key_compare = occurrenceComparator lt) :
    mergeAt? (mirrorMergeState size state) i =
      (mergeAt? state i).map (mirrorMergeAtResult size) := by
  unfold mergeAt?
  rw [mirrorPrepareMergeAt lt size state i hcompare]
  cases hprepare : prepareMergeAt? state i with
  | none => rfl
  | some preparation =>
      simp only [Option.map_some, mergeAt_bindOptionAcross_some]
      apply mirrorFinishMergeAtPreparation lt size preparation
      rw [prepareMergeAt?_key_compare_of_eq_some state i preparation hprepare]
      exact hcompare

/-- A successful raw `merge_at` result preserves the stored comparator. -/
theorem mergeAt?_key_compare_of_eq_some
    (state : MergeState (Occurrence alpha) nu) (i : Nat)
    (result : MergeAtResult (Occurrence alpha) nu)
    (hresult : mergeAt? state i = some result) :
    result.state.key_compare = state.key_compare := by
  unfold mergeAt? at hresult
  cases hprepare : prepareMergeAt? state i with
  | none => simp [hprepare] at hresult
  | some preparation =>
      have hpreFrame :=
        prepareMergeAt?_key_compare_of_eq_some state i preparation hprepare
      have hfinish :=
        finishMergeAtPreparation?_key_compare_of_eq_some preparation result
          (by simpa [hprepare] using hresult)
      exact hfinish.trans hpreFrame

/-! ## `found_new_run` -/

theorem setTopPower?_key_compare_of_eq_some
    (state updated : MergeState (Occurrence alpha) nu) (power : Nat)
    (hresult : setTopPower? state power = some updated) :
    updated.key_compare = state.key_compare := by
  unfold setTopPower? at hresult
  split at hresult <;> simp_all
  split at hresult <;> simp_all
  subst updated
  rfl

/-- Every successful raw policy-loop result retains the input comparator. -/
theorem foundNewRunLoop?_key_compare_of_eq_some
    (fuel : Nat) (state : MergeState (Occurrence alpha) nu) (power : Nat)
    (result : FoundNewRunResult (Occurrence alpha) nu)
    (hresult : foundNewRunLoop? fuel state power = some result) :
    result.state.key_compare = state.key_compare := by
  induction fuel generalizing state with
  | zero =>
      simp [foundNewRunLoop?, foundNewRunOutOfFuel_eq] at hresult
      subst result
      rfl
  | succ fuel ih =>
      simp only [foundNewRunLoop?] at hresult
      by_cases hdepth : 1 < state.pending.size
      · rw [if_pos hdepth] at hresult
        cases hpreceding : state.pending[state.pending.size - 2]? with
        | none => simp [hpreceding] at hresult
        | some preceding =>
            simp only [hpreceding] at hresult
            cases hpower : preceding.power with
            | none => simp [hpower] at hresult
            | some precedingPower =>
                simp only [hpower] at hresult
                by_cases hcollapse : power < precedingPower
                · rw [if_pos hcollapse] at hresult
                  cases hmerge : mergeAt? state (state.pending.size - 2) with
                  | none => simp [hmerge] at hresult
                  | some merged =>
                      simp only [hmerge] at hresult
                      by_cases hok :
                          merged.returnCode = 0 ∧ !merged.fuelExhausted
                      · rw [if_pos hok] at hresult
                        exact (ih merged.state hresult).trans
                          (mergeAt?_key_compare_of_eq_some state
                            (state.pending.size - 2) merged hmerge)
                      · rw [if_neg hok] at hresult
                        simp only [foundNewRunFromMergeAt_eq,
                          Option.some.injEq] at hresult
                        subst result
                        exact mergeAt?_key_compare_of_eq_some state
                          (state.pending.size - 2) merged hmerge
                · rw [if_neg hcollapse] at hresult
                  cases hset : setTopPower? state power with
                  | none => simp [hset] at hresult
                  | some updated =>
                      simp only [hset, foundNewRunSuccess_eq,
                        Option.some.injEq] at hresult
                      subst result
                      exact setTopPower?_key_compare_of_eq_some state updated
                        power hset
      · rw [if_neg hdepth] at hresult
        cases hset : setTopPower? state power with
        | none => simp [hset] at hresult
        | some updated =>
            simp only [hset, foundNewRunSuccess_eq,
              Option.some.injEq] at hresult
            subst result
            exact setTopPower?_key_compare_of_eq_some state updated power hset

/-- The raw policy loop commutes with origin relabeling. -/
theorem mirrorFoundNewRunLoop (lt : BoolComparator alpha) (size fuel : Nat)
    (state : MergeState (Occurrence alpha) nu) (power : Nat)
    (hcompare : state.key_compare = occurrenceComparator lt) :
    foundNewRunLoop? fuel (mirrorMergeState size state) power =
      (foundNewRunLoop? fuel state power).map
        (mirrorFoundNewRunResult size) := by
  induction fuel generalizing state with
  | zero =>
      simp [foundNewRunLoop?, foundNewRunOutOfFuel_eq,
        mirrorFoundNewRunResult, mirrorMergeState]
  | succ fuel ih =>
      simp only [mirrorMergeState]
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
                  have hmirrorMerge := mirrorMergeAt lt size state
                    (state.pending.size - 2) hcompare
                  simp only [mirrorMergeState] at hmirrorMerge
                  rw [hmirrorMerge]
                  cases hmerge : mergeAt? state (state.pending.size - 2) with
                  | none => simp
                  | some merged =>
                      simp only [Option.map_some,
                        mirrorMergeAtResult_returnCode,
                        mirrorMergeAtResult_fuelExhausted]
                      simp only [mirrorMergeAtResult]
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
                          mirrorFoundNewRunResult]
                · rw [if_neg hcollapse, if_neg hcollapse]
                  have hmirrorSet := mirrorSetTopPower size power state
                  simp only [mirrorMergeState] at hmirrorSet
                  rw [hmirrorSet]
                  cases hset : setTopPower? state power with
                  | none => simp
                  | some updated =>
                      simp [foundNewRunSuccess_eq,
                        mirrorFoundNewRunResult]
      · rw [if_neg hdepth, if_neg hdepth]
        have hmirrorSet := mirrorSetTopPower size power state
        simp only [mirrorMergeState] at hmirrorSet
        rw [hmirrorSet]
        cases hset : setTopPower? state power with
        | none => simp
        | some updated =>
            simp [foundNewRunSuccess_eq, mirrorFoundNewRunResult]

/-- Every successful `foundNewRun?` result retains the input comparator. -/
theorem foundNewRun?_key_compare_of_eq_some
    (state : MergeState (Occurrence alpha) nu) (n2 : Nat)
    (result : FoundNewRunResult (Occurrence alpha) nu)
    (hresult : foundNewRun? state n2 = some result) :
    result.state.key_compare = state.key_compare := by
  unfold foundNewRun? at hresult
  by_cases hempty : state.pending.isEmpty
  · rw [if_pos hempty] at hresult
    simp [foundNewRunSuccess_eq] at hresult
    subst result
    rfl
  · rw [if_neg hempty] at hresult
    cases htop : state.pending[state.pending.size - 1]? with
    | none => simp [htop] at hresult
    | some top =>
        simp only [htop] at hresult
        split at hresult
        · split at hresult
          · simp [foundNewRunOutOfFuel_eq] at hresult
            subst result
            rfl
          · exact foundNewRunLoop?_key_compare_of_eq_some _ _ _ _ hresult
        · simp_all

/-- The complete raw `found_new_run` evaluator commutes with mirrored-origin
relabeling. -/
@[simp]
theorem mirrorFoundNewRun (lt : BoolComparator alpha) (size : Nat)
    (state : MergeState (Occurrence alpha) nu) (n2 : Nat)
    (hcompare : state.key_compare = occurrenceComparator lt) :
    foundNewRun? (mirrorMergeState size state) n2 =
      (foundNewRun? state n2).map (mirrorFoundNewRunResult size) := by
  simp only [mirrorMergeState]
  unfold foundNewRun?
  by_cases hempty : state.pending.isEmpty
  · simp [hempty, foundNewRunSuccess_eq, mirrorFoundNewRunResult,
      mirrorMergeState]
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
              mirrorFoundNewRunResult, mirrorMergeState]
          · rw [if_neg hstopped, if_neg hstopped]
            have hloop := mirrorFoundNewRunLoop lt size state.pending.size state
              traced.result hcompare
            simpa [traced, mirrorMergeState] using hloop
        · rename_i hguard
          simp only [Option.map_none]

/-! ## Final collapse -/

/-- A successful raw final-collapse loop retains the input comparator. -/
theorem mergeForceCollapseLoop?_key_compare_of_eq_some
    (fuel : Nat) (state : MergeState (Occurrence alpha) nu)
    (result : MergeForceCollapseResult (Occurrence alpha) nu)
    (hresult : mergeForceCollapseLoop? fuel state = some result) :
    result.state.key_compare = state.key_compare := by
  induction fuel generalizing state with
  | zero =>
      simp only [mergeForceCollapseLoop?] at hresult
      split at hresult <;>
        simp at hresult <;>
        subst result <;> rfl
  | succ fuel ih =>
      simp only [mergeForceCollapseLoop?] at hresult
      by_cases hdepth : 1 < state.pending.size
      · rw [if_pos hdepth] at hresult
        cases hindex : forceCollapseIndex? state with
        | none => simp [hindex] at hresult
        | some i =>
            simp only [hindex] at hresult
            cases hmerge : mergeAt? state i with
            | none => simp [hmerge] at hresult
            | some merged =>
                simp only [hmerge] at hresult
                by_cases hok :
                    merged.returnCode = 0 ∧ !merged.fuelExhausted
                · rw [if_pos hok] at hresult
                  exact (ih merged.state hresult).trans
                    (mergeAt?_key_compare_of_eq_some state i merged hmerge)
                · rw [if_neg hok] at hresult
                  simp only [Option.some.injEq] at hresult
                  subst result
                  exact mergeAt?_key_compare_of_eq_some state i merged hmerge
      · rw [if_neg hdepth] at hresult
        simp at hresult
        subst result
        rfl

/-- The fuel-bounded final-collapse loop commutes with origin relabeling. -/
theorem mirrorMergeForceCollapseLoop (lt : BoolComparator alpha)
    (size fuel : Nat) (state : MergeState (Occurrence alpha) nu)
    (hcompare : state.key_compare = occurrenceComparator lt) :
    mergeForceCollapseLoop? fuel (mirrorMergeState size state) =
      (mergeForceCollapseLoop? fuel state).map
        (mirrorMergeForceCollapseResult size) := by
  induction fuel generalizing state with
  | zero =>
      simp only [mirrorMergeState]
      simp only [mergeForceCollapseLoop?]
      split <;> rfl
  | succ fuel ih =>
      simp only [mirrorMergeState]
      simp only [mergeForceCollapseLoop?]
      by_cases hdepth : 1 < state.pending.size
      · rw [if_pos hdepth, if_pos hdepth]
        have hmirrorIndex := mirrorForceCollapseIndex size state
        simp only [mirrorMergeState] at hmirrorIndex
        rw [hmirrorIndex]
        cases hindex : forceCollapseIndex? state with
        | none => simp
        | some i =>
            simp only
            have hmirrorMerge := mirrorMergeAt lt size state i hcompare
            simp only [mirrorMergeState] at hmirrorMerge
            rw [hmirrorMerge]
            cases hmerge : mergeAt? state i with
            | none => simp
            | some merged =>
                simp only [Option.map_some,
                  mirrorMergeAtResult_returnCode,
                  mirrorMergeAtResult_fuelExhausted]
                simp only [mirrorMergeAtResult]
                split
                · rename_i hok
                  simp only [hok]
                  apply ih
                  exact
                    (mergeAt?_key_compare_of_eq_some state i merged hmerge).trans
                      hcompare
                · rename_i hok
                  simp only [hok, if_false]
                  rfl
      · rw [if_neg hdepth, if_neg hdepth]
        rfl

/-- The complete raw final-collapse evaluator commutes with origin
relabeling. -/
@[simp]
theorem mirrorMergeForceCollapse (lt : BoolComparator alpha) (size : Nat)
    (state : MergeState (Occurrence alpha) nu)
    (hcompare : state.key_compare = occurrenceComparator lt) :
    mergeForceCollapse? (mirrorMergeState size state) =
      (mergeForceCollapse? state).map
        (mirrorMergeForceCollapseResult size) := by
  unfold mergeForceCollapse?
  rw [mirrorMergeState_pending]
  exact mirrorMergeForceCollapseLoop lt size state.pending.size state hcompare

/-! ## Cleanup -/

/-- Final reverse and temporary-storage cleanup commute with occurrence-origin
relabeling. -/
@[simp]
theorem mirrorFinishListSort (size : Nat)
    (state : MergeState (Occurrence alpha) nu) (reverse : Bool)
    (inputSize : Nat) (returnCode : Int) (fuelExhausted : Bool) :
    finishListSort? (mirrorMergeState size state) reverse inputSize
        returnCode fuelExhausted =
      (finishListSort? state reverse inputSize returnCode fuelExhausted).map
        (mirrorListSortImplResult size) := by
  unfold finishListSort?
  by_cases hreverse : reverse && decide (1 < inputSize)
  · rw [if_pos hreverse, if_pos hreverse]
    simp only [mirrorMergeState_data]
    rw [mirrorSortsliceReverse]
    cases hreversed : sortsliceReverse? state.data 0 inputSize with
    | none => simp
    | some reversed =>
        simp only [Option.map_some, bind, Option.bind,
          mirrorReverseSliceResult]
        rw [mirrorMergeState_setData, mirrorMergeFreemem]
        rfl
  · rw [if_neg hreverse, if_neg hreverse]
    simp only [bind, Option.bind]
    rw [mirrorMergeFreemem]
    rfl

@[simp]
theorem mirrorFailFromFoundNewRun (size : Nat)
    (result : FoundNewRunResult (Occurrence alpha) nu) (reverse : Bool)
    (inputSize : Nat) :
    failFromFoundNewRun? (mirrorFoundNewRunResult size result) reverse
        inputSize =
      (failFromFoundNewRun? result reverse inputSize).map
        (mirrorListSortImplResult size) := by
  simp [failFromFoundNewRun?]

@[simp]
theorem mirrorFailFromCollapse (size : Nat)
    (result : MergeForceCollapseResult (Occurrence alpha) nu) (reverse : Bool)
    (inputSize : Nat) :
    failFromCollapse? (mirrorMergeForceCollapseResult size result) reverse
        inputSize =
      (failFromCollapse? result reverse inputSize).map
        (mirrorListSortImplResult size) := by
  simp [failFromCollapse?]

/-! ## Scan continuations -/

/-- The continuation shared by the binarysort and already-long-enough arms of
one scan iteration.  This is definitionally the tail of `listSortScan?`; naming
it keeps the origin-parametricity proof aligned with the evaluator's actual
control-flow boundary. -/
private def listSortScanAfterExtension? (fuel : Nat)
    (state : MergeState (Occurrence alpha) nu) (lo remaining : Nat)
    (reverse : Bool) (inputSize runLength : Nat) (extensionFuel : Bool) :
    Option (ListSortImplResult (Occurrence alpha) nu) :=
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

/-- The portion of one scan iteration following a successful natural-run
scan.  It is a definitional factorization of the corresponding `do`-block in
`listSortScan?`, not a second evaluator specification. -/
private def listSortScanAfterCount? (fuel : Nat)
    (state : MergeState (Occurrence alpha) nu) (lo remaining : Nat)
    (reverse : Bool) (inputSize : Nat)
    (counted : CountRunResult (Occurrence alpha) nu) :
    Option (ListSortImplResult (Occurrence alpha) nu) :=
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

/-- Origin relabeling commutes with the post-extension scan continuation,
assuming the recursive scan call itself commutes. -/
private theorem mirrorListSortScanAfterExtension
    (lt : BoolComparator alpha) (size fuel : Nat)
    (state : MergeState (Occurrence alpha) nu) (lo remaining : Nat)
    (reverse : Bool) (inputSize runLength : Nat) (extensionFuel : Bool)
    (hcompare : state.key_compare = occurrenceComparator lt)
    (hscan : ∀ (nextState : MergeState (Occurrence alpha) nu)
        (nextLo nextRemaining : Nat),
      nextState.key_compare = occurrenceComparator lt →
        listSortScan? fuel (mirrorMergeState size nextState) nextLo
            nextRemaining reverse inputSize =
          (listSortScan? fuel nextState nextLo nextRemaining reverse
            inputSize).map (mirrorListSortImplResult size)) :
    listSortScanAfterExtension? fuel (mirrorMergeState size state) lo
        remaining reverse inputSize runLength extensionFuel =
      (listSortScanAfterExtension? fuel state lo remaining reverse inputSize
        runLength extensionFuel).map (mirrorListSortImplResult size) := by
  unfold listSortScanAfterExtension?
  by_cases hextFuel : extensionFuel
  · rw [if_pos hextFuel, if_pos hextFuel]
    exact mirrorFinishListSort size state reverse inputSize (-1) true
  · rw [if_neg hextFuel, if_neg hextFuel]
    by_cases hbad : runLength = 0 ∨ remaining < runLength
    · simp [hbad]
    · rw [if_neg hbad, if_neg hbad]
      rw [mirrorFoundNewRun lt size state runLength hcompare]
      cases hfound : foundNewRun? state runLength with
      | none => simp
      | some found =>
          simp only [Option.map_some,
            mirrorFoundNewRunResult_returnCode,
            mirrorFoundNewRunResult_fuelExhausted]
          simp only [mirrorFoundNewRunResult]
          split
          · rename_i hok
            simp only [hok, mirrorPushPendingRun]
            apply hscan
            exact
              (foundNewRun?_key_compare_of_eq_some state runLength found
                hfound).trans hcompare
          · rename_i hok
            simp only [hok, if_false]
            exact mirrorFailFromFoundNewRun size found reverse inputSize

/-- Origin relabeling commutes with the remainder of a scan iteration after
`countRun?`, assuming the recursive scan call itself commutes. -/
private theorem mirrorListSortScanAfterCount
    (lt : BoolComparator alpha) (size fuel : Nat)
    (state : MergeState (Occurrence alpha) nu) (lo remaining : Nat)
    (reverse : Bool) (inputSize : Nat)
    (counted : CountRunResult (Occurrence alpha) nu)
    (hcompare : state.key_compare = occurrenceComparator lt)
    (hscan : ∀ (nextState : MergeState (Occurrence alpha) nu)
        (nextLo nextRemaining : Nat),
      nextState.key_compare = occurrenceComparator lt →
        listSortScan? fuel (mirrorMergeState size nextState) nextLo
            nextRemaining reverse inputSize =
          (listSortScan? fuel nextState nextLo nextRemaining reverse
            inputSize).map (mirrorListSortImplResult size)) :
    listSortScanAfterCount? fuel (mirrorMergeState size state) lo remaining
        reverse inputSize (mirrorCountRunResult size counted) =
      (listSortScanAfterCount? fuel state lo remaining reverse inputSize
        counted).map (mirrorListSortImplResult size) := by
  unfold listSortScanAfterCount?
  simp only [mirrorCountRunResult_slice, mirrorCountRunResult_length,
    mirrorCountRunResult_fuel, mirrorMergeState_setData]
  set countedState : MergeState (Occurrence alpha) nu :=
    { state with data := counted.slice }
  have hcountedCompare :
      countedState.key_compare = occurrenceComparator lt := hcompare
  by_cases hcountFuel : counted.fuelExhausted
  · rw [if_pos hcountFuel, if_pos hcountFuel]
    exact mirrorFinishListSort size countedState reverse inputSize (-1) true
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
        have hextendMirror :
            (BitVec.ofNat 64 counted.length : PySSize).slt
              (minrunNext (mirrorMergeState size countedState).minrunState).result := by
            simpa only [mirrorMergeState_minrunState] using hextendBase
        rw [if_pos hextendMirror, if_pos hextendBase]
        by_cases hforce : remaining ≤ target
        · have hforceBase :
              remaining ≤ (minrunNext countedState.minrunState).result.toNat := by
              simpa only [target, nextMinrun] using hforce
          have hforceMirror :
              remaining ≤ (minrunNext
                (mirrorMergeState size countedState).minrunState).result.toNat := by
              simpa only [mirrorMergeState_minrunState] using hforceBase
          simp only [if_pos hforceMirror, if_pos hforceBase]
          simp only [mirrorMergeState_minrunState, mirrorInstallMinrunState,
            mirrorMergeState_data]
          rw [mirrorBinarysort lt size nextState nextState.data (Int.ofNat lo)
            remaining runLength hnextCompare]
          cases hsorted : binarysort? nextState nextState.data (Int.ofNat lo)
              remaining runLength with
          | none => simp
          | some sorted =>
              simp only [Option.map_some, bind, Option.bind,
                mirrorBinarysortResult_slice, mirrorBinarysortResult_fuel,
                mirrorMergeState_setData]
              exact mirrorListSortScanAfterExtension lt size fuel
                { nextState with data := sorted.slice } lo remaining reverse
                inputSize remaining sorted.fuelExhausted hnextCompare hscan
        · have hforceBase :
              ¬ remaining ≤ (minrunNext countedState.minrunState).result.toNat := by
              simpa only [target, nextMinrun] using hforce
          have hforceMirror :
              ¬ remaining ≤ (minrunNext
                (mirrorMergeState size countedState).minrunState).result.toNat := by
              simpa only [mirrorMergeState_minrunState] using hforceBase
          simp only [if_neg hforceMirror, if_neg hforceBase]
          simp only [mirrorMergeState_minrunState, mirrorInstallMinrunState,
            mirrorMergeState_data]
          rw [mirrorBinarysort lt size nextState nextState.data (Int.ofNat lo)
            target runLength hnextCompare]
          cases hsorted : binarysort? nextState nextState.data (Int.ofNat lo)
              target runLength with
          | none => simp
          | some sorted =>
              simp only [Option.map_some, bind, Option.bind,
                mirrorBinarysortResult_slice, mirrorBinarysortResult_fuel,
                mirrorMergeState_setData]
              exact mirrorListSortScanAfterExtension lt size fuel
                { nextState with data := sorted.slice } lo remaining reverse
                inputSize target sorted.fuelExhausted hnextCompare hscan
      · have hextendBase :
            ¬ (BitVec.ofNat 64 counted.length : PySSize).slt
              (minrunNext countedState.minrunState).result := by
            simpa only [runLength, nextMinrun] using hextend
        have hextendMirror :
            ¬ (BitVec.ofNat 64 counted.length : PySSize).slt
              (minrunNext (mirrorMergeState size countedState).minrunState).result := by
            simpa only [mirrorMergeState_minrunState] using hextendBase
        rw [if_neg hextendMirror, if_neg hextendBase]
        simp only [mirrorMergeState_minrunState, mirrorInstallMinrunState,
          mirrorMergeState_data, bind, Option.bind, mirrorMergeState_setData]
        exact mirrorListSortScanAfterExtension lt size fuel
          { nextState with data := nextState.data } lo remaining reverse
          inputSize runLength false hnextCompare hscan

/-! ## Complete scan -/

private theorem listSortScan_succ_of_remaining_ne_zero
    (fuel : Nat) (state : MergeState (Occurrence alpha) nu)
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
      let countedState : MergeState (Occurrence alpha) nu :=
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
                  MergeState (Occurrence alpha) nu).minrunState).result := by
            simpa only [runLength, nextMinrun, countedState] using hextend
        simp only [hextendBase, if_true]
        by_cases hforce : remaining ≤ target
        · have hforceBase :
              remaining ≤
                (minrunNext
                  ({ state with data := counted.slice } :
                    MergeState (Occurrence alpha) nu).minrunState).result.toNat := by
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
                    MergeState (Occurrence alpha) nu).minrunState).result.toNat := by
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
                  MergeState (Occurrence alpha) nu).minrunState).result := by
            simpa only [runLength, nextMinrun, countedState] using hextend
        simp [hextendBase, hcountBad]
        split <;> simp_all

/-- The raw scan/final-collapse evaluator commutes with mirrored-origin
relabeling.  The comparator binding is the only semantic premise; no ordering
law is needed for this evaluator equation. -/
@[simp]
theorem mirrorListSortScan (lt : BoolComparator alpha) (size fuel : Nat)
    (state : MergeState (Occurrence alpha) nu) (lo remaining : Nat)
    (reverse : Bool) (inputSize : Nat)
    (hcompare : state.key_compare = occurrenceComparator lt) :
    listSortScan? fuel (mirrorMergeState size state) lo remaining reverse
        inputSize =
      (listSortScan? fuel state lo remaining reverse inputSize).map
        (mirrorListSortImplResult size) := by
  induction fuel generalizing state lo remaining with
  | zero =>
      simp only [listSortScan?]
      by_cases hremaining : remaining = 0
      · rw [if_pos hremaining, if_pos hremaining]
        have hmirrorCollapse :=
          mirrorMergeForceCollapse lt size state hcompare
        rw [hmirrorCollapse]
        cases hcollapse : mergeForceCollapse? state with
        | none => simp
        | some collapsed =>
            simp only [Option.map_some,
              mirrorMergeForceCollapseResult_returnCode,
              mirrorMergeForceCollapseResult_fuelExhausted]
            simp only [mirrorMergeForceCollapseResult]
            split
            · rename_i hok
              simp only [hok]
              exact mirrorFinishListSort size collapsed.state reverse
                inputSize 0 false
            · rename_i hok
              simp only [hok, if_false]
              exact mirrorFailFromCollapse size collapsed reverse inputSize
      · rw [if_neg hremaining, if_neg hremaining]
        exact mirrorFinishListSort size state reverse inputSize (-1) true
  | succ fuel ih =>
      by_cases hremaining : remaining = 0
      · simp only [listSortScan?]
        rw [if_pos hremaining, if_pos hremaining]
        have hmirrorCollapse :=
          mirrorMergeForceCollapse lt size state hcompare
        rw [hmirrorCollapse]
        cases hcollapse : mergeForceCollapse? state with
        | none => simp
        | some collapsed =>
            simp only [Option.map_some,
              mirrorMergeForceCollapseResult_returnCode,
              mirrorMergeForceCollapseResult_fuelExhausted]
            simp only [mirrorMergeForceCollapseResult]
            split
            · rename_i hok
              simp only [hok]
              exact mirrorFinishListSort size collapsed.state reverse
                inputSize 0 false
            · rename_i hok
              simp only [hok, if_false]
              exact mirrorFailFromCollapse size collapsed reverse inputSize
      · have hmirrorStep :=
          listSortScan_succ_of_remaining_ne_zero fuel
            (mirrorMergeState size state) lo remaining reverse inputSize
            hremaining
        have hbaseStep :=
          listSortScan_succ_of_remaining_ne_zero fuel state lo remaining
            reverse inputSize hremaining
        rw [hmirrorStep, hbaseStep]
        have hmirrorCount := mirrorCountRun lt size state state.data
          (Int.ofNat lo) remaining hcompare
        rw [mirrorMergeState_data]
        rw [hmirrorCount]
        cases hcount : countRun? state state.data (Int.ofNat lo) remaining with
        | none => simp
        | some counted =>
            simp only [Option.map_some, bind, Option.bind]
            have htail := mirrorListSortScanAfterCount lt size fuel state lo
              remaining reverse inputSize counted hcompare
              (fun nextState nextLo nextRemaining hnextCompare =>
                ih nextState nextLo nextRemaining hnextCompare)
            exact htail
end CPythonListsort
