/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Code.Assembly.FoundNewRunSafety
import Code.Correctness.MergeAtCorrectness

/-!
# Functional correctness of `found_new_run`

This module carries pending-run correctness and the persistent whole-entry
snapshot through the actual `foundNewRunLoop?` collapse loop.  Pending-power
writes are proved semantically inert, while every taken merge is discharged by
`mergeAt_correct`.
-/

namespace CPythonListsort

universe u v

variable {α : Type u} {ν : Type v}

/-- Semantic state facts preserved by the collapse loop.  The frame is stated
relative to the loop call state, so recursive merge frames compose directly. -/
private structure FoundNewRunSemanticPost
    (lt : BoolComparator α) (input : Array α) (source : SortSlice α ν)
    (pre : MergeState (Occurrence α) ν) (scanned : Nat)
    (result : FoundNewRunResult (Occurrence α) ν) : Prop where
  pendingRunsCorrect : PendingRunsCorrect lt input result.state scanned
  entrySnapshot : EntrySnapshotPermutation source result.state.data
  comparator : result.state.key_compare = occurrenceComparator lt
  consumedFrame : SortSlice.EqualOutsideRange pre.data result.state.data
    pre.basekeys scanned

/-- End-to-end functional certificate for one admitted `found_new_run` call. -/
structure FoundNewRunCorrectnessPost
    (lt : BoolComparator α) (input : Array α) (source : SortSlice α ν)
    (pre : MergeState (Occurrence α) ν) (scanned : Nat)
    (newRun : PendingRun)
    (result : FoundNewRunResult (Occurrence α) ν) : Prop where
  safety : FoundNewRunSafetyPost pre scanned newRun result
  pendingRunsCorrect : PendingRunsCorrect lt input result.state scanned
  entrySnapshot : EntrySnapshotPermutation source result.state.data
  comparator : result.state.key_compare = occurrenceComparator lt
  consumedFrame : SortSlice.EqualOutsideRange pre.data result.state.data
    pre.basekeys scanned

/-- Exact shape of a successful power-only update. -/
private theorem setTopPower_pending_frame
    (state after : MergeState κ ν) (power : Nat)
    (hset : setTopPower? state power = some after) :
    ∃ before top,
      state.pending.toList = before ++ [top] ∧
      after =
        { state with
          pending := state.pending.setIfInBounds (state.pending.size - 1)
            ({ top with power := some power } : PendingRun) } ∧
      after.pending.toList =
        before ++ [{ top with power := some power }] := by
  unfold setTopPower? at hset
  split at hset
  · simp at hset
  · rename_i hnonempty
    generalize hlookup : state.pending[state.pending.size - 1]? = lookup at hset
    cases lookup with
    | none => simp [hlookup] at hset
    | some top =>
        simp only [hlookup] at hset
        have hafter : after =
            { state with
              pending := state.pending.setIfInBounds (state.pending.size - 1)
                ({ top with power := some power } : PendingRun) } := by
          exact (Option.some.inj hset).symm
        have hsizePositive : 0 < state.pending.size := by
          apply Nat.pos_of_ne_zero
          intro hzero
          apply hnonempty
          rw [Array.isEmpty_iff_size_eq_zero]
          exact hzero
        rcases List.eq_nil_or_concat' state.pending.toList with hempty |
            ⟨before, last, hsplit⟩
        · have hsizeZero : state.pending.size = 0 := by
            simpa using congrArg List.length hempty
          omega
        · have hsize : state.pending.size = before.length + 1 := by
            have hlength := congrArg List.length hsplit
            simpa using hlength
          have hlastLookup :
              state.pending[state.pending.size - 1]? = some last := by
            rw [← Array.getElem?_toList, hsplit, hsize]
            simp
          have hlast : last = top := by
            rw [hlookup] at hlastLookup
            exact (Option.some.inj hlastLookup).symm
          subst last
          refine ⟨before, top, hsplit, hafter, ?_⟩
          subst after
          rw [Array.toList_setIfInBounds, hsplit, hsize]
          simp

/-- Stored powers do not participate in the interval-cover invariant. -/
private theorem PendingRunsCover.replace_last_power
    {cursor limit : Nat} {before : List PendingRun} {top : PendingRun}
    {power : Nat}
    (h : PendingRunsCover cursor limit (before ++ [top])) :
    PendingRunsCover cursor limit
      (before ++ [{ top with power := some power }]) := by
  induction before generalizing cursor with
  | nil => simpa [PendingRunsCover, PendingRun.endIndex] using h
  | cons head before ih =>
      simp only [List.cons_append, PendingRunsCover] at h ⊢
      exact ⟨h.1, h.2.1, h.2.2.1, h.2.2.2.1, ih h.2.2.2.2⟩

/-- Writing only the top run's power preserves all semantic correctness facts
used by the scan proof. -/
private theorem setTopPower_preserves_semantics
    {lt : BoolComparator α} {input : Array α} {source : SortSlice α ν}
    {state after : MergeState (Occurrence α) ν} {scanned power : Nat}
    (hset : setTopPower? state power = some after)
    (hcorrect : PendingRunsCorrect lt input state scanned)
    (hsnapshot : EntrySnapshotPermutation source state.data)
    (hcompare : state.key_compare = occurrenceComparator lt) :
    PendingRunsCorrect lt input after scanned ∧
      EntrySnapshotPermutation source after.data ∧
      after.key_compare = occurrenceComparator lt ∧
      SortSlice.EqualOutsideRange state.data after.data state.basekeys scanned := by
  rcases setTopPower_pending_frame state after power hset with
    ⟨before, top, hbefore, hafter, hafterPending⟩
  subst after
  have hcorrectAfter : PendingRunsCorrect lt input
      { state with
        pending := state.pending.setIfInBounds (state.pending.size - 1)
          ({ top with power := some power } : PendingRun) } scanned := by
    rcases hcorrect with ⟨hlayout, hsorted, hstable⟩
    refine ⟨?_, ?_, ?_⟩
    · rcases hlayout with ⟨hnonnegative, hbound, hscanned, hcover⟩
      refine ⟨hnonnegative, hbound, hscanned, ?_⟩
      rw [hafterPending]
      rw [hbefore] at hcover
      exact hcover.replace_last_power
    · intro run hrun
      rw [hafterPending] at hrun
      simp only [List.mem_append, List.mem_singleton] at hrun
      rcases hrun with hrun | rfl
      · exact hsorted run (by rw [hbefore]; simp [hrun])
      · simpa [pendingRunOccurrenceKeys, PendingRun.endIndex] using
          hsorted top (by rw [hbefore]; simp)
    · have hpendingKeys :
          pendingOccurrenceKeys
              { state with
                pending := state.pending.setIfInBounds
                  (state.pending.size - 1)
                  ({ top with power := some power } : PendingRun) } =
            pendingOccurrenceKeys state := by
          unfold pendingOccurrenceKeys
          rw [hafterPending, hbefore]
          simp [pendingRunOccurrenceKeys, PendingRun.endIndex]
      rw [hpendingKeys]
      exact hstable
  refine ⟨hcorrectAfter, hsnapshot, hcompare, ?_⟩
  exact SortSlice.EqualOutsideRange.refl state.data state.basekeys scanned

/-- The precise portion of `mergeAt_correct` consumed by the loop induction.
Keeping it as a parameter lets the recursion expose that every taken merge,
and only a taken merge, invokes the full correctness theorem. -/
private def MergeAtCorrectnessProvider
    (lt : BoolComparator α) (input : Array α) (source : SortSlice α ν)
    (scanned : Nat) : Prop :=
  ∀ (pre : MergeState (Occurrence α) ν) (i : Nat),
    PendingRunsCorrect lt input pre scanned →
    EntrySnapshotPermutation source pre.data →
    pre.key_compare = occurrenceComparator lt →
    pre.listlen.toNat ≤ PY_LIST_MAX →
    (i + 2 = pre.pending.size ∨ i + 3 = pre.pending.size) →
    TempStorageInv pre.a pre.alloced →
    pre.a.Live →
    SortSlice.ValuesModeInvariant pre.a.hasValues pre.data →
    ∃ merged,
      MergeAtSafetyPost pre scanned i (mergeAtTraced? pre i) merged ∧
        PendingRunsCorrect lt input merged.state scanned ∧
        EntrySnapshotPermutation source merged.state.data ∧
        merged.state.key_compare = occurrenceComparator lt ∧
        SortSlice.EqualOutsideRange pre.data merged.state.data
          pre.basekeys scanned

/-- Successful, non-exhausted executions of the real collapse loop preserve
the semantic scan invariants. -/
private theorem foundNewRunLoop_preserves_semantics
    {lt : BoolComparator α} {input : Array α} {source : SortSlice α ν}
    {scanned : Nat}
    (mergeCorrect : MergeAtCorrectnessProvider lt input source scanned)
    (fuel : Nat) (state : MergeState (Occurrence α) ν) (power : Nat)
    (result : FoundNewRunResult (Occurrence α) ν)
    (hloop : foundNewRunLoop? fuel state power = some result)
    (hcode : result.returnCode = 0)
    (hresultFuel : result.fuelExhausted = false)
    (hcorrect : PendingRunsCorrect lt input state scanned)
    (hsnapshot : EntrySnapshotPermutation source state.data)
    (hcompare : state.key_compare = occurrenceComparator lt)
    (hmax : state.listlen.toNat ≤ PY_LIST_MAX)
    (hInv : TempStorageInv state.a state.alloced)
    (hLive : state.a.Live)
    (hMode : SortSlice.ValuesModeInvariant state.a.hasValues state.data) :
    FoundNewRunSemanticPost lt input source state scanned result := by
  induction fuel generalizing state result with
  | zero =>
      simp only [foundNewRunLoop?, foundNewRunOutOfFuel_eq] at hloop
      injection hloop with hresult
      subst result
      change true = false at hresultFuel
      contradiction
  | succ remaining ih =>
      by_cases hmany : 1 < state.pending.size
      · have hloop' := hloop
        simp only [foundNewRunLoop?, hmany, if_pos] at hloop'
        cases hpreceding : state.pending[state.pending.size - 2]? with
        | none => simp [hpreceding] at hloop'
        | some preceding =>
            simp only [hpreceding] at hloop'
            cases hstored : preceding.power with
            | none => simp [hstored] at hloop'
            | some precedingPower =>
                simp only [hstored] at hloop'
                by_cases hguard : power < precedingPower
                · rw [if_pos hguard] at hloop'
                  cases hmerge : mergeAt? state (state.pending.size - 2) with
                  | none => simp [hmerge] at hloop'
                  | some merged =>
                      simp only [hmerge] at hloop'
                      by_cases hsuccess :
                          merged.returnCode = 0 ∧ !merged.fuelExhausted
                      · rw [if_pos hsuccess] at hloop'
                        have hposition :
                            state.pending.size - 2 + 2 = state.pending.size ∨
                              state.pending.size - 2 + 3 =
                                state.pending.size := by
                          left
                          omega
                        rcases mergeCorrect state (state.pending.size - 2)
                            hcorrect hsnapshot hcompare hmax hposition hInv hLive
                            hMode with
                          ⟨certified, hsafety, hmergedCorrect,
                            hmergedSnapshot, hmergedCompare, hmergedFrame⟩
                        have hcertifiedRaw :
                            mergeAt? state (state.pending.size - 2) =
                              some certified := by
                          rw [← hsafety.exactErasure]
                          simpa [TraceResult.erase] using hsafety.resultEq
                        have hcertified : certified = merged := by
                          rw [hmerge] at hcertifiedRaw
                          exact (Option.some.inj hcertifiedRaw).symm
                        subst certified
                        have hmergedMax :
                            merged.state.listlen.toNat ≤ PY_LIST_MAX := by
                          simpa [hsafety.stableFrame.listlen] using hmax
                        have hrecursive := ih merged.state result hloop' hcode
                          hresultFuel hmergedCorrect hmergedSnapshot
                          hmergedCompare hmergedMax hsafety.tempInvariant
                          hsafety.tempLive hsafety.valuesMode
                        refine
                          { pendingRunsCorrect := hrecursive.pendingRunsCorrect
                            entrySnapshot := hrecursive.entrySnapshot
                            comparator := hrecursive.comparator
                            consumedFrame := ?_ }
                        have hrecursiveFrame := hrecursive.consumedFrame
                        rw [hsafety.stableFrame.basekeys] at hrecursiveFrame
                        exact hmergedFrame.trans hrecursiveFrame
                      · rw [if_neg hsuccess] at hloop'
                        injection hloop' with hresult
                        subst result
                        change merged.returnCode = 0 at hcode
                        change merged.fuelExhausted = false at hresultFuel
                        exfalso
                        apply hsuccess
                        exact ⟨hcode, by simp [hresultFuel]⟩
                · rw [if_neg hguard] at hloop'
                  cases hset : setTopPower? state power with
                  | none => simp [hset] at hloop'
                  | some after =>
                      rw [hset] at hloop'
                      injection hloop' with hresult
                      subst result
                      rcases setTopPower_preserves_semantics hset hcorrect
                          hsnapshot hcompare with
                        ⟨hafterCorrect, hafterSnapshot, hafterCompare,
                          hafterFrame⟩
                      exact
                        { pendingRunsCorrect := hafterCorrect
                          entrySnapshot := hafterSnapshot
                          comparator := hafterCompare
                          consumedFrame := hafterFrame }
      · have hloop' := hloop
        simp only [foundNewRunLoop?, hmany, if_false] at hloop'
        cases hset : setTopPower? state power with
        | none => simp [hset] at hloop'
        | some after =>
            rw [hset] at hloop'
            injection hloop' with hresult
            subst result
            rcases setTopPower_preserves_semantics hset hcorrect hsnapshot
                hcompare with
              ⟨hafterCorrect, hafterSnapshot, hafterCompare, hafterFrame⟩
            exact
              { pendingRunsCorrect := hafterCorrect
                entrySnapshot := hafterSnapshot
                comparator := hafterCompare
                consumedFrame := hafterFrame }

/-- The outer empty-stack, assertion-guard, and powerloop branches reduce the
complete evaluator to the semantic loop theorem on every successful ordinary
return. -/
private theorem foundNewRun_preserves_semantics
    {lt : BoolComparator α} {input : Array α} {source : SortSlice α ν}
    {scanned : Nat}
    (mergeCorrect : MergeAtCorrectnessProvider lt input source scanned)
    (state : MergeState (Occurrence α) ν) (n2 : Nat)
    (result : FoundNewRunResult (Occurrence α) ν)
    (hraw : foundNewRun? state n2 = some result)
    (hcode : result.returnCode = 0)
    (hresultFuel : result.fuelExhausted = false)
    (hcorrect : PendingRunsCorrect lt input state scanned)
    (hsnapshot : EntrySnapshotPermutation source state.data)
    (hcompare : state.key_compare = occurrenceComparator lt)
    (hmax : state.listlen.toNat ≤ PY_LIST_MAX)
    (hInv : TempStorageInv state.a state.alloced)
    (hLive : state.a.Live)
    (hMode : SortSlice.ValuesModeInvariant state.a.hasValues state.data) :
    FoundNewRunSemanticPost lt input source state scanned result := by
  unfold foundNewRun? at hraw
  by_cases hempty : state.pending.isEmpty = true
  · rw [if_pos hempty] at hraw
    simp only [foundNewRunSuccess_eq] at hraw
    injection hraw with hresult
    subst result
    exact
      { pendingRunsCorrect := hcorrect
        entrySnapshot := hsnapshot
        comparator := hcompare
        consumedFrame :=
          SortSlice.EqualOutsideRange.refl state.data state.basekeys scanned }
  · rw [if_neg hempty] at hraw
    cases htop : state.pending[state.pending.size - 1]? with
    | none => simp [htop] at hraw
    | some top =>
        simp only [htop] at hraw
        let guard :=
          ((!state.listlen.msb) && decide (state.basekeys ≤ top.base) &&
            (0 : PySSize).slt top.len && decide (0 < n2) &&
            decide (n2 ≤ PY_SSIZE_T_MAX) &&
            decide (top.base - state.basekeys + top.len.toNat + n2 ≤
              state.listlen.toNat))
        by_cases hguard : guard = true
        · have hguard' :
              ((!state.listlen.msb) && decide (state.basekeys ≤ top.base) &&
                (0 : PySSize).slt top.len && decide (0 < n2) &&
                decide (n2 ≤ PY_SSIZE_T_MAX) &&
                decide (top.base - state.basekeys + top.len.toNat + n2 ≤
                  state.listlen.toNat)) = true := hguard
          rw [if_pos hguard'] at hraw
          let powered := powerloopTraced
            (BitVec.ofNat 64 (top.base - state.basekeys)) top.len
            (BitVec.ofNat 64 n2) state.listlen
          by_cases hstopped : (!powered.stopped) = true
          · have hstopped' :
                (!(powerloopTraced
                  (BitVec.ofNat 64 (top.base - state.basekeys)) top.len
                  (BitVec.ofNat 64 n2) state.listlen).stopped) = true :=
              hstopped
            rw [if_pos hstopped'] at hraw
            simp only [foundNewRunOutOfFuel_eq] at hraw
            injection hraw with hresult
            subst result
            change true = false at hresultFuel
            contradiction
          · have hstopped' : ¬
                (!(powerloopTraced
                  (BitVec.ofNat 64 (top.base - state.basekeys)) top.len
                  (BitVec.ofNat 64 n2) state.listlen).stopped) = true :=
              hstopped
            rw [if_neg hstopped'] at hraw
            exact foundNewRunLoop_preserves_semantics mergeCorrect
              state.pending.size state
              (powerloopTraced
                (BitVec.ofNat 64 (top.base - state.basekeys)) top.len
                (BitVec.ofNat 64 n2) state.listlen).result
              result hraw hcode hresultFuel hcorrect hsnapshot hcompare hmax
              hInv hLive hMode
        · have hguard' : ¬
              ((!state.listlen.msb) && decide (state.basekeys ≤ top.base) &&
                (0 : PySSize).slt top.len && decide (0 < n2) &&
                decide (n2 ≤ PY_SSIZE_T_MAX) &&
                decide (top.base - state.basekeys + top.len.toNat + n2 ≤
                  state.listlen.toNat)) = true := hguard
          rw [if_neg hguard'] at hraw
          contradiction

/-- Assembly of the existing safety theorem with the semantic preservation
proof, parameterized only until the concrete `mergeAt_correct` theorem is
installed below. -/
private theorem foundNewRun_correct_of_provider
    {lt : BoolComparator α} (input : Array α) (source : SortSlice α ν)
    (state : MergeState (Occurrence α) ν) (scanned : Nat)
    (newRun : PendingRun)
    (mergeCorrect : MergeAtCorrectnessProvider lt input source scanned)
    (hcorrect : PendingRunsCorrect lt input state scanned)
    (hsnapshot : EntrySnapshotPermutation source state.data)
    (hcompare : state.key_compare = occurrenceComparator lt)
    (hmax : state.listlen.toNat ≤ PY_LIST_MAX)
    (hpowered : PoweredPrefix state)
    (hnewBase : newRun.base = state.basekeys + scanned)
    (hnewNonnegative : newRun.len.Nonnegative)
    (hnewPositive : 0 < newRun.len.toNat)
    (hnewWithin : scanned + newRun.len.toNat ≤ state.listlen.toNat)
    (hInv : TempStorageInv state.a state.alloced)
    (hLive : state.a.Live)
    (hMode : SortSlice.ValuesModeInvariant state.a.hasValues state.data) :
    ∃ result, FoundNewRunCorrectnessPost lt input source state scanned newRun
      result := by
  rcases foundNewRun_safe state scanned newRun hmax hcorrect.layout hpowered
      hnewBase hnewNonnegative hnewPositive hnewWithin hInv hLive hMode with
    ⟨result, hsafety⟩
  have hraw : foundNewRun? state newRun.len.toNat = some result := by
    rw [← hsafety.exactErasure]
    simpa [TraceResult.erase] using hsafety.resultEq
  have hsemantic := foundNewRun_preserves_semantics mergeCorrect state
    newRun.len.toNat result hraw hsafety.returnCode hsafety.resultFuel hcorrect
    hsnapshot hcompare hmax hInv hLive hMode
  exact
    ⟨result,
      { safety := hsafety
        pendingRunsCorrect := hsemantic.pendingRunsCorrect
        entrySnapshot := hsemantic.entrySnapshot
        comparator := hsemantic.comparator
        consumedFrame := hsemantic.consumedFrame }⟩

/-- End-to-end functional correctness of `found_new_run`, including every
strict-power merge taken by its real collapse loop. -/
theorem foundNewRun_correct
    {lt : BoolComparator α} (horder : BoolStrictWeakOrder lt)
    (input : Array α) (source : SortSlice α ν)
    (state : MergeState (Occurrence α) ν) (scanned : Nat)
    (newRun : PendingRun)
    (hcorrect : PendingRunsCorrect lt input state scanned)
    (hsnapshot : EntrySnapshotPermutation source state.data)
    (hcompare : state.key_compare = occurrenceComparator lt)
    (hmax : state.listlen.toNat ≤ PY_LIST_MAX)
    (hpowered : PoweredPrefix state)
    (hnewBase : newRun.base = state.basekeys + scanned)
    (hnewNonnegative : newRun.len.Nonnegative)
    (hnewPositive : 0 < newRun.len.toNat)
    (hnewWithin : scanned + newRun.len.toNat ≤ state.listlen.toNat)
    (hInv : TempStorageInv state.a state.alloced)
    (hLive : state.a.Live)
    (hMode : SortSlice.ValuesModeInvariant state.a.hasValues state.data) :
    ∃ result,
      FoundNewRunCorrectnessPost lt input source state scanned newRun result := by
  have hmerge : MergeAtCorrectnessProvider lt input source scanned := by
    intro pre i hpreCorrect hpreSnapshot hpreCompare hpreMax hposition
      hpreInv hpreLive hpreMode
    rcases mergeAt_correct horder input source pre scanned i hpreCorrect
        hpreSnapshot hpreCompare hpreMax hposition hpreInv hpreLive hpreMode with
      ⟨merged, hmerged⟩
    exact
      ⟨merged, hmerged.safety, hmerged.pendingRunsCorrect,
        hmerged.entrySnapshot, hmerged.comparator, hmerged.consumedFrame⟩
  exact foundNewRun_correct_of_provider input source state scanned newRun hmerge
    hcorrect hsnapshot hcompare hmax hpowered hnewBase hnewNonnegative
    hnewPositive hnewWithin hInv hLive hMode

private def foundNewRunTakenMergeLt : BoolComparator Nat :=
  fun left right => decide (left < right)

private def foundNewRunTakenMergeEntry (value origin : Nat) :
    SortSliceEntry (Occurrence Nat) PUnit :=
  { key := { value := value, origin := origin }, value := none }

private def foundNewRunTakenMergeState : MergeState (Occurrence Nat) PUnit :=
  { min_gallop := MIN_GALLOP
    listlen := 3
    basekeys := 0
    data :=
      { entries :=
          #[foundNewRunTakenMergeEntry 2 0,
            foundNewRunTakenMergeEntry 1 1,
            foundNewRunTakenMergeEntry 3 2] }
    a := { cells := #[], backing := .inline, hasValues := false }
    alloced := 0
    pending :=
      #[{ base := 0, len := 1, power := some 3 },
        { base := 1, len := 1, power := none }]
    key_compare := occurrenceComparator foundNewRunTakenMergeLt
    mr_current := 0
    mr_e := 0
    mr_mask := 0 }

set_option linter.style.nativeDecide false in
/-- Concrete anti-vacuity witness for the strict collapse branch: the stored
power `3` exceeds the incoming power `2`, so the real loop merges the two
one-element runs, observably reorders `2,1` to `1,2`, shrinks the stack, and
then writes power `2` on the combined run. -/
theorem foundNewRunLoop_taken_merge_regression :
    (foundNewRunLoop? 2 foundNewRunTakenMergeState 2).map
        (fun result => result.returnCode) = some 0 ∧
      (foundNewRunLoop? 2 foundNewRunTakenMergeState 2).map
        (fun result => result.fuelExhausted) = some false ∧
      (foundNewRunLoop? 2 foundNewRunTakenMergeState 2).map
        (fun result => result.state.pending.toList.map fun run =>
          (run.base, run.len.toNat, run.power)) =
        some [(0, 2, some 2)] ∧
      (foundNewRunLoop? 2 foundNewRunTakenMergeState 2).map
        (fun result => result.state.data.entries.toList.map fun entry =>
          (entry.key.value, entry.key.origin)) =
        some [(1, 1), (2, 0), (3, 2)] := by
  native_decide

end CPythonListsort
