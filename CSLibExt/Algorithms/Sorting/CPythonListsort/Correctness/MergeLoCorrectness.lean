/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Code.Correctness.EntrySnapshotPermutation
import Code.Correctness.MergeLoInvariant
import Code.Correctness.MergeLoRegressionKernel

/-!
# Functional correctness of `merge_lo`

The central postcondition is exact equality of the affected whole-entry range
with the shared left-biased mathematical merge.  Sortedness, occurrence
stability, key/payload permutation, framing, and persistent snapshot
preservation are exposed as public consequences of that equality.
-/

namespace CPythonListsort

universe u v

variable {alpha : Type u} {nu : Type v}

/-- Public functional postcondition for the exact traced `merge_lo` execution
selected by `prepareMergeAt?`. -/
structure MergeLoCorrectnessPost
    (lt : BoolComparator alpha) (canonical : List (Occurrence alpha))
    (pre : MergeState (Occurrence alpha) nu) (scanned i : Nat)
    (call : MergeAtCall (Occurrence alpha) nu)
    (result : MergeLoResult (Occurrence alpha) nu) : Prop where
  safety : MergeLoSafetyPost pre scanned i call
    (mergeLoTraced? call.state call.ssa call.ssb call.na call.nb) result
  exactRange :
    (sortSliceRangeEntries result.state.data call.ssa.toNat
      (call.na + call.nb)).toList = mergeLoTargetEntries lt call
  sorted : Sorted (occurrenceComparator lt)
    (sortSliceRangeKeys result.state.data call.ssa.toNat
      (call.na + call.nb))
  stable : StableOccurrencePermutation lt canonical
    (sortSliceRangeKeys result.state.data call.ssa.toNat
      (call.na + call.nb)).toList
  rangeEntriesPerm :
    (sortSliceRangeEntries result.state.data call.ssa.toNat
      (call.na + call.nb)).toList.Perm
      (sortSliceRangeEntries call.state.data call.ssa.toNat
        (call.na + call.nb)).toList
  frame : SortSlice.EqualOutsideRange call.state.data result.state.data
    call.ssa.toNat (call.na + call.nb)

/-- Functional certificate for the untraced transcription. -/
structure MergeLoRawCorrectnessPost
    (lt : BoolComparator alpha)
    (call : MergeAtCall (Occurrence alpha) nu)
    (result : MergeLoResult (Occurrence alpha) nu) : Prop where
  resultEq : mergeLo? call.state call.ssa call.ssb call.na call.nb = some result
  exactRange :
    (sortSliceRangeEntries result.state.data call.ssa.toNat
      (call.na + call.nb)).toList = mergeLoTargetEntries lt call
  frame : SortSlice.EqualOutsideRange call.state.data result.state.data
    call.ssa.toNat (call.na + call.nb)

/-- Projecting keys from exact whole-entry output gives the exact key target. -/
theorem mergeLoExactRange_keys
    {lt : BoolComparator alpha}
    {call : MergeAtCall (Occurrence alpha) nu}
    {result : MergeLoResult (Occurrence alpha) nu}
    (hexact :
      (sortSliceRangeEntries result.state.data call.ssa.toNat
        (call.na + call.nb)).toList = mergeLoTargetEntries lt call) :
    (sortSliceRangeKeys result.state.data call.ssa.toNat
      (call.na + call.nb)).toList =
      (mergeLoTargetEntries lt call).map SortSliceEntry.key := by
  simpa [sortSliceRangeKeys] using
    congrArg (List.map SortSliceEntry.key) hexact

/-- Algebraic closure of exact whole-entry output into the public properties. -/
theorem mergeLoCorrectnessPost_of_exactRange
    {lt : BoolComparator alpha} (horder : BoolStrictWeakOrder lt)
    (canonical : List (Occurrence alpha))
    {pre : MergeState (Occurrence alpha) nu} {scanned i : Nat}
    {call : MergeAtCall (Occurrence alpha) nu}
    {result : MergeLoResult (Occurrence alpha) nu}
    (hsafety : MergeLoSafetyPost pre scanned i call
      (mergeLoTraced? call.state call.ssa call.ssb call.na call.nb) result)
    (hsemantic : MergeLoSemanticPre lt call)
    (hstable : StableOccurrencePermutation lt canonical
      ((sortSliceRangeKeys call.state.data call.ssa.toNat call.na).toList ++
        (sortSliceRangeKeys call.state.data call.ssb.toNat call.nb).toList))
    (hexact :
      (sortSliceRangeEntries result.state.data call.ssa.toNat
        (call.na + call.nb)).toList = mergeLoTargetEntries lt call)
    (hframe : SortSlice.EqualOutsideRange call.state.data result.state.data
      call.ssa.toNat (call.na + call.nb)) :
    MergeLoCorrectnessPost lt canonical pre scanned i call result := by
  have hleftPairwise :
      ((mergeLoLeftEntries call).map SortSliceEntry.key).Pairwise
        (DescendingRunSpec.SortedRelation lt) :=
    hsemantic.leftKeysPairwise
  have hrightPairwise :
      ((mergeLoRightEntries call).map SortSliceEntry.key).Pairwise
        (DescendingRunSpec.SortedRelation lt) :=
    hsemantic.rightKeysPairwise
  have hstableInput : StableOccurrencePermutation lt canonical
      ((mergeLoLeftEntries call).map SortSliceEntry.key ++
        (mergeLoRightEntries call).map SortSliceEntry.key) := by
    simpa only [mergeLoLeftEntries_map_key, mergeLoRightEntries_map_key]
      using hstable
  have hpure := stableEntryMerge_correct horder canonical
    (mergeLoLeftEntries call) (mergeLoRightEntries call)
    hleftPairwise hrightPairwise hstableInput
  have hkeys := mergeLoExactRange_keys hexact
  refine
    { safety := hsafety
      exactRange := hexact
      sorted := ?_
      stable := ?_
      rangeEntriesPerm := ?_
      frame := hframe }
  · unfold Sorted
    rw [hkeys]
    exact hpure.1
  · rw [hkeys]
    exact hpure.2.1
  · rw [hexact, mergeLoCombinedEntries_eq_append hsafety.geometry]
    exact hpure.2.2

/-- Exact-erasure bridge from the traced safety certificate to the raw result. -/
theorem MergeLoSafetyPost.rawResultEq
    {pre : MergeState (Occurrence alpha) nu} {scanned i : Nat}
    {call : MergeAtCall (Occurrence alpha) nu}
    {result : MergeLoResult (Occurrence alpha) nu}
    (h : MergeLoSafetyPost pre scanned i call
      (mergeLoTraced? call.state call.ssa call.ssb call.na call.nb) result) :
    mergeLo? call.state call.ssa call.ssb call.na call.nb = some result := by
  have hresult := h.resultEq
  rw [← h.exactErasure]
  exact hresult

/-- Natural affected-range bound exported by the safety geometry. -/
theorem MergeLoSafetyPost.naturalMergedRange
    {pre : MergeState (Occurrence alpha) nu} {scanned i : Nat}
    {call : MergeAtCall (Occurrence alpha) nu}
    {result : MergeLoResult (Occurrence alpha) nu}
    (h : MergeLoSafetyPost pre scanned i call
      (mergeLoTraced? call.state call.ssa call.ssb call.na call.nb) result) :
    call.ssa.toNat + (call.na + call.nb) ≤
      call.state.data.entries.size := by
  have hbase : Int.ofNat call.ssa.toNat = call.ssa :=
    Int.toNat_of_nonneg h.geometry.ssaNonnegative
  have hrange := h.geometry.mergedRange
  rw [← hbase] at hrange
  apply Int.ofNat_le.mp
  simpa only [Int.ofNat_eq_natCast, Nat.cast_add] using hrange

/-- Functional `merge_lo` preserves a persistent whole-entry snapshot. -/
theorem MergeLoCorrectnessPost.preserve_entrySnapshot
    {lt : BoolComparator alpha} {canonical : List (Occurrence alpha)}
    {pre : MergeState (Occurrence alpha) nu} {scanned i : Nat}
    {call : MergeAtCall (Occurrence alpha) nu}
    {result : MergeLoResult (Occurrence alpha) nu}
    (h : MergeLoCorrectnessPost lt canonical pre scanned i call result)
    {source : SortSlice alpha nu}
    (snapshot : EntrySnapshotPermutation source call.state.data) :
    EntrySnapshotPermutation source result.state.data := by
  exact snapshot.preserve_local h.frame h.safety.naturalMergedRange
    h.rangeEntriesPerm

/-! ## Total semantic terminals and movement safety bridges -/

private theorem mergeLoSucceed_correct_total
    {lt : BoolComparator alpha}
    {pre : MergeState (Occurrence alpha) nu} {scanned i : Nat}
    {call : MergeAtCall (Occurrence alpha) nu}
    {machine : MergeLoMachine (Occurrence alpha) nu}
    (hgeometry : MergeAtSafetyGeometry pre scanned i call)
    (h : MergeLoSemanticMachineInvariant lt call machine)
    (hnb : machine.nb = 0) :
    ∃ result,
      mergeLoSucceed? machine = some result ∧
      result.returnCode = 0 ∧ result.fuelExhausted = false ∧
      MergeLoSemanticOutput lt call result.state := by
  rcases mergeLoSucceedTraced_safe (mergeLoAllocated call).state call.na
      (call.ssb + Int.ofNat call.nb) machine h.safety with
    ⟨result, hpost⟩
  have hraw : mergeLoSucceed? machine = some result := by
    rw [← hpost.exactErasure]
    exact hpost.resultEq
  exact ⟨result, hraw, hpost.returnCode, hpost.resultFuel,
    h.succeed hgeometry hnb hraw⟩

private theorem mergeLoCopyBTail_correct_total
    {lt : BoolComparator alpha}
    {pre : MergeState (Occurrence alpha) nu} {scanned i : Nat}
    {call : MergeAtCall (Occurrence alpha) nu}
    {machine : MergeLoMachine (Occurrence alpha) nu}
    (hgeometry : MergeAtSafetyGeometry pre scanned i call)
    (horder : BoolStrictWeakOrder lt)
    (hsemantic : MergeLoSemanticPre lt call)
    (h : MergeLoSemanticMachineInvariant lt call machine)
    (hna : machine.na = 1) (hnb : 0 < machine.nb) :
    ∃ result,
      mergeLoCopyB? machine = some result ∧
      result.returnCode = 0 ∧ result.fuelExhausted = false ∧
      MergeLoSemanticOutput lt call result.state := by
  rcases mergeLoCopyBTraced_safe (mergeLoAllocated call).state call.na
      (call.ssb + Int.ofNat call.nb) machine h.safety hna hnb with
    ⟨result, hpost⟩
  have hraw : mergeLoCopyB? machine = some result := by
    rw [← hpost.exactErasure]
    exact hpost.resultEq
  exact ⟨result, hraw, hpost.returnCode, hpost.resultFuel,
    h.copyBTail hgeometry horder hsemantic hna hnb hraw⟩

private theorem mergeLoCopyAIncr_total
    {lt : BoolComparator alpha}
    {call : MergeAtCall (Occurrence alpha) nu}
    {machine : MergeLoMachine (Occurrence alpha) nu}
    (h : MergeLoSemanticMachineInvariant lt call machine)
    (hna : 0 < machine.na) :
    ∃ next,
      mergeLoCopyAIncr? machine = some next ∧
      MergeLoMachineInvariant (mergeLoAllocated call).state call.na
        (call.ssb + Int.ofNat call.nb) next := by
  rcases mergeLoCopyAIncrTraced_safe (mergeLoAllocated call).state call.na
      (call.ssb + Int.ofNat call.nb) machine h.safety hna with
    ⟨next, hnext, _hsafe, hnextInvariant, _hna, _hnb⟩
  have hraw : mergeLoCopyAIncr? machine = some next := by
    rw [← erase_mergeLoCopyAIncrTraced]
    exact hnext
  exact ⟨next, hraw, hnextInvariant⟩

private theorem mergeLoCopyBIncr_total
    {lt : BoolComparator alpha}
    {call : MergeAtCall (Occurrence alpha) nu}
    {machine : MergeLoMachine (Occurrence alpha) nu}
    (h : MergeLoSemanticMachineInvariant lt call machine)
    (hna : 0 < machine.na) (hnb : 0 < machine.nb) :
    ∃ next,
      mergeLoCopyBIncr? machine = some next ∧
      MergeLoMachineInvariant (mergeLoAllocated call).state call.na
        (call.ssb + Int.ofNat call.nb) next := by
  rcases mergeLoCopyBIncrTraced_safe (mergeLoAllocated call).state call.na
      (call.ssb + Int.ofNat call.nb) machine h.safety hna hnb with
    ⟨next, hnext, _hsafe, hnextInvariant, _hna, _hnb⟩
  have hraw : mergeLoCopyBIncr? machine = some next := by
    rw [← erase_mergeLoCopyBIncrTraced]
    exact hnext
  exact ⟨next, hraw, hnextInvariant⟩

private theorem mergeLoCopyABlock_safety_of_eq_some
    {lt : BoolComparator alpha}
    {call : MergeAtCall (Occurrence alpha) nu}
    {machine : MergeLoMachine (Occurrence alpha) nu}
    (h : MergeLoSemanticMachineInvariant lt call machine)
    (count : Nat) (hcount : count ≤ machine.na)
    (copied : MergeState (Occurrence alpha) nu)
    (hcopy : mergeLoMemcpyTempToData? .gallopTempToData rfl count
      machine.state machine.dest machine.aPos = some copied) :
    MergeLoMachineInvariant (mergeLoAllocated call).state call.na
      (call.ssb + Int.ofNat call.nb)
      { machine with
        state := copied
        dest := machine.dest + Int.ofNat count
        aPos := machine.aPos + count
        na := machine.na - count } := by
  rcases tempToMainMemcpyTraced_post (.lo .gallopTempToData)
      mergeLoGallopTempToDataPermit count machine.state machine.dest
      (Int.ofNat machine.aPos) (h.safety.destRange count hcount)
      (h.safety.tempPrefixInBounds count hcount)
      (h.safety.tempPrefixValuesMode count hcount)
      h.safety.tempInvariant h.safety.tempLive h.safety.valuesMode with
    ⟨tracedCopied, hpost⟩
  have hcore : tempToMainMemcpy? count machine.state machine.dest
      (Int.ofNat machine.aPos) = some copied := by
    rw [tempToMainMemcpy_eq_mergeLo .gallopTempToData rfl]
    exact hcopy
  have htraceCore : tempToMainMemcpy? count machine.state machine.dest
      (Int.ofNat machine.aPos) = some tracedCopied := by
    rw [← hpost.exactErasure]
    exact hpost.success
  have heq : tracedCopied = copied :=
    Option.some.inj (htraceCore.symm.trans hcore)
  subst tracedCopied
  exact h.safety.copyABlock count hcount copied hpost.frame
    (tempToMainMemcpy_temp_eq_of_eq_some count machine.state copied
      machine.dest (Int.ofNat machine.aPos) hcore)
    hpost.valuesMode

private theorem mergeLoCopyBBlock_safety_of_eq_some
    {lt : BoolComparator alpha}
    {call : MergeAtCall (Occurrence alpha) nu}
    {machine : MergeLoMachine (Occurrence alpha) nu}
    (h : MergeLoSemanticMachineInvariant lt call machine)
    (count : Nat) (hcount : count ≤ machine.nb)
    (copiedData : SortSlice (Occurrence alpha) nu)
    (hcopy : mergeDataMemmove? .loGallopB machine.state.data
      machine.dest machine.bPos count = some copiedData) :
    MergeLoMachineInvariant (mergeLoAllocated call).state call.na
      (call.ssb + Int.ofNat call.nb)
      { machine with
        state := { machine.state with data := copiedData }
        dest := machine.dest + Int.ofNat count
        bPos := machine.bPos + Int.ofNat count
        nb := machine.nb - count } := by
  rcases mainDataMemmoveTraced_safe machine.state machine.dest machine.bPos count
      h.safety.tempInvariant h.safety.tempLive h.safety.valuesMode
      (h.safety.destTotalRange count (by omega))
      (h.safety.rightRange count hcount) with ⟨moved, hpost⟩
  have hcoreData : machine.state.data.memmove? machine.dest machine.bPos count =
      some copiedData := by
    simpa [mergeDataMemmove_eq] using hcopy
  have hcoreState : mainDataMemmove? machine.state machine.dest machine.bPos
      count = some moved := by
    rw [← hpost.exactErasure]
    exact hpost.success
  unfold mainDataMemmove? at hcoreState
  rw [hcoreData] at hcoreState
  injection hcoreState with hcoreState
  subst moved
  exact h.safety.copyBBlock count hcount _ hpost.frame rfl hpost.valuesMode

private theorem mergeLoCopyABlock_total
    {lt : BoolComparator alpha}
    {pre : MergeState (Occurrence alpha) nu} {scanned i : Nat}
    {call : MergeAtCall (Occurrence alpha) nu}
    {machine : MergeLoMachine (Occurrence alpha) nu}
    (hgeometry : MergeAtSafetyGeometry pre scanned i call)
    (h : MergeLoSemanticMachineInvariant lt call machine)
    (count : Nat) (hcount : count < machine.na) (hnb : 0 < machine.nb)
    (firstB : SortSliceEntry (Occurrence alpha) nu)
    (hfirstB : machine.state.data.read? machine.bPos = some firstB)
    (activeA : SortSlice (Occurrence alpha) nu)
    (hactiveA : mergeLoTempRun? machine.state.a machine.aPos machine.na =
      some activeA)
    (hpartition : GallopRightPartition machine.state.key_compare activeA 0
      firstB.key machine.na count) :
    ∃ copied,
      mergeLoMemcpyTempToData? .gallopTempToData rfl count machine.state
        machine.dest machine.aPos = some copied ∧
      MergeLoSemanticMachineInvariant lt call
        { machine with
          state := copied
          dest := machine.dest + Int.ofNat count
          aPos := machine.aPos + count
          na := machine.na - count } := by
  have hcountLe : count ≤ machine.na := Nat.le_of_lt hcount
  rcases tempToMainMemcpyTraced_post (.lo .gallopTempToData)
      mergeLoGallopTempToDataPermit count machine.state machine.dest
      (Int.ofNat machine.aPos) (h.safety.destRange count hcountLe)
      (h.safety.tempPrefixInBounds count hcountLe)
      (h.safety.tempPrefixValuesMode count hcountLe)
      h.safety.tempInvariant h.safety.tempLive h.safety.valuesMode with
    ⟨copied, hpost⟩
  have hcore : tempToMainMemcpy? count machine.state machine.dest
      (Int.ofNat machine.aPos) = some copied := by
    rw [← hpost.exactErasure]
    exact hpost.success
  have hcopy : mergeLoMemcpyTempToData? .gallopTempToData rfl count
      machine.state machine.dest machine.aPos = some copied := by
    rw [← tempToMainMemcpy_eq_mergeLo .gallopTempToData rfl]
    exact hcore
  have hsafety := mergeLoCopyABlock_safety_of_eq_some h count hcountLe copied
    hcopy
  exact ⟨copied, hcopy,
    h.copyABlock hgeometry count hcount hnb firstB hfirstB
      (h.gallopRight_beforeBlock firstB activeA hactiveA count hpartition)
      copied hcopy hsafety⟩

private theorem mergeLoCopyBBlock_total
    {lt : BoolComparator alpha}
    {pre : MergeState (Occurrence alpha) nu} {scanned i : Nat}
    {call : MergeAtCall (Occurrence alpha) nu}
    {machine : MergeLoMachine (Occurrence alpha) nu}
    (hgeometry : MergeAtSafetyGeometry pre scanned i call)
    (h : MergeLoSemanticMachineInvariant lt call machine)
    (count : Nat) (hcount : count ≤ machine.nb)
    (firstA : SortSliceEntry (Occurrence alpha) nu)
    (hfirstA : mergeLoTempRead? machine.state.a machine.aPos = some firstA)
    (hpartition : GallopLeftPartition machine.state.key_compare
      machine.state.data machine.bPos firstA.key machine.nb count) :
    ∃ copiedData,
      mergeDataMemmove? .loGallopB machine.state.data machine.dest machine.bPos
        count = some copiedData ∧
      MergeLoSemanticMachineInvariant lt call
        { machine with
          state := { machine.state with data := copiedData }
          dest := machine.dest + Int.ofNat count
          bPos := machine.bPos + Int.ofNat count
          nb := machine.nb - count } := by
  rcases mainDataMemmoveTraced_safe machine.state machine.dest machine.bPos count
      h.safety.tempInvariant h.safety.tempLive h.safety.valuesMode
      (h.safety.destTotalRange count (by omega))
      (h.safety.rightRange count hcount) with ⟨moved, hpost⟩
  have hstateRaw : mainDataMemmove? machine.state machine.dest machine.bPos
      count = some moved := by
    rw [← hpost.exactErasure]
    exact hpost.success
  unfold mainDataMemmove? at hstateRaw
  cases hdata : machine.state.data.memmove? machine.dest machine.bPos count with
  | none => simp [hdata] at hstateRaw
  | some copiedData =>
      simp only [hdata, bind, Option.bind] at hstateRaw
      injection hstateRaw with hstateRaw
      subst moved
      have hcopy : mergeDataMemmove? .loGallopB machine.state.data machine.dest
          machine.bPos count = some copiedData := by
        simpa [mergeDataMemmove_eq] using hdata
      have hsafety := mergeLoCopyBBlock_safety_of_eq_some h count hcount
        copiedData hcopy
      exact ⟨copiedData, hcopy,
        h.copyBBlock hgeometry count hcount firstA hfirstA
          (h.gallopLeft_beforeBlock firstA count hpartition)
          copiedData hcopy hsafety⟩

private structure MergeLoLoopCorrectPost
    (lt : BoolComparator alpha)
    (call : MergeAtCall (Occurrence alpha) nu)
    (execution : Option (MergeLoResult (Occurrence alpha) nu))
    (result : MergeLoResult (Occurrence alpha) nu) : Prop where
  resultEq : execution = some result
  returnCode : result.returnCode = 0
  resultFuel : result.fuelExhausted = false
  semantic : MergeLoSemanticOutput lt call result.state

private theorem mergeLoOrdinary_correct_step
    {lt : BoolComparator alpha}
    {pre : MergeState (Occurrence alpha) nu} {scanned i : Nat}
    {call : MergeAtCall (Occurrence alpha) nu}
    (hgeometry : MergeAtSafetyGeometry pre scanned i call)
    (horder : BoolStrictWeakOrder lt)
    (hsemantic : MergeLoSemanticPre lt call)
    (fuel : Nat) (machine : MergeLoMachine (Occurrence alpha) nu)
    (aCount bCount : Nat)
    (h : MergeLoSemanticMachineInvariant lt call machine)
    (hfuel : MergeLoFuelInvariant (fuel + 1) machine)
    (hna : 1 < machine.na) (hnb : 0 < machine.nb)
    (ih : ∀ (next : MergeLoMachine (Occurrence alpha) nu)
      (phase : MergeLoPhase),
      MergeLoSemanticMachineInvariant lt call next →
      MergeLoFuelInvariant fuel next → 1 < next.na → 0 < next.nb →
      ∃ result, MergeLoLoopCorrectPost lt call
        (mergeLoLoop? fuel next phase) result) :
    ∃ result, MergeLoLoopCorrectPost lt call
      (mergeLoLoop? (fuel + 1) machine (.ordinary aCount bCount)) result := by
  have hactive : ¬ (machine.na ≤ 1 ∨ machine.nb = 0) := by omega
  rcases h.safety.tempReadable (by omega) with ⟨firstA, hfirstASigned⟩
  have hfirstA : mergeLoTempRead? machine.state.a machine.aPos = some firstA := by
    simpa only [mergeTempRead_ofNat] using hfirstASigned
  rcases SortSlice.read_eq_some_of_indexInBounds machine.state.data machine.bPos
      (h.safety.bPosInBounds hnb) with ⟨firstB, hfirstB⟩
  cases hcompare : lt firstB.key.value firstA.key.value with
  | false =>
      have hcompareMachine :
          machine.state.key_compare firstB.key firstA.key = false := by
        rw [h.comparator]
        exact hcompare
      rcases mergeLoCopyAIncr_total h (by omega) with
        ⟨next, hcopy, hnextSafety⟩
      have hnext := h.copyA hgeometry hna hnb firstA firstB hfirstA hfirstB
        hcompare hcopy hnextSafety
      rcases mergeLoCopyAIncr_spec_of_eq_some machine next hcopy with
        ⟨_hdest, _haPos, _hbPos, hnextNa, hnextNb, _hcmp, _htemp,
          _hread, _hframe⟩
      by_cases hterminal : next.na = 1
      · rcases mergeLoCopyBTail_correct_total hgeometry horder hsemantic hnext
          hterminal (by omega) with ⟨result, hresult, hrc, hrfuel, hout⟩
        refine ⟨result, ?_⟩
        refine
          { resultEq := ?_
            returnCode := hrc
            resultFuel := hrfuel
            semantic := hout }
        rw [mergeLoLoop_ordinary_copyA_equation fuel machine aCount bCount
          firstA firstB hactive hfirstA hfirstB hcompareMachine]
        simp [hcopy, hterminal, hresult]
      · have hnextNaPositive : 1 < next.na := by omega
        have hnextFuel : MergeLoFuelInvariant fuel next := by
          unfold MergeLoFuelInvariant at hfuel ⊢
          omega
        let nextACount := aCount + 1
        by_cases hgallop :
            mergeLoCountAtLeastWord nextACount next.minGallop = true
        all_goals dsimp only [nextACount] at hgallop
        · let adjusted := { next with minGallop := next.minGallop + 1 }
          have hadjusted := hnext.setMachineMinGallop (next.minGallop + 1)
          have hadjustedFuel : MergeLoFuelInvariant fuel adjusted := by
            unfold MergeLoFuelInvariant at hnextFuel ⊢
            simpa only [adjusted] using hnextFuel
          rcases ih adjusted .galloping hadjusted hadjustedFuel (by
              simpa only [adjusted] using hnextNaPositive) (by
              simpa only [adjusted, hnextNb] using hnb) with
            ⟨result, hresult⟩
          refine ⟨result, ?_⟩
          refine
            { resultEq := ?_
              returnCode := hresult.returnCode
              resultFuel := hresult.resultFuel
              semantic := hresult.semantic }
          rw [mergeLoLoop_ordinary_copyA_equation fuel machine aCount bCount
            firstA firstB hactive hfirstA hfirstB hcompareMachine]
          simp only [hcopy, bind, Option.bind, hterminal, if_false]
          rw [if_pos hgallop]
          change mergeLoLoop? fuel adjusted .galloping = some result
          exact hresult.resultEq
        · rcases ih next (.ordinary nextACount 0) hnext hnextFuel
            hnextNaPositive (by omega) with ⟨result, hresult⟩
          refine ⟨result, ?_⟩
          refine
            { resultEq := ?_
              returnCode := hresult.returnCode
              resultFuel := hresult.resultFuel
              semantic := hresult.semantic }
          rw [mergeLoLoop_ordinary_copyA_equation fuel machine aCount bCount
            firstA firstB hactive hfirstA hfirstB hcompareMachine]
          simp [hcopy, hterminal, hgallop, nextACount, hresult.resultEq]
  | true =>
      have hcompareMachine :
          machine.state.key_compare firstB.key firstA.key = true := by
        rw [h.comparator]
        exact hcompare
      rcases mergeLoCopyBIncr_total h (by omega) hnb with
        ⟨next, hcopy, hnextSafety⟩
      have hnext := h.copyB hgeometry (by omega) hnb firstA firstB hfirstA
        hfirstB hcompare hcopy hnextSafety
      rcases mergeLoCopyBIncr_spec_of_eq_some machine next hcopy with
        ⟨_hdest, _haPos, _hbPos, hnextNa, hnextNb, _hcmp, _htemp,
          _hread, _hframe⟩
      by_cases hterminal : next.nb = 0
      · rcases mergeLoSucceed_correct_total hgeometry hnext hterminal with
          ⟨result, hresult, hrc, hrfuel, hout⟩
        refine ⟨result, ?_⟩
        refine
          { resultEq := ?_
            returnCode := hrc
            resultFuel := hrfuel
            semantic := hout }
        rw [mergeLoLoop_ordinary_copyB_equation fuel machine aCount bCount
          firstA firstB hactive hfirstA hfirstB hcompareMachine]
        simp [hcopy, hterminal, hresult]
      · have hnextNbPositive : 0 < next.nb := by omega
        have hnextFuel : MergeLoFuelInvariant fuel next := by
          unfold MergeLoFuelInvariant at hfuel ⊢
          omega
        let nextBCount := bCount + 1
        by_cases hgallop :
            mergeLoCountAtLeastWord nextBCount next.minGallop = true
        all_goals dsimp only [nextBCount] at hgallop
        · let adjusted := { next with minGallop := next.minGallop + 1 }
          have hadjusted := hnext.setMachineMinGallop (next.minGallop + 1)
          have hadjustedFuel : MergeLoFuelInvariant fuel adjusted := by
            unfold MergeLoFuelInvariant at hnextFuel ⊢
            simpa only [adjusted] using hnextFuel
          rcases ih adjusted .galloping hadjusted hadjustedFuel (by
              simpa only [adjusted, hnextNa] using hna) (by
              simpa only [adjusted] using hnextNbPositive) with
            ⟨result, hresult⟩
          refine ⟨result, ?_⟩
          refine
            { resultEq := ?_
              returnCode := hresult.returnCode
              resultFuel := hresult.resultFuel
              semantic := hresult.semantic }
          rw [mergeLoLoop_ordinary_copyB_equation fuel machine aCount bCount
            firstA firstB hactive hfirstA hfirstB hcompareMachine]
          simp only [hcopy, bind, Option.bind, hterminal, if_false]
          rw [if_pos hgallop]
          change mergeLoLoop? fuel adjusted .galloping = some result
          exact hresult.resultEq
        · rcases ih next (.ordinary 0 nextBCount) hnext hnextFuel
            (by omega) hnextNbPositive with ⟨result, hresult⟩
          refine ⟨result, ?_⟩
          refine
            { resultEq := ?_
              returnCode := hresult.returnCode
              resultFuel := hresult.resultFuel
              semantic := hresult.semantic }
          rw [mergeLoLoop_ordinary_copyB_equation fuel machine aCount bCount
            firstA firstB hactive hfirstA hfirstB hcompareMachine]
          simp [hcopy, hterminal, hgallop, nextBCount, hresult.resultEq]

private theorem mergeLoGalloping_correct_step
    {lt : BoolComparator alpha}
    {pre : MergeState (Occurrence alpha) nu} {scanned i : Nat}
    {call : MergeAtCall (Occurrence alpha) nu}
    (hgeometry : MergeAtSafetyGeometry pre scanned i call)
    (horder : BoolStrictWeakOrder lt)
    (hsemantic : MergeLoSemanticPre lt call)
    (fuel : Nat) (machine : MergeLoMachine (Occurrence alpha) nu)
    (h : MergeLoSemanticMachineInvariant lt call machine)
    (hfuel : MergeLoFuelInvariant (fuel + 1) machine)
    (hna : 1 < machine.na) (hnb : 0 < machine.nb)
    (ih : ∀ (next : MergeLoMachine (Occurrence alpha) nu)
      (phase : MergeLoPhase),
      MergeLoSemanticMachineInvariant lt call next →
      MergeLoFuelInvariant fuel next → 1 < next.na → 0 < next.nb →
      ∃ result, MergeLoLoopCorrectPost lt call
        (mergeLoLoop? fuel next phase) result) :
    ∃ result, MergeLoLoopCorrectPost lt call
      (mergeLoLoop? (fuel + 1) machine .galloping) result := by
  have hguard : ¬ (machine.na ≤ 1 ∨ machine.nb = 0) := by omega
  let minGallop :=
    if (1 : PySSize).slt machine.minGallop then machine.minGallop - 1
    else machine.minGallop
  let adjusted : MergeLoMachine (Occurrence alpha) nu :=
    { machine with
      state := { machine.state with min_gallop := minGallop }
      minGallop := minGallop }
  have hadjusted : MergeLoSemanticMachineInvariant lt call adjusted :=
    h.setMinGallop minGallop
  have hadjustedNa : adjusted.na = machine.na := rfl
  have hadjustedNb : adjusted.nb = machine.nb := rfl
  rcases SortSlice.read_eq_some_of_indexInBounds adjusted.state.data
      adjusted.bPos (hadjusted.safety.bPosInBounds (by omega)) with
    ⟨firstB, hfirstB⟩
  have hinitialized : MergeLoTempRangeInitialized adjusted.state.a
      adjusted.aPos adjusted.na := by
    intro offset hoffset
    rcases hadjusted.safety.tempActiveValuesMode offset hoffset with
      ⟨entry, hread, _hmode⟩
    refine ⟨entry, ?_⟩
    rw [erase_mergeTempRead] at hread
    have hsum : Int.ofNat adjusted.aPos + Int.ofNat offset =
        Int.ofNat (adjusted.aPos + offset) := by
      simp only [Int.ofNat_eq_natCast, Nat.cast_add]
    rw [hsum, mergeTempRead_ofNat] at hread
    exact hread
  rcases mergeLoTempRun_exists_of_initialized adjusted.state.a adjusted.aPos
      adjusted.na hinitialized with ⟨activeA, hactiveA⟩
  rcases hadjusted.gallopRight_exists horder hsemantic firstB activeA hactiveA with
    ⟨gallopA, hgallopA, hgallopAFuel, hpartitionA⟩
  let aCount := gallopA.index
  have haCountLt : aCount < adjusted.na :=
    hadjusted.gallopRightIndex_lt hgeometry horder hsemantic (by omega)
      firstB hfirstB activeA hactiveA aCount hpartitionA
  have haNotGreater : ¬ adjusted.na < aCount := by omega
  rcases mergeLoCopyABlock_total hgeometry hadjusted aCount haCountLt
      (by omega) firstB hfirstB activeA hactiveA hpartitionA with
    ⟨copiedA, hcopyA, hafterA⟩
  let afterA : MergeLoMachine (Occurrence alpha) nu :=
    { adjusted with
      state := copiedA
      dest := adjusted.dest + Int.ofNat aCount
      aPos := adjusted.aPos + aCount
      na := adjusted.na - aCount }
  have hafterA' : MergeLoSemanticMachineInvariant lt call afterA := hafterA
  let afterACall := fun (copiedCount : Nat)
      (current : MergeLoMachine (Occurrence alpha) nu) =>
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
              let data ← mergeDataMemmove? .loGallopB moved.state.data
                moved.dest moved.bPos bCount
              let moved : MergeLoMachine (Occurrence alpha) nu :=
                { moved with
                  state := { moved.state with data := data }
                  dest := moved.dest + Int.ofNat bCount
                  bPos := moved.bPos + Int.ofNat bCount
                  nb := moved.nb - bCount }
              if moved.nb = 0 then
                mergeLoSucceed? moved
              else
                let moved ← mergeLoCopyAIncr? moved
                if moved.na = 1 then
                  mergeLoCopyB? moved
                else if MIN_GALLOP.toNat ≤ copiedCount ∨
                    MIN_GALLOP.toNat ≤ bCount then
                  mergeLoLoop? fuel moved .galloping
                else
                  let threshold := moved.minGallop + 1
                  let state := { moved.state with min_gallop := threshold }
                  mergeLoLoop? fuel
                    { moved with state := state, minGallop := threshold }
                    (.ordinary 0 0)
  have hgallopAExpanded := hgallopA
  dsimp only [adjusted, minGallop] at hgallopAExpanded
  have hcopyAExpanded := hcopyA
  dsimp only [adjusted, minGallop] at hcopyAExpanded
  have hfirstBExecution :
      machine.state.data.read? machine.bPos = some firstB := by
    simpa only [adjusted] using hfirstB
  have hactiveAExecution :
      mergeLoTempRun? machine.state.a machine.aPos machine.na = some activeA := by
    simpa only [adjusted] using hactiveA
  have haNotGreaterExecution : ¬ machine.na < gallopA.index := by
    simpa only [adjusted, aCount] using haNotGreater
  have hcopyAExecution :
      mergeLoMemcpyTempToData? .gallopTempToData rfl gallopA.index
        { machine.state with min_gallop := minGallop }
        machine.dest machine.aPos = some copiedA := by
    simpa only [adjusted, aCount] using hcopyA
  have hexecutionAfterA :
      mergeLoLoop? (fuel + 1) machine .galloping =
        afterACall aCount afterA := by
    rw [mergeLoLoop?]
    rw [mergeLoGallopRound_equation]
    simp only [hguard, if_false, hfirstBExecution, hactiveAExecution,
      bind, Option.bind]
    rw [hgallopAExpanded]
    simp only [mergeLoBindOptionAcross, hgallopAFuel, Bool.false_eq_true,
      if_false, haNotGreaterExecution]
    rw [hcopyAExecution]
    change afterACall aCount afterA = afterACall aCount afterA
    rfl
  by_cases hafterAZero : afterA.na = 0
  · have : 0 < afterA.na := hafterA'.leftPositive
    omega
  by_cases hafterAOne : afterA.na = 1
  · rcases mergeLoCopyBTail_correct_total hgeometry horder hsemantic hafterA'
      hafterAOne (by simpa only [afterA, adjusted] using hnb) with
      ⟨result, hresult, hrc, hrfuel, hout⟩
    refine ⟨result, ?_⟩
    refine
      { resultEq := ?_
        returnCode := hrc
        resultFuel := hrfuel
        semantic := hout }
    rw [hexecutionAfterA]
    simp [afterACall, hafterAOne, hresult]
  have hafterAMore : 1 < afterA.na := by
    have := hafterA'.leftPositive
    omega
  have hafterANb : 0 < afterA.nb := by
    simpa only [afterA, adjusted] using hnb
  rcases hafterA'.safety.tempReadable (by omega) with
    ⟨firstA, hfirstASigned⟩
  have hfirstA : mergeLoTempRead? afterA.state.a afterA.aPos = some firstA := by
    simpa only [mergeTempRead_ofNat] using hfirstASigned
  rcases SortSlice.read_eq_some_of_indexInBounds afterA.state.data afterA.bPos
      (hafterA'.safety.bPosInBounds hafterANb) with ⟨currentB, hcurrentB⟩
  have hcurrentBEq : currentB = firstB := by
    have hnew := hafterA'.mainActive.2 0 hafterANb
    have hold := hadjusted.mainActive.2 0 (by omega)
    have hnewPos : adjusted.bPos + Int.ofNat 0 = afterA.bPos := by
      dsimp only [afterA]
      norm_num
    have holdPos : adjusted.bPos + Int.ofNat 0 = adjusted.bPos := by norm_num
    rw [hnewPos] at hnew
    rw [holdPos] at hold
    have hpositions : afterA.bPos = adjusted.bPos := rfl
    have hcounts : call.nb - afterA.nb = call.nb - adjusted.nb := rfl
    rw [hpositions, hcounts, hcurrentB] at hnew
    rw [hfirstB] at hold
    exact Option.some.inj (hnew.trans hold.symm)
  have hboundaryA := hpartitionA.2.2 aCount (by rfl) haCountLt
  rcases hboundaryA with ⟨boundaryA, hboundaryARead, hboundaryACompare⟩
  have hagreesA := tempRun_agreesWithSlice_of_eq_some adjusted.state.a
    adjusted.aPos adjusted.na activeA hactiveA
  have hagreeA := hagreesA (Int.ofNat aCount) (Int.natCast_nonneg _)
    (Int.ofNat_lt.mpr haCountLt)
  have hsourceA :
      (GallopKeySource.temporary adjusted.state.a
        (Int.ofNat adjusted.aPos)).read? (Int.ofNat aCount) = some firstA := by
    change mergeTempRead? adjusted.state.a
      (Int.ofNat adjusted.aPos + Int.ofNat aCount) = some firstA
    have htempEq := mergeLoMemcpyTempToData_temp_eq_of_eq_some
      .gallopTempToData rfl aCount adjusted.state copiedA adjusted.dest
        adjusted.aPos hcopyA
    have hsum : Int.ofNat adjusted.aPos + Int.ofNat aCount =
        Int.ofNat (adjusted.aPos + aCount) := by
      simp only [Int.ofNat_eq_natCast, Nat.cast_add]
    rw [hsum, mergeTempRead_ofNat]
    have hfirstA' := hfirstA
    change mergeLoTempRead? copiedA.a (adjusted.aPos + aCount) =
      some firstA at hfirstA'
    rw [htempEq] at hfirstA'
    exact hfirstA'
  have hsliceA : activeA.read? (0 + Int.ofNat aCount) = some firstA :=
    hagreeA.symm.trans hsourceA
  have hboundaryAEq : boundaryA = firstA :=
    Option.some.inj (hboundaryARead.symm.trans hsliceA)
  subst boundaryA
  rw [hadjusted.comparator] at hboundaryACompare
  subst currentB
  rcases mergeLoCopyBIncr_total hafterA' (by omega) hafterANb with
    ⟨afterB, hcopyB, hafterBSafety⟩
  have hafterB := hafterA'.copyB hgeometry (by omega) hafterANb firstA firstB
    hfirstA hcurrentB hboundaryACompare hcopyB hafterBSafety
  rcases mergeLoCopyBIncr_spec_of_eq_some afterA afterB hcopyB with
    ⟨_hdestB, _haPosB, _hbPosB, hafterBNa, hafterBNb, _hcmpB, _htempB,
      _hreadB, _hframeB⟩
  by_cases hafterBZero : afterB.nb = 0
  · rcases mergeLoSucceed_correct_total hgeometry hafterB hafterBZero with
      ⟨result, hresult, hrc, hrfuel, hout⟩
    refine ⟨result, ?_⟩
    refine
      { resultEq := ?_
        returnCode := hrc
        resultFuel := hrfuel
        semantic := hout }
    rw [hexecutionAfterA]
    simp [afterACall, hafterAZero, hafterAOne, hcopyB, hafterBZero, hresult]
  have hafterBNbPositive : 0 < afterB.nb := by omega
  rcases hafterB.safety.tempReadable (by omega) with
    ⟨gallopFirstA, hgallopFirstASigned⟩
  have hgallopFirstA : mergeLoTempRead? afterB.state.a afterB.aPos =
      some gallopFirstA := by
    simpa only [mergeTempRead_ofNat] using hgallopFirstASigned
  have hgallopFirstAEq : gallopFirstA = firstA := by
    have hold := hafterA'.tempActive.2 0 (by omega)
    have hnew := hafterB.tempActive.2 0 (by omega)
    simp only [Nat.add_zero] at hold hnew
    rw [hfirstA] at hold
    rw [hgallopFirstA] at hnew
    rw [_haPosB] at hnew
    exact Option.some.inj (hnew.trans hold.symm)
  subst gallopFirstA
  rcases hafterB.gallopLeft_exists horder hsemantic hafterBNbPositive firstA with
    ⟨gallopB, hgallopB, hgallopBFuel, hpartitionB⟩
  let bCount := gallopB.index
  have hbCount : bCount ≤ afterB.nb := hpartitionB.1
  have hbNotGreater : ¬ afterB.nb < bCount := by omega
  rcases mergeLoCopyBBlock_total hgeometry hafterB bCount hbCount firstA
      hgallopFirstA hpartitionB with ⟨copiedB, hcopyBlockB, hafterC⟩
  have hcopyBlockBCore : afterB.state.data.memmove? afterB.dest afterB.bPos
      bCount = some copiedB := by
    simpa [mergeDataMemmove_eq] using hcopyBlockB
  let afterC : MergeLoMachine (Occurrence alpha) nu :=
    { afterB with
      state := { afterB.state with data := copiedB }
      dest := afterB.dest + Int.ofNat bCount
      bPos := afterB.bPos + Int.ofNat bCount
      nb := afterB.nb - bCount }
  have hafterC' : MergeLoSemanticMachineInvariant lt call afterC := hafterC
  by_cases hafterCZero : afterC.nb = 0
  · rcases mergeLoSucceed_correct_total hgeometry hafterC' hafterCZero with
      ⟨result, hresult, hrc, hrfuel, hout⟩
    have hsubZero : afterB.nb - bCount = 0 := by
      simpa only [afterC] using hafterCZero
    refine ⟨result, ?_⟩
    refine
      { resultEq := ?_
        returnCode := hrc
        resultFuel := hrfuel
        semantic := hout }
    rw [hexecutionAfterA]
    simp only [mergeLoBindOptionAcross, gt_iff_lt, mergeDataMemmove_eq,
      Int.ofNat_eq_natCast, BitVec.ofNat_eq_ofNat, Option.bind_eq_bind,
      hafterAZero, ↓reduceIte, hafterAOne, hcopyB, Option.bind_some,
      hafterBZero, hgallopFirstA, hgallopB, hgallopBFuel,
      Bool.false_eq_true, hbNotGreater, hcopyBlockBCore, hsubZero,
      afterACall, bCount]
    have hsubZeroG : afterB.nb - gallopB.index = 0 := by
      simpa only [bCount] using hsubZero
    rw [← hsubZeroG]
    change mergeLoSucceed? afterC = some result
    exact hresult
  have hafterCNb : 0 < afterC.nb := by omega
  rcases SortSlice.read_eq_some_of_indexInBounds afterC.state.data afterC.bPos
      (hafterC'.safety.bPosInBounds hafterCNb) with ⟨nextB, hnextB⟩
  have hbCountLt : bCount < afterB.nb := by
    dsimp only [afterC] at hafterCZero
    omega
  rcases hpartitionB.2.2 bCount (by rfl) hbCountLt with
    ⟨boundaryB, hboundaryBRead, hboundaryBCompare⟩
  have hbeforeB := hafterB.mainActive.2 bCount hbCountLt
  have hafterCHead := hafterC'.mainActive.2 0 hafterCNb
  have hconsumedC : call.nb - afterC.nb =
      (call.nb - afterB.nb) + bCount := by
    dsimp only [afterC]
    have := hafterB.rightCount
    omega
  have hheadPos : afterC.bPos + Int.ofNat 0 = afterC.bPos := by norm_num
  rw [hheadPos] at hafterCHead
  rw [hconsumedC] at hafterCHead
  simp only [Nat.add_zero] at hafterCHead
  rw [hboundaryBRead] at hbeforeB
  rw [hnextB] at hafterCHead
  have hnextBEq : nextB = boundaryB :=
    Option.some.inj (hafterCHead.trans hbeforeB.symm)
  subst nextB
  rw [hafterB.comparator] at hboundaryBCompare
  have hfirstAC : mergeLoTempRead? afterC.state.a afterC.aPos = some firstA := by
    simpa only [afterC] using hgallopFirstA
  have hafterCMore : 1 < afterC.na := by
    dsimp only [afterC]
    rw [hafterBNa]
    exact hafterAMore
  rcases mergeLoCopyAIncr_total hafterC' hafterC'.leftPositive with
    ⟨afterD, hcopyD, hafterDSafety⟩
  have hafterD := hafterC'.copyA hgeometry hafterCMore hafterCNb
    firstA boundaryB
    hfirstAC hnextB hboundaryBCompare hcopyD hafterDSafety
  rcases mergeLoCopyAIncr_spec_of_eq_some afterC afterD hcopyD with
    ⟨_hdestD, _haPosD, _hbPosD, hafterDNa, hafterDNb, _hcmpD, _htempD,
      _hreadD, _hframeD⟩
  have hcopyDExpanded :
      mergeLoCopyAIncr?
          { afterB with
            state := { afterB.state with data := copiedB }
            dest := afterB.dest + Int.ofNat gallopB.index
            bPos := afterB.bPos + Int.ofNat gallopB.index
            nb := afterB.nb - gallopB.index } = some afterD := by
    simpa only [afterC, bCount] using hcopyD
  dsimp only at hcopyDExpanded
  simp only [Int.ofNat_eq_natCast] at hcopyDExpanded
  have hafterDNbPositive : 0 < afterD.nb := by
    rw [hafterDNb]
    exact hafterCNb
  by_cases hafterDOne : afterD.na = 1
  · rcases mergeLoCopyBTail_correct_total hgeometry horder hsemantic hafterD
      hafterDOne hafterDNbPositive with ⟨result, hresult, hrc, hrfuel, hout⟩
    refine ⟨result, ?_⟩
    refine
      { resultEq := ?_
        returnCode := hrc
        resultFuel := hrfuel
        semantic := hout }
    rw [hexecutionAfterA]
    simp only [mergeLoBindOptionAcross, gt_iff_lt, mergeDataMemmove_eq,
      Int.ofNat_eq_natCast, BitVec.ofNat_eq_ofNat, Option.bind_eq_bind,
      hafterAZero, ↓reduceIte, hafterAOne, hcopyB, Option.bind_some,
      hafterBZero, hgallopFirstA, hgallopB, hgallopBFuel,
      Bool.false_eq_true, hbNotGreater, hcopyBlockBCore, hafterCZero,
      afterACall, afterC, bCount]
    rw [hcopyDExpanded]
    simp [hafterDOne, hresult]
  have hafterDMore : 1 < afterD.na := by
    have := hafterD.leftPositive
    omega
  have hafterDFuel : MergeLoFuelInvariant fuel afterD := by
    unfold MergeLoFuelInvariant at hfuel ⊢
    dsimp only [afterC, afterA, adjusted] at *
    omega
  by_cases hstay : MIN_GALLOP.toNat ≤ aCount ∨ MIN_GALLOP.toNat ≤ bCount
  · rcases ih afterD .galloping hafterD hafterDFuel hafterDMore
      hafterDNbPositive with
      ⟨result, hresult⟩
    refine ⟨result, ?_⟩
    refine
      { resultEq := ?_
        returnCode := hresult.returnCode
        resultFuel := hresult.resultFuel
        semantic := hresult.semantic }
    rw [hexecutionAfterA]
    simp only [mergeLoBindOptionAcross, gt_iff_lt, mergeDataMemmove_eq,
      Int.ofNat_eq_natCast, BitVec.ofNat_eq_ofNat, Option.bind_eq_bind,
      hafterAZero, ↓reduceIte, hafterAOne, hcopyB, Option.bind_some,
      hafterBZero, hgallopFirstA, hgallopB, hgallopBFuel,
      Bool.false_eq_true, hbNotGreater, hcopyBlockBCore, hafterCZero,
      afterACall, afterC, bCount]
    rw [hcopyDExpanded]
    simp only [Option.bind_some, hafterDOne, if_false]
    have hstayExpanded : MIN_GALLOP.toNat ≤ aCount ∨
        MIN_GALLOP.toNat ≤ gallopB.index := by
      simpa only [bCount] using hstay
    rw [if_pos hstayExpanded]
    exact hresult.resultEq
  · let threshold := afterD.minGallop + 1
    let adjustedD : MergeLoMachine (Occurrence alpha) nu :=
      { afterD with
        state := { afterD.state with min_gallop := threshold }
        minGallop := threshold }
    have hadjustedD := hafterD.setMinGallop threshold
    have hadjustedDFuel : MergeLoFuelInvariant fuel adjustedD := by
      unfold MergeLoFuelInvariant at hafterDFuel ⊢
      simpa only [adjustedD] using hafterDFuel
    rcases ih adjustedD (.ordinary 0 0) hadjustedD hadjustedDFuel (by
        simpa only [adjustedD] using hafterDMore) (by
        simpa only [adjustedD, hafterDNb] using hafterCNb) with
      ⟨result, hresult⟩
    refine ⟨result, ?_⟩
    refine
      { resultEq := ?_
        returnCode := hresult.returnCode
        resultFuel := hresult.resultFuel
        semantic := hresult.semantic }
    rw [hexecutionAfterA]
    simp only [mergeLoBindOptionAcross, gt_iff_lt, mergeDataMemmove_eq,
      Int.ofNat_eq_natCast, BitVec.ofNat_eq_ofNat, Option.bind_eq_bind,
      hafterAZero, ↓reduceIte, hafterAOne, hcopyB, Option.bind_some,
      hafterBZero, hgallopFirstA, hgallopB, hgallopBFuel,
      Bool.false_eq_true, hbNotGreater, hcopyBlockBCore, hafterCZero,
      afterACall, afterC, bCount]
    rw [hcopyDExpanded]
    simp only [Option.bind_some, hafterDOne, if_false]
    have hstayExpanded : ¬(MIN_GALLOP.toNat ≤ aCount ∨
        MIN_GALLOP.toNat ≤ gallopB.index) := by
      simpa only [bCount] using hstay
    rw [if_neg hstayExpanded]
    change mergeLoLoop? fuel adjustedD (.ordinary 0 0) = some result
    exact hresult.resultEq

/-- The raw forward driver terminates successfully with exact stable-merge
semantics whenever its arithmetic/storage and semantic invariants hold. -/
private theorem mergeLoLoop_correct
    {lt : BoolComparator alpha}
    {pre : MergeState (Occurrence alpha) nu} {scanned i : Nat}
    {call : MergeAtCall (Occurrence alpha) nu}
    (hgeometry : MergeAtSafetyGeometry pre scanned i call)
    (horder : BoolStrictWeakOrder lt)
    (hsemantic : MergeLoSemanticPre lt call)
    (fuel : Nat) (machine : MergeLoMachine (Occurrence alpha) nu)
    (phase : MergeLoPhase)
    (h : MergeLoSemanticMachineInvariant lt call machine)
    (hfuel : MergeLoFuelInvariant fuel machine)
    (hna : 1 < machine.na) (hnb : 0 < machine.nb) :
    ∃ result, MergeLoLoopCorrectPost lt call
      (mergeLoLoop? fuel machine phase) result := by
  induction fuel generalizing machine phase with
  | zero =>
      unfold MergeLoFuelInvariant at hfuel
      omega
  | succ fuel ih =>
      cases phase with
      | ordinary aCount bCount =>
          exact mergeLoOrdinary_correct_step hgeometry horder hsemantic fuel
            machine aCount bCount h hfuel hna hnb ih
      | galloping =>
          exact mergeLoGalloping_correct_step hgeometry horder hsemantic fuel
            machine h hfuel hna hnb ih

/-! ## Whole-entry correctness at the public raw and traced entries -/

private theorem mergeLo_semanticOutput_of_safety
    {lt : BoolComparator alpha}
    (horder : BoolStrictWeakOrder lt)
    (pre : MergeState (Occurrence alpha) nu) (scanned i : Nat)
    (call : MergeAtCall (Occurrence alpha) nu)
    (hlayout : PendingLayout pre scanned)
    (hmax : pre.listlen.toNat ≤ PY_LIST_MAX)
    (hprepare : prepareMergeAt? pre i = some (.mergeLo call))
    (hInv : TempStorageInv pre.a pre.alloced)
    (hLive : pre.a.Live)
    (hMode : SortSlice.ValuesModeInvariant pre.a.hasValues pre.data)
    (hcomparator : call.state.key_compare = occurrenceComparator lt)
    (hsemantic : MergeLoSemanticPre lt call)
    (result : MergeLoResult (Occurrence alpha) nu)
    (hsafety : MergeLoSafetyPost pre scanned i call
      (mergeLoTraced? call.state call.ssa call.ssb call.na call.nb) result) :
    MergeLoSemanticOutput lt call result.state := by
  rcases mergeLo_prepareInitial pre scanned i call hlayout hmax hprepare
      hInv hLive hMode with ⟨copied, stage⟩
  rcases mergeLoSemantic_afterForcedB stage hcomparator hsemantic with
    ⟨afterB, hforcedB, hafterB⟩
  have hentryGuard :
      0 < call.na ∧ 0 < call.nb ∧ call.na ≤ PY_SSIZE_T_MAX ∧
        call.nb ≤ PY_SSIZE_T_MAX ∧
        call.ssa + Int.ofNat call.na = call.ssb :=
    ⟨stage.geometry.leftPositive, stage.geometry.rightPositive,
      stage.geometry.leftWordBound, stage.geometry.rightWordBound,
      stage.geometry.adjacent⟩
  have hmainCopy : mainToTempMemcpy? call.na (mergeLoAllocated call).state
      0 call.ssa = some copied := by
    rw [← stage.copyPost.exactErasure]
    exact stage.copyPost.success
  have hinitialCopy :
      mergeLoMemcpyDataToTemp? .initialDataToTemp rfl call.na
        (mergeLoAllocated call).state 0 call.ssa = some copied := by
    exact (mainToTempMemcpy_eq_mergeLo .initialDataToTemp rfl call.na
      (mergeLoAllocated call).state 0 call.ssa).symm ▸ hmainCopy
  have hraw := hsafety.rawResultEq
  rw [mergeLo?, if_pos hentryGuard,
    if_neg stage.requestFacts.guardNotRejected] at hraw
  change (do
    let copiedState ← mergeLoMemcpyDataToTemp? .initialDataToTemp rfl call.na
      (mergeLoAllocated call).state 0 call.ssa
    let machine := mergeLoInitialMachine call copiedState
    let machine ← mergeLoCopyBIncr? machine
    if machine.nb = 0 then
      mergeLoSucceed? machine
    else if machine.na = 1 then
      mergeLoCopyB? machine
    else
      mergeLoLoop? (call.na + call.nb + 1) machine (.ordinary 0 0)) =
      some result at hraw
  rw [hinitialCopy] at hraw
  simp only [bind, Option.bind] at hraw
  rw [hforcedB] at hraw
  by_cases hnbZero : afterB.nb = 0
  · have hterminal : mergeLoSucceed? afterB = some result := by
      simpa only [hnbZero, if_pos] using hraw
    exact hafterB.succeed stage.geometry hnbZero hterminal
  have hnbPositive : 0 < afterB.nb := Nat.pos_of_ne_zero hnbZero
  by_cases hnaOne : afterB.na = 1
  · have hterminal : mergeLoCopyB? afterB = some result := by
      simp only [hnbZero, if_false, hnaOne, if_pos] at hraw
      exact hraw
    exact hafterB.copyBTail stage.geometry horder hsemantic hnaOne hnbPositive
      hterminal
  have hnaLarge : 1 < afterB.na := by
    have := hafterB.leftPositive
    omega
  have hfuel : MergeLoFuelInvariant (call.na + call.nb + 1) afterB := by
    unfold MergeLoFuelInvariant
    have hleft := hafterB.leftCount
    have hright := hafterB.rightCount
    omega
  have hloopActual :
      mergeLoLoop? (call.na + call.nb + 1) afterB (.ordinary 0 0) =
        some result := by
    simp only [hnbZero, if_false, hnaOne, if_false] at hraw
    exact hraw
  rcases mergeLoLoop_correct stage.geometry horder hsemantic
      (call.na + call.nb + 1) afterB (.ordinary 0 0) hafterB hfuel hnaLarge
      hnbPositive with ⟨loopResult, hloop⟩
  have heq : loopResult = result :=
    Option.some.inj (hloop.resultEq.symm.trans hloopActual)
  simpa only [heq] using hloop.semantic

/-- The untraced transcription succeeds and materializes the exact stable
whole-entry merge while framing every cell outside the merged range. -/
theorem mergeLo_raw_correct
    {lt : BoolComparator alpha}
    (horder : BoolStrictWeakOrder lt)
    (pre : MergeState (Occurrence alpha) nu) (scanned i : Nat)
    (call : MergeAtCall (Occurrence alpha) nu)
    (hlayout : PendingLayout pre scanned)
    (hmax : pre.listlen.toNat ≤ PY_LIST_MAX)
    (hprepare : prepareMergeAt? pre i = some (.mergeLo call))
    (hInv : TempStorageInv pre.a pre.alloced)
    (hLive : pre.a.Live)
    (hMode : SortSlice.ValuesModeInvariant pre.a.hasValues pre.data)
    (hcomparator : call.state.key_compare = occurrenceComparator lt)
    (hsemantic : MergeLoSemanticPre lt call) :
    ∃ result, MergeLoRawCorrectnessPost lt call result := by
  rcases mergeLo_safe pre scanned i call hlayout hmax hprepare hInv hLive hMode
    with ⟨result, hsafety⟩
  have hout := mergeLo_semanticOutput_of_safety horder pre scanned i
    call hlayout hmax hprepare hInv hLive hMode hcomparator hsemantic result
    hsafety
  exact ⟨result,
    { resultEq := hsafety.rawResultEq
      exactRange := hout.exactRange
      frame := hout.frame }⟩

/-- Full traced `merge_lo` functional correctness: exact whole-entry output,
sortedness, shared stability, whole-entry permutation, and external framing. -/
theorem mergeLo_correct
    {lt : BoolComparator alpha}
    (horder : BoolStrictWeakOrder lt)
    (canonical : List (Occurrence alpha))
    (pre : MergeState (Occurrence alpha) nu) (scanned i : Nat)
    (call : MergeAtCall (Occurrence alpha) nu)
    (hlayout : PendingLayout pre scanned)
    (hmax : pre.listlen.toNat ≤ PY_LIST_MAX)
    (hprepare : prepareMergeAt? pre i = some (.mergeLo call))
    (hInv : TempStorageInv pre.a pre.alloced)
    (hLive : pre.a.Live)
    (hMode : SortSlice.ValuesModeInvariant pre.a.hasValues pre.data)
    (hcomparator : call.state.key_compare = occurrenceComparator lt)
    (hstable : StableOccurrencePermutation lt canonical
      ((sortSliceRangeKeys call.state.data call.ssa.toNat call.na).toList ++
        (sortSliceRangeKeys call.state.data call.ssb.toNat call.nb).toList))
    (hsemantic : MergeLoSemanticPre lt call) :
    ∃ result, MergeLoCorrectnessPost lt canonical pre scanned i call result := by
  rcases mergeLo_safe pre scanned i call hlayout hmax hprepare hInv hLive hMode
    with ⟨result, hsafety⟩
  have hout := mergeLo_semanticOutput_of_safety horder pre scanned i
    call hlayout hmax hprepare hInv hLive hMode hcomparator hsemantic result
    hsafety
  exact ⟨result, mergeLoCorrectnessPost_of_exactRange horder canonical hsafety
    hsemantic hstable hout.exactRange hout.frame⟩

/-! ## Executable exact-target regressions -/

/-- The executable fixture's four temporary cells are genuinely covered by
its declared allocation; they are not phantom storage. -/
theorem mergeLoCorrectnessRegression_tempStorage :
    TempStorageInv mergeLoCorrectnessRegressionState.a
      mergeLoCorrectnessRegressionState.alloced := by
  exact mergeLoCorrectnessRegression_tempStorage_kernel

/-- The real raw evaluator resolves the equal `4` pair stably and preserves the
nonzero-base range's payload-bearing neighboring cells.  The exposed equality
does not identify which terminal branch produced that final state. -/
theorem mergeLo_exact_stable_range_and_frame_regression :
    (mergeLo? mergeLoCorrectnessRegressionState 1 3 2 3).map
        (fun result =>
          (result.returnCode, result.fuelExhausted,
            result.state.data.entries.toList)) =
      some
        (0, false,
          [mergeLoCorrectnessEntry 99 990,
           mergeLoCorrectnessEntry 2 20,
           mergeLoCorrectnessEntry 4 40,
           mergeLoCorrectnessEntry 4 41,
           mergeLoCorrectnessEntry 5 50,
           mergeLoCorrectnessEntry 6 60,
           mergeLoCorrectnessEntry 100 1000]) := by
  exact mergeLoCorrectnessRegression_kernel

/-- The min-gallop-one evaluator returns stable tie/payload output; this
equality observes final state, not gallop-branch entry. -/
theorem mergeLo_correctness_gallop_tie_regression :
    (mergeLo? mergeLoGallopStabilityRegressionState 0 3 3 3).map
        (fun result => (result.returnCode, result.fuelExhausted,
          result.state.min_gallop, result.state.data.entries.toList)) =
      some
        (0, false, 1,
          [{ key := 1, value := some 10 },
           { key := 2, value := some 20 },
           { key := 3, value := some 30 },
           { key := 3, value := some 31 },
           { key := 4, value := some 40 },
           { key := 5, value := some 50 }]) := by
  exact mergeLo_gallop_stability_regression

end CPythonListsort
