/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Code.Assembly.ListSortMergePolicy
import Code.Assembly.PowerSortPolicyCost

/-!
# Final-collapse policy cost for the real traced evaluator

This module connects the exact selector used by `merge_force_collapse` to the
pure `CPythonForceCollapseCost` relation.  It deliberately keeps CPython's
final-collapse schedule distinct from canonical repeated-top-pair completion.
-/

namespace CPythonListsort

universe u v

variable {κ : Type u} {ν : Type v}

/-- Pending-run lengths as mathematical naturals, in stack order. -/
def pendingRunLengths (state : MergeState κ ν) : List Nat :=
  state.pending.toList.map fun run => run.len.toNat

/-- A replay forest matching the pending stack has exactly its run lengths. -/
theorem PolicyForestMatches.openForestLengths_eq_pendingRunLengths
    {forest : List SpannedMergeTree} {state : MergeState κ ν}
    (hmatch : PolicyForestMatches forest state) :
    openForestLengths forest = pendingRunLengths state := by
  have hspans := congrArg (List.map RunSpan.len) hmatch
  simpa [openForestLengths, pendingRunLengths, Function.comp_def,
    RunSpan.ofPendingRun] using hspans

private theorem pendingRunRead_result_of_get?
    (state : MergeState κ ν) (i : Nat) (run : PendingRun)
    (hget : state.pending[i]? = some run) :
    (TraceResult.pendingRunRead? state (Int.ofNat i)).result = some run := by
  change (TraceResult.pendingRunRead? state (Int.ofNat i)).erase = some run
  rw [TraceResult.erase_pendingRunRead]
  have hnonnegative : 0 ≤ Int.ofNat i := Int.natCast_nonneg _
  rw [if_pos hnonnegative]
  simpa using hget

private theorem traceResult_bind_result_of_eq_some
    (current : TraceResult α) (next : α → TraceResult β) (value : α)
    (hresult : current.result = some value) :
    (current.bind next).result = (next value).result := by
  change (current.bind next).erase = (next value).erase
  rw [TraceResult.erase_bind]
  change current.result.bind (fun item => (next item).result) = _
  rw [hresult]
  rfl

/-- Exact source selector pin for stacks of depth at least three.

The final three pending runs are exposed as `a,b,c`.  The returned merge index
is the third-last pair exactly when `a.len < c.len` as naturals; ties and the
opposite strict inequality select the top pair. -/
theorem forceCollapseIndexTraced_exact_selector
    (state : MergeState κ ν) (scanned : Nat)
    (hlayout : PendingLayout state scanned)
    (hthree : 2 < state.pending.size) :
    ∃ before a b c,
      state.pending.toList = before ++ [a, b, c] ∧
      (forceCollapseIndexTraced? state).result =
        some (if a.len.toNat < c.len.toNat then
          before.length else before.length + 1) := by
  let runs := state.pending.toList
  have hrunsLength : runs.length = state.pending.size := by
    simp [runs]
  rcases List.eq_nil_or_concat' runs with hrunsEmpty |
      ⟨withoutC, c, hrunsC⟩
  · rw [hrunsEmpty] at hrunsLength
    simp at hrunsLength
    omega
  rcases List.eq_nil_or_concat' withoutC with hwithoutCEmpty |
      ⟨withoutBC, b, hrunsB⟩
  · rw [hwithoutCEmpty] at hrunsC
    have := congrArg List.length hrunsC
    simp [hrunsLength] at this
    omega
  rcases List.eq_nil_or_concat' withoutBC with hwithoutBCEmpty |
      ⟨before, a, hrunsA⟩
  · rw [hwithoutBCEmpty] at hrunsB
    rw [hrunsB] at hrunsC
    have := congrArg List.length hrunsC
    simp [hrunsLength] at this
    omega
  have hruns : state.pending.toList = before ++ [a, b, c] := by
    dsimp [runs] at hrunsC
    rw [hrunsA] at hrunsB
    rw [hrunsB] at hrunsC
    simpa [List.append_assoc] using hrunsC
  have hsize : state.pending.size = before.length + 3 := by
    have := congrArg List.length hruns
    simpa using this
  have haGet : state.pending[before.length]? = some a := by
    rw [← Array.getElem?_toList, hruns]
    simp
  have hcGet : state.pending[before.length + 2]? = some c := by
    rw [← Array.getElem?_toList, hruns]
    simp
  have haRead := pendingRunRead_result_of_get? state before.length a haGet
  have hcRead := pendingRunRead_result_of_get? state (before.length + 2) c hcGet
  have haMem : a ∈ state.pending.toList := by simp [hruns]
  have hcMem : c ∈ state.pending.toList := by simp [hruns]
  have haNonnegative :=
    (PendingRunsCover.member_spec hlayout.2.2.2 haMem).2.1
  have hcNonnegative :=
    (PendingRunsCover.member_spec hlayout.2.2.2 hcMem).2.1
  have hslt := pySSize_slt_eq_nat_lt a.len c.len
    haNonnegative hcNonnegative
  refine ⟨before, a, b, c, hruns, ?_⟩
  unfold forceCollapseIndexTraced?
  rw [if_pos (by omega : 1 < state.pending.size)]
  dsimp only
  rw [if_pos (by omega : 0 < state.pending.size - 2)]
  have hpreviousIndex : state.pending.size - 2 - 1 = before.length := by omega
  have hfollowingIndex : state.pending.size - 2 + 1 =
      before.length + 2 := by omega
  rw [hpreviousIndex, hfollowingIndex]
  rw [traceResult_bind_result_of_eq_some _ _ a haRead]
  change Option.map _ _ = _
  rw [hcRead]
  simp [hslt, hsize]

private theorem pendingRunLengths_collapse_small
    (state : MergeState κ ν) (hsmall : state.pending.size ≤ 1) :
    CPythonForceCollapseCost (pendingRunLengths state) 0 := by
  have hlength : state.pending.toList.length ≤ 1 := by
    simpa using hsmall
  cases hpending : state.pending.toList with
  | nil =>
      simpa [pendingRunLengths, hpending] using
        CPythonForceCollapseCost.empty
  | cons run rest =>
      cases rest with
      | nil =>
          simpa [pendingRunLengths, hpending] using
            CPythonForceCollapseCost.singleton run.len.toNat
      | cons next tail =>
          simp [hpending] at hlength

private theorem mergeForceCollapseLoop_logicalCost_small
    (fuel : Nat) (state : MergeState κ ν)
    (hsmall : state.pending.size ≤ 1) :
    PolicyEvent.logicalMergeCost
      (mergeForceCollapseLoopTraced? fuel state).trace.policyEvents = 0 := by
  cases fuel with
  | zero =>
      simp [mergeForceCollapseLoopTraced?, hsmall, TraceResult.pure,
        AccessTrace.empty]
  | succ fuel =>
      have hnotMany : ¬1 < state.pending.size := by omega
      simp [mergeForceCollapseLoopTraced?, hnotMany, TraceResult.pure,
        AccessTrace.empty]

private theorem bitVec_add_toNat_of_pairFits
    {state : MergeState κ ν} {scanned : Nat}
    {before after : List PendingRun} {left right : PendingRun}
    (hlayout : PendingLayout state scanned)
    (hsplit : state.pending.toList =
      before ++ left :: right :: after) :
    (left.len + right.len).toNat =
      left.len.toNat + right.len.toNat := by
  have hfit := hlayout.pairFits hsplit
  have hfit64 : left.len.toNat + right.len.toNat < 2 ^ 64 := by
    norm_num at hfit ⊢
    omega
  exact BitVec.toNat_add_of_lt hfit64

private theorem mergeForceCollapseLoop_cost
    (fuel : Nat) (state : MergeState κ ν) (scanned : Nat)
    (result : MergeForceCollapseResult κ ν)
    (hresult :
      (mergeForceCollapseLoopTraced? fuel state).result = some result)
    (hcode : result.returnCode = 0)
    (hresultFuel : result.fuelExhausted = false)
    (hmax : state.listlen.toNat ≤ PY_LIST_MAX)
    (hlayout : PendingLayout state scanned)
    (hInv : TempStorageInv state.a state.alloced)
    (hLive : state.a.Live)
    (hMode : SortSlice.ValuesModeInvariant state.a.hasValues state.data) :
    CPythonForceCollapseCost (pendingRunLengths state)
      (PolicyEvent.logicalMergeCost
        (mergeForceCollapseLoopTraced? fuel state).trace.policyEvents) := by
  induction fuel generalizing state result with
  | zero =>
      by_cases hsmall : state.pending.size ≤ 1
      · rw [mergeForceCollapseLoop_logicalCost_small 0 state hsmall]
        exact pendingRunLengths_collapse_small state hsmall
      · have hresult' := hresult
        rw [mergeForceCollapseLoopTraced?, if_neg hsmall] at hresult'
        injection hresult' with hresultEq
        subst result
        change true = false at hresultFuel
        contradiction
  | succ remaining ih =>
      by_cases hmany : 1 < state.pending.size
      · rcases forceCollapseIndexTraced_safe state hmany with
          ⟨i, hindex, _hindexSafe, _hindexErase, hposition⟩
        rcases mergeAt_safe state scanned i hlayout hmax hposition
            hInv hLive hMode with ⟨merged, hmerged⟩
        have hsuccess : merged.returnCode = 0 ∧ !merged.fuelExhausted :=
          ⟨hmerged.returnCode, by simp [hmerged.resultFuel]⟩
        have hresult' := hresult
        rw [mergeForceCollapseLoopTraced?, if_pos hmany,
          traceResult_bind_result_of_eq_some _ _ i hindex,
          traceResult_bind_result_of_eq_some _ _ merged hmerged.resultEq,
          if_pos hsuccess] at hresult'
        have hmergedMax : merged.state.listlen.toNat ≤ PY_LIST_MAX := by
          rw [hmerged.stableFrame.listlen]
          exact hmax
        have htail := ih merged.state result hresult' hcode hresultFuel
          hmergedMax hmerged.pendingLayout hmerged.tempInvariant
          hmerged.tempLive hmerged.valuesMode
        have hevents :
            (mergeForceCollapseLoopTraced? (remaining + 1)
              state).trace.policyEvents =
              (mergeAtTraced? state i).trace.policyEvents ++
                (mergeForceCollapseLoopTraced? remaining
                  merged.state).trace.policyEvents := by
          rw [mergeForceCollapseLoopTraced?, if_pos hmany,
            TraceResult.policyEvents_bind, hindex]
          simp only [forceCollapseIndexTraced_policyEvents_eq_nil,
            List.nil_append]
          rw [TraceResult.policyEvents_bind, hmerged.resultEq]
          simp only
          rw [if_pos hsuccess]
        rcases hmerged.logicalMerge with
          ⟨left, right, hleft, hright, hpending, hmergeEvents⟩
        have hcost :
            PolicyEvent.logicalMergeCost
                (mergeForceCollapseLoopTraced? (remaining + 1)
                  state).trace.policyEvents =
              left.len.toNat + right.len.toNat +
                PolicyEvent.logicalMergeCost
                  (mergeForceCollapseLoopTraced? remaining
                    merged.state).trace.policyEvents := by
          rw [hevents, PolicyEvent.logicalMergeCost_append, hmergeEvents]
          simp [RunSpan.ofPendingRun]
        by_cases hthree : 2 < state.pending.size
        · rcases forceCollapseIndexTraced_exact_selector state scanned
              hlayout hthree with ⟨before, a, b, c, hruns, hselector⟩
          have hi : i =
              (if a.len.toNat < c.len.toNat then
                before.length else before.length + 1) :=
            Option.some.inj (hindex.symm.trans hselector)
          by_cases hselect : a.len.toNat < c.len.toNat
          · simp only [if_pos hselect] at hi
            have haGet : state.pending[i]? = some a := by
              rw [hi, ← Array.getElem?_toList, hruns]
              simp
            have hbGet : state.pending[i + 1]? = some b := by
              rw [hi, ← Array.getElem?_toList, hruns]
              simp
            have hleftEq : left = a :=
              Option.some.inj (hleft.symm.trans haGet)
            have hrightEq : right = b :=
              Option.some.inj (hright.symm.trans hbGet)
            subst left
            subst right
            have hsum := bitVec_add_toNat_of_pairFits hlayout
              (before := before) (after := [c]) hruns
            have hsplice := Array.toList_set_eraseIdx_adjacent
              (xs := state.pending) (i := i) (before := before)
              (after := [c]) (left := a) (right := b)
              (replacement := ({ a with len := a.len + b.len } : PendingRun))
              hruns (by omega)
            have hmergedRuns : merged.state.pending.toList =
                before ++
                  [({ a with len := a.len + b.len } : PendingRun), c] := by
              calc
                merged.state.pending.toList =
                    ((state.pending.setIfInBounds i
                      { a with len := a.len + b.len }).eraseIdxIfInBounds
                        (i + 1)).toList := congrArg Array.toList hpending
                _ = before ++
                    ({ a with len := a.len + b.len } : PendingRun) :: [c] :=
                      hsplice
            have htailLengths :
                pendingRunLengths merged.state =
                  before.map (fun run => run.len.toNat) ++
                    [a.len.toNat + b.len.toNat, c.len.toNat] := by
              simp [pendingRunLengths, hmergedRuns, hsum]
            rw [htailLengths] at htail
            rw [hcost]
            have hheadLengths : pendingRunLengths state =
                before.map (fun run => run.len.toNat) ++
                  [a.len.toNat, b.len.toNat, c.len.toNat] := by
              simp [pendingRunLengths, hruns]
            rw [hheadLengths]
            exact CPythonForceCollapseCost.mergeThirdLast
              (before.map fun run => run.len.toNat) a.len.toNat b.len.toNat
              c.len.toNat _ hselect htail
          · simp only [if_neg hselect] at hi
            have hbGet : state.pending[i]? = some b := by
              rw [hi, ← Array.getElem?_toList, hruns]
              simp
            have hcGet : state.pending[i + 1]? = some c := by
              have hindexEq : i + 1 = before.length + 2 := by omega
              rw [hindexEq, ← Array.getElem?_toList, hruns]
              simp
            have hleftEq : left = b :=
              Option.some.inj (hleft.symm.trans hbGet)
            have hrightEq : right = c :=
              Option.some.inj (hright.symm.trans hcGet)
            subst left
            subst right
            have htopSplit : state.pending.toList =
                (before ++ [a]) ++ b :: c :: [] := by
              simpa [List.append_assoc] using hruns
            have hsum := bitVec_add_toNat_of_pairFits hlayout htopSplit
            have hsplice := Array.toList_set_eraseIdx_adjacent
              (xs := state.pending) (i := i) (before := before ++ [a])
              (after := []) (left := b) (right := c)
              (replacement := ({ b with len := b.len + c.len } : PendingRun))
              htopSplit (by simp [hi])
            have hmergedRuns : merged.state.pending.toList =
                before ++
                  [a, ({ b with len := b.len + c.len } : PendingRun)] := by
              calc
                merged.state.pending.toList =
                    ((state.pending.setIfInBounds i
                      { b with len := b.len + c.len }).eraseIdxIfInBounds
                        (i + 1)).toList := congrArg Array.toList hpending
                _ = (before ++ [a]) ++
                    [({ b with len := b.len + c.len } : PendingRun)] := hsplice
                _ = before ++
                    [a, ({ b with len := b.len + c.len } : PendingRun)] := by
                      simp [List.append_assoc]
            have htailLengths :
                pendingRunLengths merged.state =
                  before.map (fun run => run.len.toNat) ++
                    [a.len.toNat, b.len.toNat + c.len.toNat] := by
              simp [pendingRunLengths, hmergedRuns, hsum]
            rw [htailLengths] at htail
            rw [hcost]
            have hheadLengths : pendingRunLengths state =
                before.map (fun run => run.len.toNat) ++
                  [a.len.toNat, b.len.toNat, c.len.toNat] := by
              simp [pendingRunLengths, hruns]
            rw [hheadLengths]
            exact CPythonForceCollapseCost.mergeTop
              (before.map fun run => run.len.toNat) a.len.toNat b.len.toNat
              c.len.toNat _ hselect htail
        · have hsize : state.pending.size = 2 := by omega
          have hi : i = 0 := by
            rcases hposition with htop | hlower <;> omega
          have hsplit := Array.exists_pair_split_of_getElem?_eq_some
            hleft hright
          rcases hsplit with ⟨before, after, hbeforeLength, hruns⟩
          have hbefore : before = [] := by
            apply List.eq_nil_of_length_eq_zero
            omega
          subst before
          have hafter : after = [] := by
            apply List.eq_nil_of_length_eq_zero
            have hpendingLength : state.pending.toList.length = 2 := by
              simpa using hsize
            rw [hruns] at hpendingLength
            simp only [List.nil_append, List.length_cons] at hpendingLength
            omega
          subst after
          have hsum := bitVec_add_toNat_of_pairFits hlayout hruns
          have hsplice := Array.toList_set_eraseIdx_adjacent
            (xs := state.pending) (i := i) (before := []) (after := [])
            (left := left) (right := right)
            (replacement :=
              ({ left with len := left.len + right.len } : PendingRun))
            hruns (by simp [hi])
          have hmergedRuns : merged.state.pending.toList =
              [({ left with len := left.len + right.len } : PendingRun)] := by
            calc
              merged.state.pending.toList =
                  ((state.pending.setIfInBounds i
                    { left with len := left.len + right.len }).eraseIdxIfInBounds
                      (i + 1)).toList := congrArg Array.toList hpending
              _ = [({ left with len := left.len + right.len } : PendingRun)] :=
                hsplice
          have htailLengths : pendingRunLengths merged.state =
              [left.len.toNat + right.len.toNat] := by
            simp [pendingRunLengths, hmergedRuns, hsum]
          rw [htailLengths] at htail
          have htailCost :
              PolicyEvent.logicalMergeCost
                (mergeForceCollapseLoopTraced? remaining
                  merged.state).trace.policyEvents = 0 := by
            exact htail.singleton_cost_eq_zero
          rw [hcost, htailCost]
          have hheadLengths : pendingRunLengths state =
              [left.len.toNat, right.len.toNat] := by
            simp [pendingRunLengths, hruns]
          rw [hheadLengths]
          exact CPythonForceCollapseCost.pair _ _
      · have hsmall : state.pending.size ≤ 1 := by omega
        rw [mergeForceCollapseLoop_logicalCost_small (remaining + 1)
          state hsmall]
        exact pendingRunLengths_collapse_small state hsmall

/-- The successful real final-collapse evaluator follows exactly the
source-level `CPythonForceCollapseCost` relation, including its strict
third-last-versus-top selector. -/
theorem mergeForceCollapse_cpythonForceCollapseCost
    (state : MergeState κ ν) (scanned : Nat)
    (result : MergeForceCollapseResult κ ν)
    (hmax : state.listlen.toNat ≤ PY_LIST_MAX)
    (hlayout : PendingLayout state scanned)
    (hInv : TempStorageInv state.a state.alloced)
    (hLive : state.a.Live)
    (hMode : SortSlice.ValuesModeInvariant state.a.hasValues state.data)
    (hsafety : MergeForceCollapseSafetyPost state scanned result) :
    CPythonForceCollapseCost (pendingRunLengths state)
      (PolicyEvent.logicalMergeCost
        (mergeForceCollapseTraced? state).trace.policyEvents) := by
  unfold mergeForceCollapseTraced?
  exact mergeForceCollapseLoop_cost state.pending.size state scanned result
    (by simpa [mergeForceCollapseTraced?] using hsafety.resultEq)
    hsafety.returnCode hsafety.resultFuel hmax hlayout hInv hLive hMode

/-- Final top-level bridge for the real collapse segment.

The checked event replay ends in a forest matching the machine's singleton
pending stack, while the very same event stream's logical merge cost obeys
the exact CPython final-collapse relation on the incoming open lengths. -/
theorem mergeForceCollapse_policyReplay_and_cost
    (input : RunSpan) (forest : List SpannedMergeTree)
    (state : MergeState κ ν) (scanned : Nat)
    (result : MergeForceCollapseResult κ ν)
    (hmatch : PolicyForestMatches forest state)
    (hmax : state.listlen.toNat ≤ PY_LIST_MAX)
    (hlayout : PendingLayout state scanned)
    (hInv : TempStorageInv state.a state.alloced)
    (hLive : state.a.Live)
    (hMode : SortSlice.ValuesModeInvariant state.a.hasValues state.data)
    (hsafety : MergeForceCollapseSafetyPost state scanned result) :
    ∃ nextForest root,
      replayPolicyEventsFrom? input forest
          (mergeForceCollapseTraced? state).trace.policyEvents =
        some nextForest ∧
      nextForest = [root] ∧
      PolicyForestMatches nextForest result.state ∧
      CPythonForceCollapseCost (openForestLengths forest)
        (PolicyEvent.logicalMergeCost
          (mergeForceCollapseTraced? state).trace.policyEvents) := by
  rcases mergeForceCollapse_policyReplay input forest state scanned result
      hmatch hmax hlayout hInv hLive hMode hsafety with
    ⟨nextForest, hreplay, hnextMatch⟩
  rcases hsafety.singleton with ⟨run, hpending⟩
  have hlength : nextForest.length = 1 := by
    rw [hnextMatch.length_eq]
    have := congrArg List.length hpending
    simpa using this
  rcases List.length_eq_one_iff.mp hlength with ⟨root, hforest⟩
  have hcost := mergeForceCollapse_cpythonForceCollapseCost state scanned
    result hmax hlayout hInv hLive hMode hsafety
  rw [← hmatch.openForestLengths_eq_pendingRunLengths] at hcost
  exact ⟨nextForest, root, hreplay, hforest, hnextMatch, hcost⟩

end CPythonListsort
