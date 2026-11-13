/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Code.Transcription.MergeHi
import Code.Transcription.MergeLo

/-!
# Pending-stack merge dispatch

This module transcribes CPython's `merge_at`.  The pending-stack replacement
happens before either galloping search, exactly as it does in C, so a later
modeled failure retains that mutation.  The two searches trim entries already
in their final positions and the shorter remaining run selects `merge_lo` or
`merge_hi`.
-/

namespace CPythonListsort

universe u v w x

variable {κ : Type u} {ν : Type v}

private def bindOptionAcross {α : Type w} {β : Type x}
    (value : Option α) (next : α → Option β) : Option β :=
  match value with
  | none => none
  | some value => next value

/-- Public reduction equation used by traced assembly proofs without exposing
the private sequencing helper as part of the model's callable API. -/
@[simp]
theorem mergeAt_bindOptionAcross_none {α : Type w} {β : Type x}
    (next : α → Option β) :
    bindOptionAcross none next = none := rfl

/-- Public reduction equation for the successful sequencing branch. -/
@[simp]
theorem mergeAt_bindOptionAcross_some {α : Type w} {β : Type x}
    (value : α) (next : α → Option β) :
    bindOptionAcross (some value) next = next value := rfl

/-- Observable result of `merge_at`.  Fuel exhaustion comes only from a
bounded nested gallop or merge transcription and is kept separate from the C
return code. -/
structure MergeAtResult (κ : Type u) (ν : Type v) where
  state : MergeState κ ν
  returnCode : Int
  fuelExhausted : Bool

private def mergeAtSuccess (state : MergeState κ ν) : MergeAtResult κ ν :=
  { state := state, returnCode := 0, fuelExhausted := false }

private def mergeAtOutOfFuel (state : MergeState κ ν) : MergeAtResult κ ν :=
  { state := state, returnCode := -1, fuelExhausted := true }

private def fromMergeLo (result : MergeLoResult κ ν) : MergeAtResult κ ν :=
  { state := result.state
    returnCode := result.returnCode
    fuelExhausted := result.fuelExhausted }

private def fromMergeHi (result : MergeHiResult κ ν) : MergeAtResult κ ν :=
  { state := result.state
    returnCode := result.returnCode
    fuelExhausted := result.fuelExhausted }

/-- Public constructor equation for a successful early `merge_at` return. -/
@[simp]
theorem mergeAtSuccess_eq (state : MergeState κ ν) :
    mergeAtSuccess state =
      { state := state, returnCode := 0, fuelExhausted := false } := rfl

/-- Public constructor equation for the modeled gallop-fuel failure return. -/
@[simp]
theorem mergeAtOutOfFuel_eq (state : MergeState κ ν) :
    mergeAtOutOfFuel state =
      { state := state, returnCode := -1, fuelExhausted := true } := rfl

/-- Public constructor equation for the `merge_lo` continuation result. -/
@[simp]
theorem fromMergeLo_eq (result : MergeLoResult κ ν) :
    fromMergeLo result =
      { state := result.state
        returnCode := result.returnCode
        fuelExhausted := result.fuelExhausted } := rfl

/-- Public constructor equation for the `merge_hi` continuation result. -/
@[simp]
theorem fromMergeHi_eq (result : MergeHiResult κ ν) :
    fromMergeHi result =
      { state := result.state
        returnCode := result.returnCode
        fuelExhausted := result.fuelExhausted } := rfl

/-- Replace pending runs `i` and `i+1` by their combined run.  Erasing the
second run also performs CPython's explicit slide when `i` is third-last. -/
private def combinePendingAt (state : MergeState κ ν) (i : Nat)
    (left right : PendingRun) : MergeState κ ν :=
  let combined := { left with len := left.len + right.len }
  let pending := (state.pending.setIfInBounds i combined).eraseIdxIfInBounds (i + 1)
  { state with pending := pending }

/-- Public reduction equation for the pending splice, used to prove exact
erasure of the independently instrumented physical read/write sequence. -/
@[simp]
theorem combinePendingAt_eq (state : MergeState κ ν) (i : Nat)
    (left right : PendingRun) :
    combinePendingAt state i left right =
      { state with
        pending :=
          (state.pending.setIfInBounds i
            { left with len := left.len + right.len }).eraseIdxIfInBounds
              (i + 1) } := rfl

/-- The exact source values retained at a post-trimming merge call site.  The
original selected runs and both gallop results are intentionally retained so
assembly proofs can connect trimming monotonicity to the gallop safety
theorems rather than to the defensive checks in `prepareMergeAt?`. -/
structure MergeAtCall (κ : Type u) (ν : Type v) where
  state : MergeState κ ν
  ssa : Int
  ssb : Int
  na : Nat
  nb : Nat
  left : PendingRun
  right : PendingRun
  firstB : SortSliceEntry κ ν
  lastA : SortSliceEntry κ ν
  trimA : GallopResult
  trimB : GallopResult

/-- The observable continuation selected after `merge_at` has updated the
pending stack and completed both trimming gallops.  Keeping the two merge
continuations explicit makes the exact state and request at the subsequent
`merge_getmem` call available to assembly proofs. -/
inductive MergeAtPreparation (κ : Type u) (ν : Type v) where
  | finished (result : MergeAtResult κ ν)
  | mergeLo (call : MergeAtCall κ ν)
  | mergeHi (call : MergeAtCall κ ν)

/-- State at the end of the trimming segment (or at its early return). -/
def MergeAtPreparation.state : MergeAtPreparation κ ν → MergeState κ ν
  | .finished result => result.state
  | .mergeLo call | .mergeHi call => call.state

/-- Execute the continuation selected by `prepareMergeAt?`. -/
def finishMergeAtPreparation? :
    MergeAtPreparation κ ν → Option (MergeAtResult κ ν)
  | .finished result => some result
  | .mergeLo call =>
      match mergeLo? call.state call.ssa call.ssb call.na call.nb with
      | none => none
      | some result => some (fromMergeLo result)
  | .mergeHi call =>
      match mergeHi? call.state call.ssa call.ssb call.na call.nb with
      | none => none
      | some result => some (fromMergeHi result)

/-- The stack-update, two gallop trims, and shorter-run dispatch prefix of
`merge_at`.  A successful `.mergeLo` or `.mergeHi` result is exactly the state
and argument tuple used by the corresponding merge routine, whose first step
is the modeled `merge_getmem` call. -/
def prepareMergeAt? (state : MergeState κ ν) (i : Nat) :
    Option (MergeAtPreparation κ ν) :=
  if 2 ≤ state.pending.size ∧
      (i + 2 = state.pending.size ∨ i + 3 = state.pending.size) then
    bindOptionAcross state.pending[i]? fun left =>
      bindOptionAcross state.pending[i + 1]? fun right =>
        if (0 : PySSize).slt left.len ∧ (0 : PySSize).slt right.len ∧
            left.base + left.len.toNat = right.base then
          let na₀ := left.len.toNat
          let nb₀ := right.len.toNat
          let call := combinePendingAt state i left right
          match call.data.read? (Int.ofNat right.base) with
          | none => none
          | some firstB =>
              bindOptionAcross
                  (gallopRight? call call.data (Int.ofNat left.base)
                    firstB.key na₀ 0) fun trimA =>
                if trimA.fuelExhausted then
                  some (.finished (mergeAtOutOfFuel call))
                else if na₀ < trimA.index then
                  none
                else
                  let ssa := left.base + trimA.index
                  let na := na₀ - trimA.index
                  if na = 0 then
                    some (.finished (mergeAtSuccess call))
                  else
                    match call.data.read? (Int.ofNat (ssa + na - 1)) with
                    | none => none
                    | some lastA =>
                        bindOptionAcross
                            (gallopLeft? call call.data (Int.ofNat right.base)
                              lastA.key nb₀ (nb₀ - 1)) fun trimB =>
                          if trimB.fuelExhausted then
                            some (.finished (mergeAtOutOfFuel call))
                          else if nb₀ < trimB.index then
                            none
                          else
                            let nb := trimB.index
                            if nb = 0 then
                              some (.finished (mergeAtSuccess call))
                            else if na ≤ nb then
                              some (.mergeLo
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
                              some (.mergeHi
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
          none
  else
    none

/-- Transcription of CPython's `merge_at`.

`none` denotes an input outside the source assertion domain or a failed
modeled array access.  In particular, the function accepts exactly one of the
top two legal merge positions.  Once those checks pass, the stack is updated
before trimming, as in the source. -/
def mergeAt? (state : MergeState κ ν) (i : Nat) : Option (MergeAtResult κ ν) :=
  bindOptionAcross (prepareMergeAt? state i) finishMergeAtPreparation?

private theorem combinePendingAt_layoutFrame (state : MergeState κ ν) (i : Nat)
    (left right : PendingRun) :
    let combined := { left with len := left.len + right.len }
    let combinedState := combinePendingAt state i left right
    combinedState.listlen = state.listlen ∧
      combinedState.basekeys = state.basekeys ∧
      combinedState.data.entries.size = state.data.entries.size ∧
      combinedState.a.hasValues = state.a.hasValues ∧
      combinedState.alloced = state.alloced ∧
      combinedState.pending =
        (state.pending.setIfInBounds i combined).eraseIdxIfInBounds (i + 1) := by
  simp [combinePendingAt]

attribute [aesop safe forward] mergeLo_layout_frame_of_eq_some
  mergeHi_layoutFrame_of_eq_some

/-- Facts exported from the actual `merge_at` preparation path for a
subsequent `merge_getmem` call.  In particular, the guard-relevant state frame
is proved from the transcribed control flow, while the two trimming facts are
kept separately rather than replacing them with an assumed sum bound. -/
structure MergeAtCallsiteEvidence (pre : MergeState κ ν) (i : Nat)
    (call : MergeAtCall κ ν) : Prop where
  leftSelected : pre.pending[i]? = some call.left
  rightSelected : pre.pending[i + 1]? = some call.right
  ssa_eq :
    call.ssa = Int.ofNat (call.left.base + call.trimA.index)
  ssb_eq : call.ssb = Int.ofNat call.right.base
  listlen_eq : call.state.listlen = pre.listlen
  basekeys_eq : call.state.basekeys = pre.basekeys
  data_eq : call.state.data = pre.data
  dataSize_eq : call.state.data.entries.size = pre.data.entries.size
  storage_eq : call.state.a = pre.a
  hasValues_eq : call.state.a.hasValues = pre.a.hasValues
  alloced_eq : call.state.alloced = pre.alloced
  pending_eq :
    call.state.pending =
      (pre.pending.setIfInBounds i
        { call.left with len := call.left.len + call.right.len }).eraseIdxIfInBounds
          (i + 1)
  firstBRead :
    call.state.data.read? (Int.ofNat call.right.base) = some call.firstB
  rightGallop :
    gallopRight? call.state call.state.data (Int.ofNat call.left.base)
      call.firstB.key call.left.len.toNat 0 = some call.trimA
  leftRemainder : call.na = call.left.len.toNat - call.trimA.index
  lastARead :
    call.state.data.read?
      (Int.ofNat (call.left.base + call.trimA.index + call.na - 1)) =
        some call.lastA
  leftGallop :
    gallopLeft? call.state call.state.data (Int.ofNat call.right.base)
      call.lastA.key call.right.len.toNat (call.right.len.toNat - 1) =
        some call.trimB
  rightRemainder : call.nb = call.trimB.index
  leftPositive : 0 < call.na
  rightPositive : 0 < call.nb

set_option linter.flexible false in
set_option maxHeartbeats 5000000 in
-- The proof follows every nested option, early-return, and dispatch branch.
set_option maxRecDepth 10000 in
/-- A real `merge_lo` continuation exported by `prepareMergeAt?` carries the
exact pre-call frame, monotone gallop trimming, and the source branch test. -/
theorem prepareMergeAt_lo_callsite_of_eq_some
    (pre : MergeState κ ν) (i : Nat) (call : MergeAtCall κ ν)
    (h : prepareMergeAt? pre i = some (.mergeLo call)) :
    MergeAtCallsiteEvidence pre i call ∧ call.na ≤ call.nb := by
  simp only [prepareMergeAt?, bindOptionAcross] at h
  split at h <;> try simp at h
  all_goals try split at h <;> try simp at h
  all_goals try split at h <;> try simp at h
  all_goals try split at h <;> try simp at h
  all_goals try split at h <;> try simp at h
  all_goals try split at h <;> try simp at h
  all_goals try split at h <;> try simp at h
  all_goals try split at h <;> try simp at h
  all_goals try split at h <;> try simp at h
  all_goals try split at h <;> try simp at h
  all_goals try split at h <;> try simp at h
  all_goals try split at h <;> try simp at h
  all_goals try cases h
  all_goals
    aesop (config := {
      enableSimp := true, maxRuleApplications := 200,
      warnOnNonterminal := false })
  all_goals constructor <;> simp_all
  all_goals omega

set_option linter.flexible false in
set_option maxHeartbeats 5000000 in
-- The proof follows every nested option, early-return, and dispatch branch.
set_option maxRecDepth 10000 in
/-- A real `merge_hi` continuation exports the same control-flow facts and
the strict complementary shorter-run test. -/
theorem prepareMergeAt_hi_callsite_of_eq_some
    (pre : MergeState κ ν) (i : Nat) (call : MergeAtCall κ ν)
    (h : prepareMergeAt? pre i = some (.mergeHi call)) :
    MergeAtCallsiteEvidence pre i call ∧ call.nb < call.na := by
  simp only [prepareMergeAt?, bindOptionAcross] at h
  split at h <;> try simp at h
  all_goals try split at h <;> try simp at h
  all_goals try split at h <;> try simp at h
  all_goals try split at h <;> try simp at h
  all_goals try split at h <;> try simp at h
  all_goals try split at h <;> try simp at h
  all_goals try split at h <;> try simp at h
  all_goals try split at h <;> try simp at h
  all_goals try split at h <;> try simp at h
  all_goals try split at h <;> try simp at h
  all_goals try split at h <;> try simp at h
  all_goals try split at h <;> try simp at h
  all_goals try cases h
  all_goals
    aesop (config := {
      enableSimp := true, maxRuleApplications := 200,
      warnOnNonterminal := false })
  all_goals try omega
  all_goals constructor <;> simp_all
  all_goals omega

set_option linter.flexible false in
set_option maxHeartbeats 5000000 in
-- The generic frame proof follows all successful preparation branches.
set_option maxRecDepth 10000 in
private theorem prepareMergeAt_frame_of_eq_some
    (state : MergeState κ ν) (i : Nat) (prepared : MergeAtPreparation κ ν)
    (h : prepareMergeAt? state i = some prepared) :
    ∃ left right,
      state.pending[i]? = some left ∧
      state.pending[i + 1]? = some right ∧
      prepared.state.listlen = state.listlen ∧
      prepared.state.basekeys = state.basekeys ∧
      prepared.state.data.entries.size = state.data.entries.size ∧
      prepared.state.pending =
        (state.pending.setIfInBounds i
          { left with len := left.len + right.len }).eraseIdxIfInBounds (i + 1) := by
  simp only [prepareMergeAt?, bindOptionAcross] at h
  split at h <;> try simp at h
  all_goals try split at h <;> try simp at h
  all_goals try split at h <;> try simp at h
  all_goals try split at h <;> try simp at h
  all_goals try split at h <;> try simp at h
  all_goals try split at h <;> try simp at h
  all_goals try split at h <;> try simp at h
  all_goals try split at h <;> try simp at h
  all_goals try split at h <;> try simp at h
  all_goals try split at h <;> try simp at h
  all_goals try split at h <;> try simp at h
  all_goals try split at h <;> try simp at h
  all_goals try cases h
  all_goals
    aesop (config := {
      enableSimp := false, maxRuleApplications := 100,
      warnOnNonterminal := false })

set_option linter.flexible false in
private theorem finishMergeAtPreparation_layoutFrame
    (prepared : MergeAtPreparation κ ν) (result : MergeAtResult κ ν)
    (h : finishMergeAtPreparation? prepared = some result) :
    result.state.listlen = prepared.state.listlen ∧
      result.state.basekeys = prepared.state.basekeys ∧
      result.state.data.entries.size = prepared.state.data.entries.size ∧
      result.state.pending = prepared.state.pending := by
  cases prepared with
  | finished preparedResult =>
      have hresult : preparedResult = result := by
        simpa [finishMergeAtPreparation?] using Option.some.inj h
      subst result
      simp [MergeAtPreparation.state]
  | mergeLo call =>
      simp only [finishMergeAtPreparation?] at h
      split at h <;> try simp at h
      rename_i mergeResult hmerge
      rw [← h]
      simpa [fromMergeLo, MergeAtPreparation.state] using
        mergeLo_layout_frame_of_eq_some call.state call.ssa call.ssb call.na
          call.nb mergeResult hmerge
  | mergeHi call =>
      simp only [finishMergeAtPreparation?] at h
      split at h <;> try simp at h
      rename_i mergeResult hmerge
      rw [← h]
      simpa [fromMergeHi, MergeAtPreparation.state] using
        mergeHi_layoutFrame_of_eq_some call.state call.ssa call.ssb call.na
          call.nb mergeResult hmerge

set_option maxHeartbeats 5000000 in
-- The proof follows every nested trim and merge-result branch of `mergeAt?`.
/-- Every defined `merge_at` result exposes the two source-selected adjacent
runs and retains the exact eager stack mutation, even when a later gallop or
merge reports failure. The remaining `PendingLayout` fields are framed across
the data movement. -/
theorem mergeAt_pending_frame_of_eq_some
    (state : MergeState κ ν) (i : Nat) (result : MergeAtResult κ ν)
    (h : mergeAt? state i = some result) :
    ∃ left right,
      state.pending[i]? = some left ∧
      state.pending[i + 1]? = some right ∧
      result.state.listlen = state.listlen ∧
      result.state.basekeys = state.basekeys ∧
      result.state.data.entries.size = state.data.entries.size ∧
      result.state.pending =
        (state.pending.setIfInBounds i
          { left with len := left.len + right.len }).eraseIdxIfInBounds (i + 1) := by
  unfold mergeAt? at h
  cases hprepare : prepareMergeAt? state i with
  | none => simp [bindOptionAcross, hprepare] at h
  | some prepared =>
      have hfinish : finishMergeAtPreparation? prepared = some result := by
        simpa [bindOptionAcross, hprepare] using h
      rcases prepareMergeAt_frame_of_eq_some state i prepared hprepare with
        ⟨left, right, hleft, hright, hlistlen, hbasekeys, hdataSize,
          hpending⟩
      rcases finishMergeAtPreparation_layoutFrame prepared result hfinish with
        ⟨hresultListlen, hresultBasekeys, hresultDataSize, hresultPending⟩
      exact
        ⟨left, right, hleft, hright, hresultListlen.trans hlistlen,
          hresultBasekeys.trans hbasekeys, hresultDataSize.trans hdataSize,
          hresultPending.trans hpending⟩

private def mergeAtSlideExampleState : MergeState Nat Nat :=
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
      #[{ base := 0, len := 1, power := some 4 },
        { base := 1, len := 1, power := some 7 },
        { base := 2, len := 1, power := none }]
    key_compare := fun left right => decide (left < right)
    mr_current := 0
    mr_e := 0
    mr_mask := 0 }

set_option linter.style.nativeDecide false in
/-- When `i` is third-last, the unrelated final run slides left.  This input
also pins that trimming all of A returns only after the pending-stack update
and that the combined run retains the old left run's power. -/
theorem mergeAt_slide_regression :
    (mergeAt? mergeAtSlideExampleState 0).map
        (fun result =>
          (result.returnCode, result.fuelExhausted,
            result.state.pending.toList)) =
      some
        (0, false,
          [{ base := 0, len := 2, power := some 4 },
           { base := 2, len := 1, power := none }]) := by
  native_decide

private def mergeAtPreparationShape (prepared : MergeAtPreparation Nat Nat) :
    Option (Bool × Nat × Nat) :=
  match prepared with
  | .finished _ => none
  | .mergeLo call => some (true, call.na, call.nb)
  | .mergeHi call => some (false, call.na, call.nb)

private def mergeAtLoPreparationExampleState : MergeState Nat Nat :=
  { min_gallop := MIN_GALLOP
    listlen := 5
    basekeys := 0
    data :=
      { entries :=
          #[{ key := 2, value := none },
            { key := 4, value := none },
            { key := 1, value := none },
            { key := 3, value := none },
            { key := 5, value := none }] }
    a := { cells := #[], backing := .inline, hasValues := false }
    alloced := 0
    pending :=
      #[{ base := 0, len := 2, power := some 4 },
        { base := 2, len := 3, power := none }]
    key_compare := fun left right => decide (left < right)
    mr_current := 0
    mr_e := 0
    mr_mask := 0 }

private def mergeAtHiPreparationExampleState : MergeState Nat Nat :=
  { min_gallop := MIN_GALLOP
    listlen := 6
    basekeys := 0
    data :=
      { entries :=
          #[{ key := 1, value := none },
            { key := 3, value := none },
            { key := 5, value := none },
            { key := 7, value := none },
            { key := 2, value := none },
            { key := 6, value := none }] }
    a := { cells := #[], backing := .inline, hasValues := false }
    alloced := 0
    pending :=
      #[{ base := 0, len := 4, power := some 4 },
        { base := 4, len := 2, power := none }]
    key_compare := fun left right => decide (left < right)
    mr_current := 0
    mr_e := 0
    mr_mask := 0 }

set_option linter.style.nativeDecide false in
/-- Concrete regression: the exposed preparation path can reach the
`merge_lo` call site with nonempty post-trim runs. -/
example :
    (prepareMergeAt? mergeAtLoPreparationExampleState 0).bind
      mergeAtPreparationShape = some (true, 2, 2) := by
  decide

set_option linter.style.nativeDecide false in
/-- Concrete regression: the exposed preparation path can also reach the
strict complementary `merge_hi` call site. -/
example :
    (prepareMergeAt? mergeAtHiPreparationExampleState 0).bind
      mergeAtPreparationShape = some (false, 3, 2) := by
  decide

end CPythonListsort
