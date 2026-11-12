/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Code.Transcription.Binarysort
import Code.Transcription.CountRun
import Code.Transcription.FoundNewRun
import Code.Transcription.MergeForceCollapse
import Code.Transcription.MergeInitStorage
import Code.Transcription.MergeMemory
import Code.Transcription.ReverseSlice

/-!
# Snapshot-model `list_sort_impl`

This module assembles the version-one snapshot model of CPython's top-level
sort.  Keys and their optional payloads are already paired, the comparator is
pure and total, and allocator failure is excluded.  Within that boundary the
control flow retains initial/final reverse handling, natural-run discovery,
adaptive minrun extension, policy merges, the unconditional pending push,
final collapse, and temporary-storage cleanup.
-/

namespace CPythonListsort

universe u v

variable {κ : Type u} {ν : Type v}

/-- Observable result of the snapshot-model top-level transcription. -/
structure ListSortImplResult (κ : Type u) (ν : Type v) where
  state : MergeState κ ν
  returnCode : Int
  fuelExhausted : Bool

/-- The source pending-run write, modeled as an unconditional operation on an
unbounded Lean array.  In particular, a 64-entry input becomes 65 entries;
the later policy theorem proves that valid top-level executions never reach
that artificial input. -/
def pushPendingRun (state : MergeState κ ν) (run : PendingRun) :
    MergeState κ ν :=
  { state with pending := state.pending.push run }

/-- Copy the adaptive-minrun projection back into the full merge state. -/
def installMinrunState (state : MergeState κ ν)
    (minrun : MinrunState) : MergeState κ ν :=
  { state with
    listlen := minrun.listlen
    mr_current := minrun.mr_current
    mr_e := minrun.mr_e
    mr_mask := minrun.mr_mask }

/-- Construct the two projections initialized by CPython's `merge_init`.

This constructor is public so assembly-level boundary theorems can connect a
validated top-level input to the representation invariants required by the
merge primitives. -/
def initialMergeState (lt : BoolComparator κ) (hasKeyfunc : Bool)
    (input : SortSlice κ ν) : MergeState κ ν × Bool :=
  let listlen : PySSize := BitVec.ofNat 64 input.entries.size
  let minrun := minrunInitTraced listlen
  let temp := mergeInitTemp (κ := κ) (ν := ν) listlen hasKeyfunc
  ({ min_gallop := MIN_GALLOP
     listlen := minrun.state.listlen
     basekeys := 0
     data := input
     a := temp.storage
     alloced := temp.alloced
     pending := #[]
     key_compare := lt
     mr_current := minrun.state.mr_current
     mr_e := minrun.state.mr_e
     mr_mask := minrun.state.mr_mask },
   minrun.stopped)

@[simp]
theorem initialMergeState_data (lt : BoolComparator κ) (hasKeyfunc : Bool)
    (input : SortSlice κ ν) :
    (initialMergeState lt hasKeyfunc input).1.data = input := by
  simp [initialMergeState]

@[simp]
theorem initialMergeState_temp_hasValues (lt : BoolComparator κ)
    (hasKeyfunc : Bool) (input : SortSlice κ ν) :
    (initialMergeState lt hasKeyfunc input).1.a.hasValues = hasKeyfunc := by
  simp [initialMergeState, mergeInitTemp]

/-- Common `succeed`/`fail` cleanup: apply CPython's final reverse to the
snapshot result when requested, then release owned temporary storage. -/
def finishListSort? (state : MergeState κ ν) (reverse : Bool)
    (inputSize : Nat) (returnCode : Int) (fuelExhausted : Bool) :
    Option (ListSortImplResult κ ν) := do
  let finished ←
    if reverse && decide (1 < inputSize) then
      match sortsliceReverse? state.data 0 inputSize with
      | none => none
      | some reversed =>
          some
            ({ state with data := reversed.slice }, reversed.fuelExhausted)
    else
      some (state, false)
  let state := finished.1
  let reverseFuel := finished.2
  pure
    { state := mergeFreemem state
      returnCode := returnCode
      fuelExhausted := fuelExhausted || reverseFuel }

def failFromFoundNewRun? (result : FoundNewRunResult κ ν)
    (reverse : Bool) (inputSize : Nat) : Option (ListSortImplResult κ ν) :=
  finishListSort? result.state reverse inputSize result.returnCode
    result.fuelExhausted

def failFromCollapse? (result : MergeForceCollapseResult κ ν)
    (reverse : Bool) (inputSize : Nat) : Option (ListSortImplResult κ ν) :=
  finishListSort? result.state reverse inputSize result.returnCode
    result.fuelExhausted

/-- The run-discovery loop.  `lo` and `remaining` replace CPython's moving
`sortslice` pointer and signed counter.  Each successful iteration consumes a
positive run, so `inputSize` units of explicit fuel are sufficient. -/
def listSortScan? :
    Nat → MergeState κ ν → Nat → Nat → Bool → Nat →
      Option (ListSortImplResult κ ν)
  | 0, state, _, remaining, reverse, inputSize =>
      if remaining = 0 then
        match mergeForceCollapse? state with
        | none => none
        | some collapsed =>
            if collapsed.returnCode = 0 ∧ !collapsed.fuelExhausted then
              finishListSort? collapsed.state reverse inputSize 0 false
            else
              failFromCollapse? collapsed reverse inputSize
      else
        finishListSort? state reverse inputSize (-1) true
  | fuel + 1, state, lo, remaining, reverse, inputSize =>
      if remaining = 0 then
        match mergeForceCollapse? state with
        | none => none
        | some collapsed =>
            if collapsed.returnCode = 0 ∧ !collapsed.fuelExhausted then
              finishListSort? collapsed.state reverse inputSize 0 false
            else
              failFromCollapse? collapsed reverse inputSize
      else do
        let counted ← countRun? state state.data (Int.ofNat lo) remaining
        let state := { state with data := counted.slice }
        if counted.fuelExhausted then
          finishListSort? state reverse inputSize (-1) true
        else if counted.length = 0 ∨ remaining < counted.length then
          none
        else
          let nextMinrun := minrunNext state.minrunState
          let state := installMinrunState state nextMinrun.state
          let runLength := counted.length
          let target := nextMinrun.result.toNat
          let force := if remaining ≤ target then remaining else target
          let extended ←
            if (BitVec.ofNat 64 runLength : PySSize).slt nextMinrun.result then
              match binarysort? state state.data (Int.ofNat lo) force runLength with
              | none => none
              | some sorted =>
                  some (sorted.slice, force, sorted.fuelExhausted)
            else
              some (state.data, runLength, false)
          let state := { state with data := extended.1 }
          let runLength := extended.2.1
          let extensionFuel := extended.2.2
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
                  -- Deliberately total and unconditional: capacity is proved
                  -- later from the policy invariant, not checked here.
                  let state := pushPendingRun found.state newRun
                  listSortScan? fuel state (lo + runLength)
                    (remaining - runLength) reverse inputSize
                else
                  failFromFoundNewRun? found reverse inputSize

/-- Snapshot-model transcription of CPython's `list_sort_impl`.

The input-size guard is the selected platform's list-allocation bound.  A
pending run is always installed with `Array.push`; this definition contains no
`MAX_MERGE_PENDING` test and no modeled debug-assertion failure.  `none`
denotes an invalid modeled access or assertion-domain input, while bounded-loop
exhaustion is returned explicitly. -/
def listSortImpl? (lt : BoolComparator κ) (reverse hasKeyfunc : Bool)
    (input : SortSlice κ ν) : Option (ListSortImplResult κ ν) :=
  if input.entries.size ≤ PY_LIST_MAX then
    let initialized := initialMergeState lt hasKeyfunc input
    let state := initialized.1
    if !initialized.2 then
      finishListSort? state reverse input.entries.size (-1) true
    else if input.entries.size < 2 then
      finishListSort? state reverse input.entries.size 0 false
    else if reverse then
      match sortsliceReverse? state.data 0 input.entries.size with
      | none => none
      | some reversed =>
          let state := { state with data := reversed.slice }
          if reversed.fuelExhausted then
            finishListSort? state reverse input.entries.size (-1) true
          else
            listSortScan? input.entries.size state 0 input.entries.size reverse
              input.entries.size
    else
      listSortScan? input.entries.size state 0 input.entries.size reverse
        input.entries.size
  else
    none

@[simp]
theorem pushPendingRun_size (state : MergeState κ ν) (run : PendingRun) :
    (pushPendingRun state run).pending.size = state.pending.size + 1 := by
  simp [pushPendingRun]

/-- Regression for the non-vacuous stack-capacity model: the operation does
not refuse, clamp, or report an assertion event at the C array's capacity. -/
theorem pushPendingRun_at_capacity (state : MergeState κ ν) (run : PendingRun)
    (hDepth : state.pending.size = MAX_MERGE_PENDING) :
    (pushPendingRun state run).pending.size = MAX_MERGE_PENDING + 1 := by
  simp [hDepth]

private def listSortExample : SortSlice Nat Nat :=
  { entries :=
      #[{ key := 3, value := some 30 },
        { key := 1, value := some 10 },
        { key := 2, value := some 20 },
        { key := 2, value := some 21 }] }

set_option linter.style.nativeDecide false in
/-- Small executable regression for run extension, stable forward order, and
the final temporary-storage cleanup. -/
example :
    (listSortImpl? (fun left right : Nat => decide (left < right))
      false true listSortExample).map
        (fun result =>
          (result.returnCode, result.fuelExhausted, result.state.a.backing,
            result.state.data.entries.toList)) =
      some
        (0, false, .inline,
          [{ key := 1, value := some 10 },
           { key := 2, value := some 20 },
           { key := 2, value := some 21 },
           { key := 3, value := some 30 }]) := by
  decide

set_option linter.style.nativeDecide false in
/-- CPython's reverse-before/stable-sort/reverse-after pattern keeps equal-key
payloads in their original order while reversing the requested key order. -/
example :
    (listSortImpl? (fun left right : Nat => decide (left < right))
      true true listSortExample).map
        (fun result =>
          (result.returnCode, result.fuelExhausted,
            result.state.data.entries.toList)) =
      some
        (0, false,
          [{ key := 3, value := some 30 },
           { key := 2, value := some 20 },
           { key := 2, value := some 21 },
           { key := 1, value := some 10 }]) := by
  decide

end CPythonListsort
