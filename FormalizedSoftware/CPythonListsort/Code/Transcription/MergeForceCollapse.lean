/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Code.Transcription.MergeAt

/-!
# Final pending-stack collapse

This module transcribes `merge_force_collapse`: until one pending run remains,
choose one of the top two adjacent merge positions using the neighboring run
lengths and call `merge_at`.
-/

namespace CPythonListsort

universe u v

variable {κ : Type u} {ν : Type v}

/-- Observable result of `merge_force_collapse`. -/
structure MergeForceCollapseResult (κ : Type u) (ν : Type v) where
  state : MergeState κ ν
  returnCode : Int
  fuelExhausted : Bool

private def mergeForceCollapseSuccess (state : MergeState κ ν) :
    MergeForceCollapseResult κ ν :=
  { state := state, returnCode := 0, fuelExhausted := false }

private def mergeForceCollapseOutOfFuel (state : MergeState κ ν) :
    MergeForceCollapseResult κ ν :=
  { state := state, returnCode := -1, fuelExhausted := true }

private def fromMergeAt (result : MergeAtResult κ ν) :
    MergeForceCollapseResult κ ν :=
  { state := result.state
    returnCode := result.returnCode
    fuelExhausted := result.fuelExhausted }

/-- Choose CPython's merge position.  The comparison is the source's strict
signed comparison; equality keeps the initial top-pair position.

This helper is exported so preservation and traced-safety proofs can follow
the exact source branch without duplicating the neighboring-length test. -/
def forceCollapseIndex? (state : MergeState κ ν) : Option Nat := do
  if 1 < state.pending.size then
    let i := state.pending.size - 2
    if 0 < i then
      let previous ← state.pending[i - 1]?
      let following ← state.pending[i + 1]?
      if previous.len.slt following.len then
        some (i - 1)
      else
        some i
    else
      some i
  else
    none

/-- Fuel-bounded transcription of the final-collapse loop.

This recursive helper is exported so policy and safety proofs can induct over
the actual transcribed control flow while keeping fuel exhaustion observable. -/
def mergeForceCollapseLoop? :
    Nat → MergeState κ ν → Option (MergeForceCollapseResult κ ν)
  | 0, state =>
      if state.pending.size ≤ 1 then
        some (mergeForceCollapseSuccess state)
      else
        some (mergeForceCollapseOutOfFuel state)
  | fuel + 1, state =>
      if 1 < state.pending.size then
        match forceCollapseIndex? state with
        | none => none
        | some i =>
            match mergeAt? state i with
            | none => none
            | some merged =>
                if merged.returnCode = 0 ∧ !merged.fuelExhausted then
                  mergeForceCollapseLoop? fuel merged.state
                else
                  some (fromMergeAt merged)
      else
        some (mergeForceCollapseSuccess state)

/-- Transcription of CPython's `merge_force_collapse`.  Empty and singleton
artificial states are total no-op successes, just as the release-mode C loop;
the top-level assembly separately establishes that a completed nontrivial sort
has exactly one run. -/
def mergeForceCollapse? (state : MergeState κ ν) :
    Option (MergeForceCollapseResult κ ν) :=
  mergeForceCollapseLoop? state.pending.size state

private def forceCollapseTieExampleState : MergeState Nat Nat :=
  { min_gallop := MIN_GALLOP
    listlen := 3
    basekeys := 0
    data := { entries := #[] }
    a := { cells := #[], backing := .inline, hasValues := false }
    alloced := 0
    pending :=
      #[{ base := 0, len := 1, power := some 1 },
        { base := 1, len := 1, power := some 2 },
        { base := 2, len := 1, power := none }]
    key_compare := fun left right => decide (left < right)
    mr_current := 0
    mr_e := 0
    mr_mask := 0 }

set_option linter.style.nativeDecide false in
/-- The neighboring-length test is strict: a tie keeps `n = size - 2` and
therefore chooses the top pair rather than the lower pair. -/
example : forceCollapseIndex? forceCollapseTieExampleState = some 1 := by
  decide

end CPythonListsort
