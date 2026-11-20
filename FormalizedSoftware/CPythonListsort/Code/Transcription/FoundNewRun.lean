/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Code.Transcription.MergeAt
import Code.Transcription.Powerloop

/-!
# PowerSort policy step for a newly found run

`found_new_run` computes the node power separating the current top pending
run from the newly discovered run, collapses strictly larger powers, and then
stores the new power on the surviving top run.  The caller remains responsible
for pushing the new run.
-/

namespace CPythonListsort

universe u v

variable {κ : Type u} {ν : Type v}

/-- Observable result of `found_new_run`. -/
structure FoundNewRunResult (κ : Type u) (ν : Type v) where
  state : MergeState κ ν
  returnCode : Int
  fuelExhausted : Bool

private def foundNewRunSuccess (state : MergeState κ ν) :
    FoundNewRunResult κ ν :=
  { state := state, returnCode := 0, fuelExhausted := false }

private def foundNewRunOutOfFuel (state : MergeState κ ν) :
    FoundNewRunResult κ ν :=
  { state := state, returnCode := -1, fuelExhausted := true }

private def fromMergeAt (result : MergeAtResult κ ν) :
    FoundNewRunResult κ ν :=
  { state := result.state
    returnCode := result.returnCode
    fuelExhausted := result.fuelExhausted }

/-- Public constructor equation for the ordinary successful return.  Assembly
proofs use this equation without exposing the private constructor helper as a
callable part of the transcription. -/
@[simp]
theorem foundNewRunSuccess_eq (state : MergeState κ ν) :
    foundNewRunSuccess state =
      { state := state, returnCode := 0, fuelExhausted := false } := rfl

/-- Public constructor equation for explicit bounded-loop exhaustion. -/
@[simp]
theorem foundNewRunOutOfFuel_eq (state : MergeState κ ν) :
    foundNewRunOutOfFuel state =
      { state := state, returnCode := -1, fuelExhausted := true } := rfl

/-- Public constructor equation for a delegated `merge_at` return. -/
@[simp]
theorem foundNewRunFromMergeAt_eq (result : MergeAtResult κ ν) :
    fromMergeAt result =
      { state := result.state
        returnCode := result.returnCode
        fuelExhausted := result.fuelExhausted } := rfl

/-- Store `power` on the current top run.

This helper is exported so policy proofs can state the exact postcondition of
the source operation without duplicating its array update. -/
def setTopPower? (state : MergeState κ ν) (power : Nat) :
    Option (MergeState κ ν) :=
  if state.pending.isEmpty then
    none
  else
    let i := state.pending.size - 1
    match state.pending[i]? with
    | none => none
    | some top =>
        some
          { state with
            pending := state.pending.setIfInBounds i
              ({ top with power := some power } : PendingRun) }

/-- Repeatedly merge the top pair while the preceding run's stored power is
strictly greater than the newly computed power.

This recursive helper is exported so the policy-preservation proof can follow
the transcribed loop and its fuel/result branches directly. -/
def foundNewRunLoop? :
    Nat → MergeState κ ν → Nat → Option (FoundNewRunResult κ ν)
  | 0, state, _ => some (foundNewRunOutOfFuel state)
  | fuel + 1, state, power =>
      if 1 < state.pending.size then
        match state.pending[state.pending.size - 2]? with
        | none => none
        | some preceding =>
            match preceding.power with
            | none => none
            | some precedingPower =>
                if power < precedingPower then
                  match mergeAt? state (state.pending.size - 2) with
                  | none => none
                  | some merged =>
                      if merged.returnCode = 0 ∧ !merged.fuelExhausted then
                        foundNewRunLoop? fuel merged.state power
                      else
                        some (fromMergeAt merged)
                else
                  match setTopPower? state power with
                  | none => none
                  | some state => some (foundNewRunSuccess state)
      else
        match setTopPower? state power with
        | none => none
        | some state => some (foundNewRunSuccess state)

/-- Transcription of CPython's `found_new_run`.

The empty-stack branch is an explicit no-op.  For a nonempty stack, the guard
records the assertion domain inherited from `powerloop`: adjacent run lengths
are positive and the two runs lie within the nonnegative list length.  A
failure of the fixed 64-step power loop is observable as fuel exhaustion.
The source's debug-only post-loop strictness assertion is not turned into a
release-mode refusal branch. -/
def foundNewRun? (state : MergeState κ ν) (n2 : Nat) :
    Option (FoundNewRunResult κ ν) :=
  if state.pending.isEmpty then
    some (foundNewRunSuccess state)
  else
    match state.pending[state.pending.size - 1]? with
    | none => none
    | some top =>
      if (!state.listlen.msb) && decide (state.basekeys ≤ top.base) &&
          (0 : PySSize).slt top.len && decide (0 < n2) &&
          decide (n2 ≤ PY_SSIZE_T_MAX) &&
          decide (top.base - state.basekeys + top.len.toNat + n2 ≤
            state.listlen.toNat) then
        let traced := powerloopTraced
          (BitVec.ofNat 64 (top.base - state.basekeys)) top.len
          (BitVec.ofNat 64 n2) state.listlen
        if !traced.stopped then
          some (foundNewRunOutOfFuel state)
        else
          foundNewRunLoop? state.pending.size state traced.result
      else
        none

private def foundNewRunExampleState : MergeState Nat Nat :=
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
      #[{ base := 0, len := 1, power := some 2 },
        { base := 1, len := 1, power := none }]
    key_compare := fun left right => decide (left < right)
    mr_current := 0
    mr_e := 0
    mr_mask := 0 }

set_option linter.style.nativeDecide false in
/-- The source explicitly makes an empty pending stack a no-op; in particular
it does not inspect the otherwise-invalid prospective length zero. -/
example :
    (foundNewRun?
        { foundNewRunExampleState with pending := #[] } 0).map
          (fun result =>
            (result.returnCode, result.fuelExhausted,
              result.state.pending.toList,
              result.state.data.entries.toList)) =
      some
        (0, false, [], foundNewRunExampleState.data.entries.toList) := by
  decide

set_option linter.style.nativeDecide false in
/-- Collapse uses strict `>` rather than `≥`: equality leaves both runs in
place and initializes the current top run with the computed power. -/
example :
    (foundNewRun? foundNewRunExampleState 1).map
        (fun result =>
          (result.returnCode, result.fuelExhausted,
            result.state.pending.toList)) =
      some
        (0, false,
          [{ base := 0, len := 1, power := some 2 },
           { base := 1, len := 1, power := some 2 }]) := by
  decide

end CPythonListsort
