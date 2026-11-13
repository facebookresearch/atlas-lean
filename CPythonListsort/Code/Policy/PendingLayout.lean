/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Code.Transcription.MergeState

/-!
# Pending-run layout

The invariant deliberately mentions only run positions and lengths. Powers,
comparators, sorting properties, and the eventual stack-capacity theorem are
kept in their own policy and correctness nodes.
-/

namespace CPythonListsort

universe u

/-- The first index after a pending run. -/
def PendingRun.endIndex (run : PendingRun) : Nat :=
  run.base + run.len.toNat

/-- A run list covers `[cursor, limit)` without gaps or empty runs. -/
def PendingRunsCover : Nat → Nat → List PendingRun → Prop
  | cursor, limit, [] => cursor = limit
  | cursor, limit, run :: rest =>
      run.base = cursor ∧
        run.len.Nonnegative ∧
        0 < run.len.toNat ∧
        run.endIndex ≤ limit ∧
        PendingRunsCover run.endIndex limit rest

/-- Pending runs are nonempty, in the input region, consecutive, and cover
exactly the already-scanned prefix beginning at `basekeys`. -/
def PendingLayout (state : MergeState κ ν) (scanned : Nat) : Prop :=
  state.listlen.Nonnegative ∧
    state.basekeys + state.listlen.toNat ≤ state.data.entries.size ∧
    scanned ≤ state.listlen.toNat ∧
    PendingRunsCover state.basekeys (state.basekeys + scanned)
      state.pending.toList

/-- The lengths of runs that cover an interval add up to that interval's
length. -/
theorem PendingRunsCover.totalLength
    {cursor limit : Nat} {runs : List PendingRun}
    (h : PendingRunsCover cursor limit runs) :
    cursor + (runs.map fun run => run.len.toNat).sum = limit := by
  induction runs generalizing cursor with
  | nil =>
      simpa [PendingRunsCover] using h
  | cons run rest ih =>
      rcases h with ⟨hbase, _, _, _, hrest⟩
      simpa [PendingRunsCover, PendingRun.endIndex, hbase, Nat.add_assoc] using
        ih hrest

/-- Two successful adjacent array lookups expose the corresponding
prefix/pair/suffix decomposition of `toList`. -/
theorem Array.exists_pair_split_of_getElem?_eq_some
    {α : Type u} {xs : Array α} {i : Nat} {left right : α}
    (hleft : xs[i]? = some left)
    (hright : xs[i + 1]? = some right) :
    ∃ before after,
      before.length = i ∧
      xs.toList = before ++ left :: right :: after := by
  rcases getElem?_eq_some_iff.mp hleft with ⟨hi, hleft'⟩
  rcases getElem?_eq_some_iff.mp hright with ⟨hi1, hright'⟩
  let before := xs.toList.take i
  let after := xs.toList.drop (i + 2)
  refine ⟨before, after, ?_, ?_⟩
  · simp [before, Nat.le_of_lt hi]
  · have hleftList : xs.toList[i] = left := by
      simpa using hleft'
    have hrightList : xs.toList[i + 1] = right := by
      simpa using hright'
    rw [← List.take_append_drop i xs.toList]
    rw [List.drop_eq_getElem_cons (by simpa using hi)]
    rw [hleftList]
    rw [List.drop_eq_getElem_cons (by simpa using hi1)]
    rw [hrightList]

end CPythonListsort
