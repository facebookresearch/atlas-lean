/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import CSLibExt.Algorithms.Sorting.CPythonListsort.Correctness.FoundNewRunCorrectness
import CSLibExtTest.Algorithms.Sorting.CPythonListsort.RuntimeAssert

namespace CPythonListsort

private def foundNewRunTakenMergeLt : BoolComparator Nat :=
  fun left right => decide (left < right)

private def foundNewRunTakenMergeEntry (value origin : Nat) :
    SortSliceEntry (Occurrence Nat) PUnit.{1} :=
  { key := { value := value, origin := origin }, value := none }

private def foundNewRunTakenMergeState : MergeState (Occurrence Nat) PUnit.{1} :=
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

/-- Concrete anti-vacuity witness for the strict collapse branch: the stored
power `3` exceeds the incoming power `2`, so the real loop merges the two
one-element runs, observably reorders `2,1` to `1,2`, shrinks the stack, and
then writes power `2` on the combined run. -/
def foundNewRunLoop_taken_merge_regression : IO Unit :=
  CPythonListsortTest.assertTrue "foundNewRunLoop_taken_merge_regression" (decide (
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
        some [(1, 1), (2, 0), (3, 2)]))

#eval foundNewRunLoop_taken_merge_regression

end CPythonListsort
