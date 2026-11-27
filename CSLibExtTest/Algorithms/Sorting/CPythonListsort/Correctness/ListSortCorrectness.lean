/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import CSLibExt.Algorithms.Sorting.CPythonListsort.Correctness.ListSortCorrectness
import CSLibExtTest.Algorithms.Sorting.CPythonListsort.RuntimeAssert

namespace CPythonListsort

/-! ## Inhabited boundary witnesses -/

private def correctnessRegressionLt : BoolComparator Nat :=
  fun left right => decide (left < right)

private theorem correctnessRegressionOrder :
    BoolStrictWeakOrder correctnessRegressionLt := by
  constructor
  let hstrict : IsStrictOrder Nat
      (fun left right => correctnessRegressionLt left right = true) :=
    { irrefl := by simp [correctnessRegressionLt]
      trans := by
        intro a b c hab hbc
        simp [correctnessRegressionLt] at hab hbc ⊢
        omega }
  exact @IsStrictWeakOrder.mk Nat
    (fun left right => correctnessRegressionLt left right = true)
    hstrict (by
      intro a b c hab hbc
      simp [correctnessRegressionLt] at hab hbc ⊢
      omega)

private def reverseKeyedDuplicateInput : ListSortInput Nat Nat :=
  ListSortInput.keyed #[(2, 20), (1, 10), (1, 11), (2, 21)]

private structure CorrectnessRegressionView where
  returnCode : Int
  fuelExhausted : Bool
  entries : List (Nat × Nat × Option Nat)
  deriving DecidableEq, Repr

private def correctnessRegressionView
    (result : ListSortImplResult (Occurrence Nat) Nat) :
    CorrectnessRegressionView :=
  { returnCode := result.returnCode
    fuelExhausted := result.fuelExhausted
    entries := result.state.data.entries.toList.map fun entry =>
      (entry.key.value, entry.key.origin, entry.value) }

/-- Kernel-checked, inhabited keyed reverse-mode boundary witness with
duplicate keys.  The raw-result equation ties every semantic conjunct to the
actual `listSort?` execution.  Sortedness fixes descending key order, the
stable-occurrence predicate keeps equal keys in increasing origin order, and
the entry snapshot keeps each payload paired with its original occurrence.

This deliberately avoids reducing the complete evaluator inside the kernel:
the public correctness theorem supplies the witness and all three observable
postconditions without adding another compiler-checked evaluator leaf. -/
theorem listSort_reverse_keyed_duplicate_regression :
    ∃ result,
      listSort? (occurrenceComparator correctnessRegressionLt) true
          reverseKeyedDuplicateInput.withOccurrenceKeys = some result ∧
        result.returnCode = 0 ∧
        result.fuelExhausted = false ∧
        Sorted
          (occurrenceComparator
            (requestedComparator correctnessRegressionLt true))
          result.occurrences ∧
        StableOccurrencePermutation
          (requestedComparator correctnessRegressionLt true)
          (tagOccurrences
            (reverseKeyedDuplicateInput.slice.entries.map
              SortSliceEntry.key)).toList
          result.occurrences.toList ∧
        EntrySnapshotPermutation reverseKeyedDuplicateInput.slice
          result.state.data := by
  have hmax : reverseKeyedDuplicateInput.slice.entries.size ≤ PY_LIST_MAX := by
    norm_num [reverseKeyedDuplicateInput, ListSortInput.keyed, PY_LIST_MAX,
      PY_SSIZE_T_MAX, PY_OBJECT_PTR_BYTES]
  rcases listSort_reverse_correct correctnessRegressionLt
      correctnessRegressionOrder reverseKeyedDuplicateInput hmax with
    ⟨result, hresult⟩
  exact ⟨result, hresult.rawResultEq, hresult.returnCode,
    hresult.resultFuel, hresult.sorted, hresult.stable,
    hresult.entrySnapshot⟩

set_option maxRecDepth 100000 in
/-- Empty and singleton executions really take the public bypass, return
successfully in reverse mode, and retain the exact occurrence/payload data. -/
theorem listSort_small_boundary_regression :
    (listSort? (occurrenceComparator correctnessRegressionLt) true
      (ListSortInput.unkeyed (#[] : Array Nat)).withOccurrenceKeys).map
        (fun result =>
          (result.returnCode, result.fuelExhausted,
            result.state.data.entries.size)) = some (0, false, 0) ∧
      (listSort? (occurrenceComparator correctnessRegressionLt) true
        (ListSortInput.keyed #[(7, 70)]).withOccurrenceKeys).map
          correctnessRegressionView =
        some
          { returnCode := 0
            fuelExhausted := false
            entries := [(7, 0, some 70)] } := by
  let emptyInput : ListSortInput Nat PUnit :=
    ListSortInput.unkeyed (#[] : Array Nat)
  let singletonInput : ListSortInput Nat Nat :=
    ListSortInput.keyed #[(7, 70)]
  have hemptySmall : emptyInput.slice.entries.size < 2 := by
    norm_num [emptyInput, ListSortInput.unkeyed, ListSortInput.unkeyedAs]
  have hemptyMax : emptyInput.slice.entries.size ≤ PY_LIST_MAX := by
    norm_num [emptyInput, ListSortInput.unkeyed, ListSortInput.unkeyedAs,
      PY_LIST_MAX, PY_SSIZE_T_MAX, PY_OBJECT_PTR_BYTES]
  have hsingletonSmall : singletonInput.slice.entries.size < 2 := by
    norm_num [singletonInput, ListSortInput.keyed]
  have hsingletonMax : singletonInput.slice.entries.size ≤ PY_LIST_MAX := by
    norm_num [singletonInput, ListSortInput.keyed, PY_LIST_MAX,
      PY_SSIZE_T_MAX, PY_OBJECT_PTR_BYTES]
  rcases listSort_small_correct correctnessRegressionLt true emptyInput
      hemptySmall hemptyMax with ⟨emptyResult, hempty⟩
  rcases listSort_small_correct correctnessRegressionLt true singletonInput
      hsingletonSmall hsingletonMax with ⟨singletonResult, hsingleton⟩
  have hemptyRaw :
      listSort? (occurrenceComparator correctnessRegressionLt) true
          (ListSortInput.unkeyed (#[] : Array Nat)).withOccurrenceKeys =
        some emptyResult := by
    simpa [emptyInput] using hempty.rawResultEq
  have hsingletonRaw :
      listSort? (occurrenceComparator correctnessRegressionLt) true
          (ListSortInput.keyed #[(7, 70)]).withOccurrenceKeys =
        some singletonResult := by
    simpa [singletonInput] using hsingleton.rawResultEq
  have hemptyEntries : emptyResult.state.data.entries = #[] := by
    have hsnapshot := hempty.entrySnapshot
    have hlist : emptyResult.state.data.entries.toList.Perm [] := by
      simpa [EntrySnapshotPermutation, emptyInput, ListSortInput.unkeyed,
        ListSortInput.unkeyedAs, tagSortSliceOccurrences] using hsnapshot
    apply Array.toList_inj.mp
    simpa using hlist.eq_nil
  have hsingletonEntries : singletonResult.state.data.entries =
      #[{ key := { value := 7, origin := 0 }, value := some 70 }] := by
    have hsnapshot := hsingleton.entrySnapshot
    simp [EntrySnapshotPermutation, singletonInput, ListSortInput.keyed,
      tagSortSliceOccurrences] at hsnapshot
    apply Array.toList_inj.mp
    simpa using hsnapshot
  constructor
  · rw [hemptyRaw]
    simp [hempty.returnCode, hempty.resultFuel, hemptyEntries]
  · rw [hsingletonRaw]
    simp [correctnessRegressionView, hsingleton.returnCode,
      hsingleton.resultFuel, hsingletonEntries]

/-- Compiler-checked exact-output witness for stable forward sorting with
duplicate keys.  This declaration is review evidence only and is forbidden
from becoming a proof dependency by `verify/verify_trust_boundary.py`. -/
def listSort_forward_keyed_duplicate_exact_regression : IO Unit :=
  CPythonListsortTest.assertTrue "listSort_forward_keyed_duplicate_exact_regression" (decide (
    (listSort? (occurrenceComparator correctnessRegressionLt) false
        reverseKeyedDuplicateInput.withOccurrenceKeys).map
        correctnessRegressionView =
      some
        { returnCode := 0
          fuelExhausted := false
          entries :=
            [(1, 1, some 10), (1, 2, some 11),
             (2, 0, some 20), (2, 3, some 21)] }))

#eval listSort_forward_keyed_duplicate_exact_regression

/-- Compiler-checked exact-output witness for reverse sorting with duplicate
keys: key order is descending while equal-key origins, and therefore their
payloads, retain original order.  This declaration is review evidence only and
is forbidden from becoming a proof dependency by
`verify/verify_trust_boundary.py`. -/
def listSort_reverse_keyed_duplicate_exact_regression : IO Unit :=
  CPythonListsortTest.assertTrue "listSort_reverse_keyed_duplicate_exact_regression" (decide (
    (listSort? (occurrenceComparator correctnessRegressionLt) true
        reverseKeyedDuplicateInput.withOccurrenceKeys).map
        correctnessRegressionView =
      some
        { returnCode := 0
          fuelExhausted := false
          entries :=
            [(2, 0, some 20), (2, 3, some 21),
             (1, 1, some 10), (1, 2, some 11)] }))

#eval listSort_reverse_keyed_duplicate_exact_regression

end CPythonListsort
