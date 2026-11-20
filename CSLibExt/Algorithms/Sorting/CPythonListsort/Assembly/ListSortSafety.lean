/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Code.Assembly.ListSortLocalBounds

namespace CPythonListsort

universe u v

variable {κ : Type u} {ν : Type v}

/-- Comparator-independent top-level completion and safety for the validated
public input.  The existential conjunct exports successful evaluation rather
than asking consumers to infer completion from fuel non-exhaustion.  The
push-depth conjunct is about every recorded post-push depth, not a guarded or
clamped stack operation. -/
theorem listsort_safe
    (lt : BoolComparator κ) (reverse : Bool) (input : ListSortInput κ ν)
    (hSize : input.slice.entries.size ≤ PY_LIST_MAX) :
    let execution := listSortTraced? lt reverse input
    (∃ result, execution.result = some result) ∧
      execution.trace.fuelExhausted = false ∧
      execution.trace.stackDepthMax ≤ 61 ∧
      61 < MAX_MERGE_PENDING ∧
      execution.trace.allAccessesInBounds := by
  rcases listSortTraced_safe lt reverse input hSize with ⟨result, hSafe⟩
  exact ⟨⟨result, hSafe.resultEq⟩, hSafe.traceSafety.fuel,
    hSafe.traceSafety.stackDepth,
    by norm_num [MAX_MERGE_PENDING],
    listSortTraced_allAccessesInBounds lt reverse input hSize⟩

/-- Keyed-array specialization through the validated keyed constructor. -/
theorem listsort_safe_keyed
    (lt : κ → κ → Bool) (reverse : Bool) (entries : Array (κ × ν))
    (hSize : entries.size ≤ PY_LIST_MAX) :
    let execution := listSortTraced? lt reverse (ListSortInput.keyed entries)
    (∃ result, execution.result = some result) ∧
      execution.trace.fuelExhausted = false ∧
      execution.trace.stackDepthMax ≤ 61 ∧
      61 < MAX_MERGE_PENDING ∧
      execution.trace.allAccessesInBounds := by
  apply listsort_safe lt reverse (ListSortInput.keyed entries)
  simpa [ListSortInput.keyed] using hSize

/-- Ordinary-array specialization through the validated unkeyed constructor. -/
theorem listsort_safe_unkeyed
    (lt : α → α → Bool) (reverse : Bool) (xs : Array α)
    (hSize : xs.size ≤ PY_LIST_MAX) :
    let execution := listSortTraced? lt reverse (ListSortInput.unkeyed xs)
    (∃ result, execution.result = some result) ∧
      execution.trace.fuelExhausted = false ∧
      execution.trace.stackDepthMax ≤ 61 ∧
      61 < MAX_MERGE_PENDING ∧
      execution.trace.allAccessesInBounds := by
  simpa using
    listsort_safe (κ := α) (ν := PUnit) lt reverse (ListSortInput.unkeyed xs)
      (by simpa [ListSortInput.unkeyed, ListSortInput.unkeyedAs] using hSize)

end CPythonListsort
