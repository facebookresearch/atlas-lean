/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import CSLibExt.Algorithms.Sorting.CPythonListsort.Assembly.ListSortLocalBounds

-- Preserve the imported development's original implicit type binders.
set_option autoImplicit true

namespace CPythonListsort

universe u v

variable {κ : Type u} {ν : Type v}

/-- Comparator-independent top-level completion and safety for the validated
public input of at most `PY_LIST_MAX = 2 ^ 60 - 1` entries, for every Boolean
comparator (no ordering premise) and either `reverse` flag.  The traced
evaluator returns some result; its trace records no fuel exhaustion (the
top-level scan's fuel is the input length); every recorded post-push
pending-stack depth is at most `61`, which is below `MAX_MERGE_PENDING = 64`;
and every recorded ordinary access attempt lies within the extent recorded
beside it.  The existential conjunct exports successful evaluation rather
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

/-- Keyed-array specialization of `listsort_safe` through the validated keyed
constructor, for arrays of at most `PY_LIST_MAX` entries. -/
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

/-- Ordinary-array specialization of `listsort_safe` through the validated
unkeyed constructor, for arrays of at most `PY_LIST_MAX` entries. -/
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
