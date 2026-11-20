/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Code.Assembly.ListSortTermination

namespace CPythonListsort

universe u v

variable {κ : Type u} {ν : Type v}

/-- Every ordinary access recorded by the raw top-level evaluator is within
the extent stored on that access event. -/
theorem listSortImplTraced_allAccessesInBounds
    (lt : BoolComparator κ) (reverse hasKeyfunc : Bool)
    (input : SortSlice κ ν) (hSize : input.entries.size ≤ PY_LIST_MAX)
    (hMode : SortSlice.ValuesModeInvariant hasKeyfunc input) :
    (listSortImplTraced? lt reverse hasKeyfunc input).trace.allAccessesInBounds := by
  rcases listSortImplTraced_safe lt reverse hasKeyfunc input hSize hMode with
    ⟨result, hSafe⟩
  exact hSafe.traceSafety.accessesInBounds

/-- Public access-bounds projection; `ListSortInput` carries the values-mode
invariant required by the raw theorem. -/
theorem listSortTraced_allAccessesInBounds
    (lt : BoolComparator κ) (reverse : Bool) (input : ListSortInput κ ν)
    (hSize : input.slice.entries.size ≤ PY_LIST_MAX) :
    (listSortTraced? lt reverse input).trace.allAccessesInBounds := by
  rcases listSortTraced_safe lt reverse input hSize with ⟨result, hSafe⟩
  exact hSafe.traceSafety.accessesInBounds

end CPythonListsort
