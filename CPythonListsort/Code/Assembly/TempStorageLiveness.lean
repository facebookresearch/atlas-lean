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

/-- Every temporary-payload access made by the raw top-level evaluator occurs
while temporary storage is live.  The explicit mode premise is required at
the generalized raw boundary. -/
theorem listSortImplTraced_tempPayloadAccessesLive
    (lt : BoolComparator κ) (reverse hasKeyfunc : Bool)
    (input : SortSlice κ ν) (hSize : input.entries.size ≤ PY_LIST_MAX)
    (hMode : SortSlice.ValuesModeInvariant hasKeyfunc input) :
    (listSortImplTraced? lt reverse hasKeyfunc input).trace.tempPayloadAccessesLive := by
  rcases listSortImplTraced_safe lt reverse hasKeyfunc input hSize hMode with
    ⟨result, hSafe⟩
  exact hSafe.traceSafety.tempAccessesLive

/-- The proof-carrying public input discharges the values-mode premise for the
whole-trace temporary-storage liveness result. -/
theorem listSortTraced_tempPayloadAccessesLive
    (lt : BoolComparator κ) (reverse : Bool) (input : ListSortInput κ ν)
    (hSize : input.slice.entries.size ≤ PY_LIST_MAX) :
    (listSortTraced? lt reverse input).trace.tempPayloadAccessesLive := by
  rcases listSortTraced_safe lt reverse input hSize with ⟨result, hSafe⟩
  exact hSafe.traceSafety.tempAccessesLive

end CPythonListsort
