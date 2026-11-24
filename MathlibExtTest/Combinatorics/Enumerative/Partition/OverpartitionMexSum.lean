/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Combinatorics.Enumerative.Partition.OverpartitionMexSum

namespace MetaMathlibExt.sigmaMexOverpartition_eq_sum_shifted_count

example (r : ℕ) (hr : 1 ≤ r) : sigmaMexOverpartition r 0 = 1 := by
  rw [← sigmaMexOverpartition_eq_sum_shifted_count 0 r hr, Finset.sum_filter,
    Finset.sum_range_succ]
  simp [overpartitionCount_zero]

-- The second triangular shift first contributes at six when the multiplicity is two.
example : sigmaMexOverpartition 2 5 = overpartitionCount 5 + overpartitionCount 3 := by
  simpa [Finset.sum_filter, Finset.sum_range_succ] using
    (sigmaMexOverpartition_eq_sum_shifted_count 5 2 (by decide)).symm

example : sigmaMexOverpartition 2 6 = overpartitionCount 6 + overpartitionCount 4 + 1 := by
  simpa [Finset.sum_filter, Finset.sum_range_succ, overpartitionCount_zero] using
    (sigmaMexOverpartition_eq_sum_shifted_count 6 2 (by decide)).symm

end MetaMathlibExt.sigmaMexOverpartition_eq_sum_shifted_count
