/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Combinatorics.Enumerative.SetPartitionSymmetricPeaksCoefficients

open Finset MetaMathlibExt

namespace MathlibExtTest.SetPartitionSymmetricPeaksCoefficients

private def total (n k : ℕ) : ℕ :=
  ∑ w ∈ univ.filter (fun w : Fin n → Fin k => IsSurjectiveRestrictedGrowthString w),
    symmetricPeakCount (List.ofFn fun i => (w i : ℕ))

-- The empty partition and a length shorter than the block count contribute zero.
example : total 0 0 = 0 := by
  rw [total, sum_symmetricPeakCount_setPartitions]
  decide

example : total 2 3 = 0 := by
  rw [total, sum_symmetricPeakCount_setPartitions]
  decide

-- At the first possible peak, only the unshifted Stirling term contributes.
example : total 3 2 = 1 := by
  rw [total, sum_symmetricPeakCount_setPartitions]
  decide

-- At length six with two blocks both i = 3 and i = 4 contribute.
example : total 6 2 = 20 := by
  rw [total, sum_symmetricPeakCount_setPartitions]
  decide

-- Independently enumerate the same two-block case.
set_option maxRecDepth 4096 in
example : total 6 2 = 20 := by decide

-- With three blocks, both j = 2 and j = 3 contribute.
example : total 6 3 = 54 := by
  rw [total, sum_symmetricPeakCount_setPartitions]
  decide

end MathlibExtTest.SetPartitionSymmetricPeaksCoefficients
