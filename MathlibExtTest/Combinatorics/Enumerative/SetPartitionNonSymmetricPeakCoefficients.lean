/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Combinatorics.Enumerative.SetPartitionNonSymmetricPeakCoefficients

open Finset MetaMathlibExt

namespace MathlibExtTest.SetPartitionNonSymmetricPeakCoefficients

private def total (n k : ℕ) : ℕ :=
  ∑ w ∈ univ.filter (fun w : Fin n → Fin k => IsSurjectiveRestrictedGrowthString w),
    nonSymmetricPeakCount (List.ofFn fun i => (w i : ℕ))

-- The empty partition contributes zero, as does an impossible block count.
example : total 0 0 = 0 := by
  rw [total, sum_nonSymmetricPeakCount_setPartitions]
  decide

example : total 2 3 = 0 := by
  rw [total, sum_nonSymmetricPeakCount_setPartitions]
  decide

-- At the first possible non-symmetric peak only the linear term contributes.
example : total 4 3 = 1 := by
  rw [total, sum_nonSymmetricPeakCount_setPartitions]
  decide

-- Independently enumerate that case.
example : total 4 3 = 1 := by decide

-- Both inner indices i = 3 and i = 4 contribute.
example : total 7 3 = 108 := by
  rw [total, sum_nonSymmetricPeakCount_setPartitions]
  decide

-- Both outer indices j = 3 and j = 4 contribute.
example : total 7 4 = 205 := by
  rw [total, sum_nonSymmetricPeakCount_setPartitions]
  decide

end MathlibExtTest.SetPartitionNonSymmetricPeakCoefficients
