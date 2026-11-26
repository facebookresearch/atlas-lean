/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Combinatorics.Enumerative.Partition.PartsNotTwoModFourTriangularSumEven

private def triangularSumP2 (n : ℕ) : ℕ :=
  ∑ k ∈ (Finset.range (n + 1)).filter (fun k => k * (k + 1) / 2 ≤ n),
    MetaMathlibExt.partsNotTwoModFourCount (n - k * (k + 1) / 2)

example (n : ℕ) (hn : 0 < n) : Even (triangularSumP2 n) :=
  MetaMathlibExt.partsNotTwoModFour_triangular_sum_even (n := n) (hn := hn)

-- The count $P_2(0)$: only the empty partition counts.
example : MetaMathlibExt.partsNotTwoModFourCount 0 = 1 := by decide

-- The count $P_2(1)$: only the partition $1$ counts.
example : MetaMathlibExt.partsNotTwoModFourCount 1 = 1 := by
  unfold MetaMathlibExt.partsNotTwoModFourCount Nat.Partition.restricted
  simp

-- At zero the triangular sum is $1$, so positivity is necessary.
example : triangularSumP2 0 = 1 := by decide
