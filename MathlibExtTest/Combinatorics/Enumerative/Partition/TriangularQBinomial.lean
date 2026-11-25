/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Combinatorics.Enumerative.Partition.TriangularQBinomial

open MetaMathlibExt PowerSeries

-- The zero-width recurrence has just the empty partition on each side.
example (r : ℕ) : triangularQBinomial (r + 1) 0 = 1 := by
  rw [triangularQBinomial_recursion.1 r 0 (Nat.zero_le _)]
  simp [triangularQBinomial_recursion.2.2.2.1]

-- The full-width staircase of height two contains (1, 1) and (2, 1).
example : triangularQBinomial 2 2 = X ^ 2 * (1 + X) := by
  rw [triangularQBinomial_recursion.1 1 2 (by decide)]
  simp [Finset.sum_range_succ, triangularQBinomial_recursion.2.1,
    triangularQBinomial_recursion.2.2.2.1, triangularQBinomial_recursion.2.2.2.2 1 2 (by decide)]

-- There is no room for a second positive part under a staircase of height one.
example : triangularQBinomial 1 2 = 0 :=
  triangularQBinomial_recursion.2.2.2.2 1 2 (by decide)
