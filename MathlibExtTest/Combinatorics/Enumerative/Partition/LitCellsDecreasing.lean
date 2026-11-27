/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Combinatorics.Enumerative.Partition.LitCellsDecreasing

open MetaMathlibExt PowerSeries
open scoped PowerSeries.WithPiTopology

-- The second column fits exactly under the first column's light bound.
example : litCellsDecreasing (Nat.Partition.ofMultiset {2, 1}) = 2 := by
  have hp : (Nat.Partition.ofMultiset {2, 1}).parts = 2 ::ₘ ({1} : Multiset ℕ) := by
    rw [Nat.Partition.ofMultiset_parts, Multiset.filter_eq_self.mpr (by simp)]
    rfl
  rw [litCellsDecreasing, decreasingParts, hp, Multiset.sort_cons _ _ _ (by simp),
    Multiset.sort_singleton]
  decide +kernel

-- A second column of the same height as the first increases the statistic.
example : litCellsDecreasing (Nat.Partition.ofMultiset {2, 2}) = 3 := by
  have hp : (Nat.Partition.ofMultiset {2, 2}).parts = 2 ::ₘ ({2} : Multiset ℕ) := by
    rw [Nat.Partition.ofMultiset_parts, Multiset.filter_eq_self.mpr (by simp)]
    rfl
  rw [litCellsDecreasing, decreasingParts, hp, Multiset.sort_cons _ _ _ (by simp),
    Multiset.sort_singleton]
  decide +kernel

-- The first staircase allows just the empty partition and the partition (1).
example : trianglePartitionSeries 1 = 1 + X := by
  simp [trianglePartitionSeries, Finset.sum_range_succ, triangularQBinomial_zero_right,
    triangularQBinomial_recursion.2.1]

-- The empty partition and (1) do not contribute to the generating function.
example :
    let F : ℤ⟦X⟧ := ∑' r : ℕ, ((r + 2 : ℕ) : ℤ⟦X⟧) * X ^ (r + 2) *
      trianglePartitionSeries (r + 1)
    coeff 0 F = 0 ∧ coeff 1 F = 0 := by
  dsimp only
  rw [← litCellsDecreasing_firstColumn_generatingFunction]
  simp
