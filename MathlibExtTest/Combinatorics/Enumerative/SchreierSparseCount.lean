/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Combinatorics.Enumerative.SchreierSparseCount

open MathlibExt.Combinatorics.Enumerative.SchreierTypeSetsWanted

-- Equal consecutive gaps and equality in the Schreier bound are both allowed.
example : IsSchreier {3, 4, 5} ∧ IsSparse {3, 4, 5} := by decide

example : ¬ IsSparse {3, 5, 6} := by decide

example : ¬ IsSchreier {2, 3, 4} := by decide

-- The singleton at the lower endpoint corresponds to the empty partition.
example : schreierSparseCount 1 = 1 := by
  rw [schreierSparseCount_eq 1 (by decide)]
  exact Fintype.card_unique (α := Nat.Partition 0)

-- The five partitions of four include repeated parts and parts of size one.
example : partitionCount 4 = 5 := by
  rw [← schreierSparseCount_eq 5 (by decide)]
  decide

-- The minimum of an `ℓ`-strong Schreier set is at least `ℓ |A| - ℓ + 1`.
example : IsStrongSchreier 1 {3, 4, 5} ∧ ¬ IsStrongSchreier 1 {2, 4, 5} := by decide

-- The first refined set of the source, `{2ℓ + 1, 2ℓ + 2, 2ℓ + 3}` for `ℓ = 1` and `n = 4`.
example : IsRefinedSchreier 4 1 {3, 4, 5} := by decide

-- The two largest gaps must be equal, and a refined set has at least three elements.
example : ¬ IsRefinedSchreier 5 0 {1, 3, 6} ∧ ¬ IsRefinedSchreier 2 0 {1, 3} := by decide

-- The partitions `3 + 1` and `2 + 2` of four match the sets `{1, 3, 5}` and `{3, 4, 5}`.
example : partitionMinPartExactCount 4 1 2 = 2 :=
  (partitionMinPartExactCount_eq_refined 4 0 2 (by decide) (by decide)).trans (by decide)

-- Both counts vanish when `n < k (ℓ + 1)`: four has no partition into two parts at least three.
example : partitionMinPartExactCount 4 3 2 = 0 :=
  (partitionMinPartExactCount_eq_refined 4 2 2 (by decide) (by decide)).trans (by decide)
