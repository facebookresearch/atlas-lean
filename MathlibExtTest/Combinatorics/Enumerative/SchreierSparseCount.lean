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
