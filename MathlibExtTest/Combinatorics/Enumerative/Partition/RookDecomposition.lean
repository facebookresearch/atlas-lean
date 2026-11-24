/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Combinatorics.Enumerative.Partition.RookDecomposition

namespace MetaMathlibExt

-- The empty board supports only the empty placement.
example : (partitionFerrersBoard (Nat.Partition.indiscrete 0)).card = 0 := by decide +kernel
example : maxRookPartitionCount 3 0 = 0 := by decide +kernel

-- The staircase has three rooks, and deleting its bottom cell leaves only two.
example : partitionMaxRookNumber (Nat.Partition.ofMultiset ({3, 2, 1} : Multiset ℕ)) = 3 := by
  decide +kernel

example : partitionMaxRookNumber (Nat.Partition.ofMultiset ({3, 2} : Multiset ℕ)) = 2 := by
  decide +kernel

-- The square has rook number three and has no cells extending beyond either side.
example : partitionMaxRookNumber (Nat.Partition.ofMultiset ({3, 3, 3} : Multiset ℕ)) = 3 := by
  decide +kernel

end MetaMathlibExt
