/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Combinatorics.Enumerative.Partition.RookParityFive

namespace MetaMathlibExt

-- Check every residue in the first period covered by the theorem.
example : List.map (fun n ↦ maxRookPartitionCount 5 n % 2) [26, 27, 28, 29, 30, 31, 32, 33] =
    [1, 1, 1, 0, 1, 0, 1, 1] := by
  simp only [List.map_cons, List.map_nil]
  rw [maxRookPartitionCount_five_mod_two 26 (by decide),
    maxRookPartitionCount_five_mod_two 27 (by decide),
    maxRookPartitionCount_five_mod_two 28 (by decide),
    maxRookPartitionCount_five_mod_two 29 (by decide),
    maxRookPartitionCount_five_mod_two 30 (by decide),
    maxRookPartitionCount_five_mod_two 31 (by decide),
    maxRookPartitionCount_five_mod_two 32 (by decide),
    maxRookPartitionCount_five_mod_two 33 (by decide)]
  decide

end MetaMathlibExt
