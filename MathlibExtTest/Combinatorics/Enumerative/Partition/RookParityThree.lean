/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Combinatorics.Enumerative.Partition.RookParityThree

namespace MetaMathlibExt

example : maxRookPartitionCount 3 10 % 2 = 1 :=
  maxRookPartitionCount_three_mod_two (n := 10) (hn := by decide)

example : maxRookPartitionCount 3 11 % 2 = 0 :=
  maxRookPartitionCount_three_mod_two (n := 11) (hn := by decide)

example : maxRookPartitionCount 3 16 % 2 = 1 :=
  maxRookPartitionCount_three_mod_two (n := 16) (hn := by decide)

example : maxRookPartitionCount 3 23 % 2 = 0 :=
  maxRookPartitionCount_three_mod_two (n := 23) (hn := by decide)

end MetaMathlibExt
