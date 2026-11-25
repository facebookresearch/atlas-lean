/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Combinatorics.YoungTableaux.SumSYTCountSq

open MathlibExt.Combinatorics.YoungTableaux.HookLength
open MathlibExt.Combinatorics.YoungTableaux.HookLengthWanted

-- The empty partition contributes one pair of empty tableaux.
example : (∑ p : (0 : ℕ).Partition, sytCount (YoungDiagram.ofPartition p) ^ 2) = 1 :=
  sum_sytCount_sq (n := 0)

-- Size three is the first level with a shape admitting several tableaux.
example : (∑ p : (3 : ℕ).Partition, sytCount (YoungDiagram.ofPartition p) ^ 2) = 6 :=
  sum_sytCount_sq (n := 3)
