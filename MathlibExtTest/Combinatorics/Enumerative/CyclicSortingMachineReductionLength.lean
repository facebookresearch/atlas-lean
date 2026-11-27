/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Combinatorics.Enumerative.CyclicSortingMachineReductionLength

open MetaMathlibExt

-- Both permutations of length two reduce to a singleton after one pass.
example : reductionSeq (cyclicSortingMachine [1, 2, 3] [1, 2]) = [1] ∧
    reductionSeq (cyclicSortingMachine [1, 2, 3] [2, 1]) = [1] := by decide

-- The input already has the increasing pairs `1, 2` and `3, 4`.
example : (reductionSeq (cyclicSortingMachine [1, 2, 3] [1, 2, 5, 3, 4, 6])).length < 6 :=
  length_reductionSeq_cyclicSortingMachine_123_lt (by decide) (by decide)

-- No increasing pair initially; the first entry is not maximal.
example : reductionSeq [2, 4, 1, 3] = [2, 4, 1, 3] ∧
    reductionSeq (cyclicSortingMachine [1, 2, 3] [2, 4, 1, 3]) = [1] := by decide

-- No increasing pair initially; the first entry is maximal.
example : reductionSeq [4, 2, 1, 3] = [4, 2, 1, 3] ∧
    reductionSeq (cyclicSortingMachine [1, 2, 3] [4, 2, 1, 3]) = [2, 1, 3] := by decide
