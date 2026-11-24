/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Combinatorics.Enumerative.CyclicPatternAvoidingStacks

open MetaMathlibExt

example : reductionSeq [] = [] ∧ cyclicSortingMachine [1, 2, 3] [] = [] := by decide

-- Contracting the middle pair leaves a permutation that still takes two passes.
example : reductionSeq [1, 4, 2, 3, 5] = [1, 3, 2, 4] ∧
    cyclicSortingMachine [1, 2, 3] [1, 4, 2, 3, 5] = [4, 1, 2, 3, 5] := by decide

example : (cyclicSortingMachine [1, 2, 3])^[2] [1, 4, 2, 3, 5] = List.range' 1 5 := by
  apply (cyclicSortingMachine_123_iterate_eq_id_iff_reductionSeq (k := 2) (n := 5)
    (π := [1, 4, 2, 3, 5]) (by decide)).mpr
  decide
