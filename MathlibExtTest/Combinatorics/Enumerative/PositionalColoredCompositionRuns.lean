/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Combinatorics.Enumerative.PositionalColoredCompositionRuns

namespace MetaMathlibExt.PositionalColoredCompositionRunsTest

-- The empty string contributes one to the count of compositions of one.
example : positionalColoredCompositionCount 2 0 1 = 1 := by
  rw [even_succ_eq_sum_runLength_prod 0]
  simp

-- The eight strings of length three have total weight twelve.
example : positionalColoredCompositionCount 2 0 4 = 12 := by
  rw [even_succ_eq_sum_runLength_prod 3]
  simp only [List.ofFn_succ, List.ofFn_zero, List.splitOn_cons_eq_ite_modifyHead, List.splitOn_nil]
  decide

-- Consecutive separators contribute no factor, including at the ends.
example :
    let w := [false, true, true, false, false, true, true, true, false]
    (((w.splitOn false).map List.length).filter (· ≠ 0)).prod = 6 := by
  simp [List.splitOn_cons_eq_ite_modifyHead, List.modifyHead]

end MetaMathlibExt.PositionalColoredCompositionRunsTest
