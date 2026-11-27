/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.NumberTheory.FareyStaircaseIciOneSubLogTwoSubsetClosureFloorGaps
import Mathlib.Analysis.SpecialFunctions.Log.Basic

namespace MathlibExtTest.NumberTheory.FareyStaircaseIciOneSubLogTwoSubsetClosureFloorGaps

-- The value `1` lies in the closure of the floor gaps.
example : (1 : ℝ) ∈ closure {y : ℝ | ∃ n : ℕ, 1 ≤ n ∧ ∃ x : ℝ,
    y = ⌊(n : ℝ) * x⌋ - n * MetaMathlibExt.fareyStaircase n x} := by
  apply MetaMathlibExt.Ici_one_sub_log_two_subset_closure_floor_gaps
  rw [Set.mem_Ici, sub_le_iff_le_add]
  exact le_add_of_nonneg_right (Real.log_nonneg one_le_two)

-- The interval `[1 - log 2, 7]` lies in the closure of the floor gaps.
example : Set.Icc (1 - Real.log 2) 7 ⊆ closure {y : ℝ | ∃ n : ℕ, 1 ≤ n ∧ ∃ x : ℝ,
    y = ⌊(n : ℝ) * x⌋ - n * MetaMathlibExt.fareyStaircase n x} :=
  Set.Icc_subset_Ici_self.trans
    MetaMathlibExt.Ici_one_sub_log_two_subset_closure_floor_gaps

end MathlibExtTest.NumberTheory.FareyStaircaseIciOneSubLogTwoSubsetClosureFloorGaps
