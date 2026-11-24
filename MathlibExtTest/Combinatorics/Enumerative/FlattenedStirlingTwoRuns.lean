/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Combinatorics.Enumerative.FlattenedStirlingTwoRuns

namespace MetaMathlibExt

-- The first step only uses the one-run word. At order three both terms contribute.
example : flattenedStirlingRunCount 3 2 = 5 := by
  have ⟨h₁, step⟩ := flattenedStirlingRunCount_two_recursion
  rw [step 2 (by decide), step 1 (by decide), h₁]

-- Prepending the largest pair to a one-run word gives two runs with decreasing leaders.
example : IsStirlingPermutation 2 ![2, 2, 1, 1] ∧
    wordRunCount ![2, 2, 1, 1] = 2 ∧ ¬ IsFlattenedWord ![2, 2, 1, 1] := by
  unfold IsStirlingPermutation
  decide

end MetaMathlibExt
