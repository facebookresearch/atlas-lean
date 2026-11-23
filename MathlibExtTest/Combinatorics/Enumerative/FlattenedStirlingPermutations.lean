/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Combinatorics.Enumerative.FlattenedStirlingPermutations

namespace MetaMathlibExt

-- The empty word contributes nothing to the one-run count.
example : flattenedStirlingRunCount 0 1 = 0 := by
  have hempty (w : Fin (2 * 0) → ℕ) : wordRunCount w = 0 := by
    simp [wordRunCount]
  simp [flattenedStirlingRunCount, hempty]

-- Equal adjacent letters stay in the same run.
example : IsStirlingPermutation 2 ![1, 1, 2, 2] ∧ IsFlattenedWord ![1, 1, 2, 2] ∧
    wordRunCount ![1, 1, 2, 2] = 1 := by
  unfold IsStirlingPermutation
  decide

-- A descent starts another run, even when its leading letter equals the first.
example : IsStirlingPermutation 2 ![1, 2, 2, 1] ∧ IsFlattenedWord ![1, 2, 2, 1] ∧
    wordRunCount ![1, 2, 2, 1] = 2 := by
  unfold IsStirlingPermutation
  decide

end MetaMathlibExt
