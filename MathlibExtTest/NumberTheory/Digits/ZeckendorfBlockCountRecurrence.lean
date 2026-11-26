/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.NumberTheory.Digits.ZeckendorfBlockCountRecurrence

/-! # Tests for the Zeckendorf block-sum recurrence -/

open MetaMathlibExt

-- At the last small index, the coefficient on the length-zero count is e₂, not 1 + e₂.
example : lStarBlockSumCount [2, 3] 2 =
    2 * lStarBlockSumCount [2, 3] 1 + 3 * lStarBlockSumCount [2, 3] 0 := by
  have h := (lStarBlockSumCount_recurrence [2, 3] (by decide) (by decide)).1 2
    (by decide) (by decide)
  have hI : (Finset.Icc 1 2 : Finset ℕ) = {1, 2} := by decide
  rw [hI] at h
  simpa [Finset.sum_insert] using h

-- At the first large index, the extra periodic term changes that coefficient to 1 + e₂.
example : lStarBlockSumCount [2, 3] 3 =
    2 * lStarBlockSumCount [2, 3] 2 + 4 * lStarBlockSumCount [2, 3] 1 := by
  have h := (lStarBlockSumCount_recurrence [2, 3] (by decide) (by decide)).2 3 (by decide)
  have hI : (Finset.Ico 1 [2, 3].length : Finset ℕ) = {1} := by decide
  rw [hI] at h
  simpa using h
