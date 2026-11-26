/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.Combinatorics.Enumerative.FlattenedPermutationRunRecurrence

open MetaMathlibExt

-- At lengths one and two there is no room for a descent after the first letter.
private theorem count_one_two : (flattenedPermRunCount 1 2 : ℤ) = 0 := by
  have h := flattenedPermRunCount_recursion.1 1 2 (by decide) (by decide)
  rwa [show Finset.Icc 1 (1 - 2 : ℕ) = ∅ by decide, Finset.sum_empty] at h

example : (flattenedPermRunCount 2 2 : ℤ) = 0 := by
  have h := flattenedPermRunCount_recursion.1 2 2 (by decide) (by decide)
  rwa [show Finset.Icc 1 (2 - 2 : ℕ) = ∅ by decide, Finset.sum_empty] at h

example : flattenedPermRunCount 5 1 = 1 :=
  flattenedPermRunCount_recursion.2.1 5 (by decide)

example : flattenedPermRunCount 4 4 = 0 :=
  flattenedPermRunCount_recursion.2.2 4 4 (by decide) (by decide)

-- The first nonempty recurrence has two label choices minus the terminal one.
private theorem count_three_two : (flattenedPermRunCount 3 2 : ℤ) = 1 := by
  have h := flattenedPermRunCount_recursion.1 3 2 (by decide) (by decide)
  rw [show Finset.Icc 1 (3 - 2 : ℕ) = {1} by decide, Finset.sum_singleton,
    show 2 - 1 = (1 : ℕ) by decide, flattenedPermRunCount_recursion.2.1 1 (by decide)] at h
  exact h.trans (by decide)

example : flattenedPermRunCount 3 2 = 1 := by decide

-- This instance uses a suffix with two runs, not just increasing suffixes.
example : (flattenedPermRunCount 5 3 : ℤ) = 3 := by
  have h := flattenedPermRunCount_recursion.1 5 3 (by decide) (by decide)
  rw [show Finset.Icc 1 (5 - 2 : ℕ) = {1, 2, 3} by decide,
    Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_singleton,
    show 3 - 1 = (2 : ℕ) by decide, count_one_two,
    flattenedPermRunCount_recursion.2.2 2 2 (by decide) (by decide), count_three_two] at h
  exact h.trans (by decide)
