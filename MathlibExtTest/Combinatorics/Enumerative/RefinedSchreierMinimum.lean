/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Combinatorics.Enumerative.RefinedSchreierMinimum

open MathlibExt.Combinatorics.Enumerative.SchreierTypeSetsWanted

-- At the least allowed minimum, the two largest parts are tied: 4 = 2 + 2.
example : partitionMinPartGapCount 4 2 2 0 = 1 := by
  rw [← refinedSchreierCardMinCount_eq 4 1 2 1 (by decide) (by decide) (by decide)]
  decide

-- A larger minimum gives a positive gap: {4, 5, 6} corresponds to 5 = 3 + 2.
example : partitionMinPartGapCount 5 2 2 1 = 1 := by
  rw [← refinedSchreierCardMinCount_eq 5 1 2 2 (by decide) (by decide) (by decide)]
  decide

-- The top gap must be exact: there is no partition of 5 into two equal parts.
example : partitionMinPartGapCount 5 2 2 0 = 0 := by
  rw [← refinedSchreierCardMinCount_eq 5 1 2 1 (by decide) (by decide) (by decide)]
  decide

-- With three parts and ℓ = 0, {2, 3, 4, 5} corresponds to 4 = 2 + 1 + 1.
example : partitionMinPartGapCount 4 1 3 1 = 1 := by
  rw [← refinedSchreierCardMinCount_eq 4 0 3 2 (by decide) (by decide) (by decide)]
  decide

-- A gap larger than the partition's total is impossible.
example : partitionMinPartGapCount 2 1 2 3 = 0 := by
  rw [← refinedSchreierCardMinCount_eq 2 0 2 4 (by decide) (by decide) (by decide)]
  decide
