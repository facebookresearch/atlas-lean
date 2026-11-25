/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Combinatorics.Additive.BoundedSubsequenceSums

open MetaMathlibExt

-- Two actual zeros and two padding zeros allow a single 3 to represent a five-term sum.
-- A sum of zero would require five zeros and exceeds the cap.
example : boundedSubsequenceSums 3 0
    (repetitionSequence (Fin.cons 0 ![(3 : ℤ)]) ![2, 3]) = {3, 6, 9} := by
  rw [boundedSubsequenceSums_eq_generalizedHFoldSumset_of_zero_mem _ (by decide) (by decide)
    _ (by decide) 5 (by decide) 3 0 (by decide) (by decide) (by decide)]
  decide

-- At the exact-length boundary, only the two original zeros are available.
example : boundedSubsequenceSums 2 3
    (repetitionSequence (Fin.cons 0 ![(3 : ℤ)]) ![2, 3]) = {0, 3, 6} := by
  rw [boundedSubsequenceSums_eq_generalizedHFoldSumset_of_zero_mem _ (by decide) (by decide)
    _ (by decide) 5 (by decide) 2 3 (by decide) (by decide) (by decide)]
  decide

-- Only lengths two and three contribute, with at most two copies of either term.
example : boundedSubsequenceSums 2 1
    (repetitionSequence ![(2 : ℤ), -3] ![2, 2]) = {-6, -4, -1, 1, 4} := by
  rw [boundedSubsequenceSums_eq_generalizedHFoldSumset_of_zero_not_mem _ (by decide) (by decide)
    _ (by decide) 4 (by decide) 2 1 (by decide) (by decide)]
  decide

-- With β = 0 the full sequence is allowed, and it is the only nonempty choice summing to zero.
example : boundedSubsequenceSums 1 0
    (repetitionSequence ![(-1 : ℤ), 2] ![2, 1]) = {-2, -1, 0, 1, 2} := by
  rw [boundedSubsequenceSums_eq_generalizedHFoldSumset_of_zero_not_mem _ (by decide) (by decide)
    _ (by decide) 3 (by decide) 1 0 (by decide) (by decide)]
  decide
