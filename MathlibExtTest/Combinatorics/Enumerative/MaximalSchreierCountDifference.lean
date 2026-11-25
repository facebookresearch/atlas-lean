/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Combinatorics.Enumerative.MaximalSchreierCountDifference

/-!
# Tests for maximal $(1, q)$-Schreier sets and differences of Schreier counts
-/

open MetaMathlibExt

-- With `|S^{1/3}_4| = 7` and `|S^{1/3}_5| = 12` this gives `|M^{1/3}_4| = 2`, as in the
-- paper's Table 2: the maximal sets are `{1, 2, 4}` and `{1, 3, 4}`.
example : (maximalSchreierCount 1 3 4 : ℤ) = 2 := by
  rw [maximalSchreierCount_eq_two_mul_sub (by decide) (by decide)]
  decide +kernel

-- At the smallest index `n = 1` there is no maximal `(1, 2)`-Schreier set, since `2 * 1 ≠ 1`.
example : (maximalSchreierCount 1 2 1 : ℤ) = 0 := by
  rw [maximalSchreierCount_eq_two_mul_sub (by decide) le_rfl]
  decide +kernel

-- The hypothesis `1 ≤ n` is needed: at `n = 0` the right side is `2 * 0 - 1 = -1`.
example :
    (maximalSchreierCount 1 2 0 : ℤ) ≠ 2 * schreierCount 1 2 0 - schreierCount 1 2 1 := by
  decide +kernel
