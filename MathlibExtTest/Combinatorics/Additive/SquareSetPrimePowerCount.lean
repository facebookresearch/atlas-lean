/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Combinatorics.Additive.SquareSetPrimePowerCount

/-! # Tests for counting nonzero squares modulo prime powers -/

open MetaMathlibExt

-- The even endpoint only contributes the unit layer modulo `3 ^ 2`.
example : (squareSet (3 ^ 2)).ncard = (unitSquareSet (3 ^ 2)).ncard := by
  simpa using (ncard_squareSet_primePower 3 2 (by decide) (by decide)).1 (by decide)

-- At odd exponent three the nonunit layer still survives, and reduces to the units' squares mod 2.
example : (squareSet (2 ^ 3)).ncard =
    (unitSquareSet (2 ^ 3)).ncard + (unitSquareSet (2 ^ 1)).ncard := by
  simpa [Finset.sum_range_succ] using
    (ncard_squareSet_primePower 2 3 (by decide) (by decide)).2 (by decide)

-- At exponent one there is just one layer.
example : (squareSet 2).ncard = (unitSquareSet 2).ncard := by
  simpa using (ncard_squareSet_primePower 2 1 (by decide) (by decide)).2 (by decide)
