/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Combinatorics.Enumerative.ArndtNegativeEven

/-! # Tests for negative even shifts in Arndt composition counts -/

open MetaMathlibExt

-- The empty composition contributes one.
example : kArndtTotalCount (-2) 0 = 1 := by
  exact (kArndtTotalCount_neg_even 1 0 (hj := by decide)).trans (by decide)

-- The part 4 is excluded at cutoff 2 and allowed at cutoff 4.
example : oddOrSmallEvenCompositionCount 1 4 = 7 ∧ oddOrSmallEvenCompositionCount 2 4 = 8 := by
  decide

example : kArndtTotalCount (-2) 4 = 7 := by
  exact (kArndtTotalCount_neg_even 1 4 (hj := by decide)).trans (by decide)
