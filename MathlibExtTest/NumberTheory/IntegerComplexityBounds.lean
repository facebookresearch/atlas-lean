/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.NumberTheory.IntegerComplexityBounds

open MathlibExt.NumberTheory.IntegerComplexityWanted

-- The convention at zero and the first positive value.
example : cx 0 = 0 := rfl
example : cx 1 = 1 := IntegerComplexity.complexity_one

-- One past the extremal value, in each of the three residue classes of the budget.
example : 2 < cx 3 := complexity_lt_of_gt_extremal 1 0 3 (by decide) (by decide) (by decide)
example : 6 < cx 10 := complexity_lt_of_gt_extremal 0 2 10 (by decide) (by decide) (by decide)
example : 7 < cx 13 := complexity_lt_of_gt_extremal 2 1 13 (by decide) (by decide) (by decide)

-- The two internal thresholds between consecutive powers of three.
example : [11, 12, 17, 18].map complexityLowerBoundG = [6, 7, 7, 8] := by decide

-- At two the lower bound equals the cost of the expression 1 + 1.
example : cx 2 = 2 :=
  Nat.le_antisymm (IntegerComplexity.complexity_le (e := .add .one .one) rfl)
    (complexityLowerBoundG_le 2 (by decide))

-- Each left endpoint has the lower bound for the interval it starts.
example : 6 ≤ cx 9 := complexityLowerBoundG_le 9 (by decide)
example : 7 ≤ cx 12 := complexityLowerBoundG_le 12 (by decide)
example : 8 ≤ cx 18 := complexityLowerBoundG_le 18 (by decide)
