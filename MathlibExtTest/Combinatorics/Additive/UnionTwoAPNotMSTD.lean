/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Combinatorics.Additive.UnionTwoAPNotMSTD

namespace MathlibExtTest.Combinatorics.Additive.UnionTwoAPNotMSTD

open MetaMathlibExt

-- Smallest case: `I_3 ∪ {4, 6, 8}`.
example : ¬ IsMSTDSet (realIntervalSet 3 ∪ realAPSet ((4 : ℕ) : ℝ) 2 ((2 : ℕ) : ℝ)) :=
  not_isMSTDSet_intervalAP_nat_of_le_two_mul_sub_two 3 2 2 4
    (by decide) (by decide) (by decide) (by decide) (by decide)

-- Larger gap and step: `I_5 ∪ {8, 12, 16, 20}`.
example : ¬ IsMSTDSet (realIntervalSet 5 ∪ realAPSet ((8 : ℕ) : ℝ) 3 ((4 : ℕ) : ℝ)) :=
  not_isMSTDSet_intervalAP_nat_of_le_two_mul_sub_two 5 3 4 8
    (by decide) (by decide) (by decide) (by decide) (by decide)

-- Start strictly inside the window `[6, 8]`, with disjoint cross-sum blocks:
-- `I_5 ∪ {7, 12, 17}`.
example : ¬ IsMSTDSet (realIntervalSet 5 ∪ realAPSet ((7 : ℕ) : ℝ) 2 ((5 : ℕ) : ℝ)) :=
  not_isMSTDSet_intervalAP_nat_of_le_two_mul_sub_two 5 2 5 7
    (by decide) (by decide) (by decide) (by decide) (by decide)

end MathlibExtTest.Combinatorics.Additive.UnionTwoAPNotMSTD
