/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Combinatorics.Additive.UnionTwoAPNotMSTDNotIsMSTDSetIntervalAPNatOfTwoMulSubOneLe

namespace MathlibExtTest.Combinatorics.Additive.UnionTwoAPNotMSTDNotIsMSTDSetIntervalAPNatOfTwoMulSubOneLe

open MetaMathlibExt

-- The smallest allowed parameters: `n = 3`, `m = 2`, `d = 2`, `x = 5 = 2 * n - 1`.
example : ¬ IsMSTDSet (realIntervalSet 3 ∪ realAPSet ((5 : ℕ) : ℝ) 2 ((2 : ℕ) : ℝ)) :=
  not_isMSTDSet_intervalAP_nat_of_two_mul_sub_one_le 3 2 2 5 (by decide) (by decide)
    (by decide) (by decide)

-- A larger gap and step: `n = 4`, `m = 3`, `d = 5`, `x = 9 ≥ 2 * n - 1`.
example : ¬ IsMSTDSet (realIntervalSet 4 ∪ realAPSet ((9 : ℕ) : ℝ) 3 ((5 : ℕ) : ℝ)) :=
  not_isMSTDSet_intervalAP_nat_of_two_mul_sub_one_le 4 3 5 9 (by decide) (by decide)
    (by decide) (by decide)

end MathlibExtTest.Combinatorics.Additive.UnionTwoAPNotMSTDNotIsMSTDSetIntervalAPNatOfTwoMulSubOneLe
