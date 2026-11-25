/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.NumberTheory.DelannoyBinomialSum

open MathlibExt.NumberTheory.DelannoyTriangleWanted MetaMathlibExt

-- At k = 0 the only summand contains the out-of-range coefficient 0.choose 1.
example : (binomialPowerSeq 1 1 1 : ℤ) = 3 * (binomialPowerSeq 1 1 0 : ℤ) := by
  apply sub_eq_zero.mp
  exact (sum_choose_choose_binomialPowerSeq 0).symm.trans (by decide)

-- At k = 2 both positive-index terms contribute, and the weighted sum is 63 - 3 * 13.
example : 4 * (∑ j ∈ Finset.range 3, (Nat.choose 2 j * Nat.choose (2 + j) 3 : ℤ)) = 24 := by
  rw [sum_choose_choose_binomialPowerSeq 2]
  decide
