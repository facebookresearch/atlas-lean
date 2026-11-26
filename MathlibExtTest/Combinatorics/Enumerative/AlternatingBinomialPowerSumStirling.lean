/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Combinatorics.Enumerative.AlternatingBinomialPowerSumStirling

open Finset MetaMathlibExt

-- At order zero only the term `j = 0` of the expansion survives (`S(0, 0) = 1`, `0 ^ 0 = 1`).
example (x y : ℂ) (ℓ : ℕ) :
    ∑ j ∈ Icc 0 ℓ, (ℓ.choose j : ℂ) * (-1) ^ 0 * ((0 : ℕ).factorial : ℂ) *
      (Nat.stirlingSecond j 0 : ℂ) * x ^ j * y ^ (ℓ - j) = y ^ ℓ := by
  rw [← (alternatingBinomialPowerSum_eq_sum_stirlingSecond x y ℓ 0).1]
  simp [alternatingBinomialPowerSum]

-- The expansion at `ℓ = 3`, `m = 2` uses `S(2, 2) = 1` and `S(3, 2) = 3` ...
example (x y : ℂ) : alternatingBinomialPowerSum 3 2 x y = 6 * x ^ 2 * y + 6 * x ^ 3 := by
  rw [(alternatingBinomialPowerSum_eq_sum_stirlingSecond x y 3 2).1,
    show Icc 2 3 = {2, 3} by decide, sum_pair (by decide)]
  simp [Nat.stirlingSecond, Nat.factorial, Nat.choose]
  ring

-- ... and agrees with the defining sum `y ^ 3 - 2 (x + y) ^ 3 + (2 x + y) ^ 3`.
example (x y : ℂ) : alternatingBinomialPowerSum 3 2 x y = 6 * x ^ 2 * y + 6 * x ^ 3 := by
  simp [alternatingBinomialPowerSum, sum_range_succ]
  ring

-- Below the diagonal the sum vanishes: `y - 2 (x + y) + (2 x + y) = 0`.
example (x y : ℂ) : alternatingBinomialPowerSum 1 2 x y = 0 :=
  (alternatingBinomialPowerSum_eq_sum_stirlingSecond x y 1 2).2.1 (by decide)

-- The diagonal value at `m = 0` is `p_{0,0}(x, y) = 1`, by the convention `0 ^ 0 = 1`.
example (x y : ℂ) : alternatingBinomialPowerSum 0 0 x y = 1 := by
  simpa using (alternatingBinomialPowerSum_eq_sum_stirlingSecond x y 0 0).2.2
