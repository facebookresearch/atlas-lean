/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.NumberTheory.Bernoulli.SumModPrime

namespace MetaMathlibExt

open Finset

-- For `p = 5` the sum is `5 (1 - 1/2 + 1/6 + 0 - 1/30 + 0) = 19/6`.
example : ∑ j ∈ range (5 + 1), ((5 : ℕ) : ℚ) * bernoulli j = 19 / 6 := by
  simp only [sum_range_succ, sum_range_zero, bernoulli_zero, bernoulli_one, bernoulli_two,
    bernoulli_eq_bernoulli'_of_ne_one (show 3 ≠ 1 by decide), bernoulli'_three,
    bernoulli_eq_bernoulli'_of_ne_one (show 4 ≠ 1 by decide), bernoulli'_four,
    bernoulli_eq_zero_of_odd (show Odd 5 by decide) (by decide)]
  norm_num

-- Its denominator `6` is prime to `5`, and `19 * 6⁻¹ = 4 * 1 = -1` in `ZMod 5`, as predicted.
example : ratResidue 5 (19 / 6) = ratResidue 5 (-1) := by
  rw [ratResidue, show (19 / 6 : ℚ).num = 19 by norm_num, show (19 / 6 : ℚ).den = 6 by norm_num,
    ZMod.inv_eq_of_mul_eq_one 5 _ 1 (by decide), show (-1 : ℚ) = ((-1 : ℤ) : ℚ) by norm_num,
    ratResidue_intCast]
  decide

-- The theorem at `p = 7`, read through `ratResidue_intCast`: the residue of the sum is `6`.
example : ratResidue 7 (∑ j ∈ range (7 + 1), ((7 : ℕ) : ℚ) * bernoulli j) = 6 := by
  rw [(sum_prime_mul_bernoulli_mod_prime 7 (by decide) (by decide)).2,
    show (-1 : ℚ) = ((-1 : ℤ) : ℚ) by norm_num, ratResidue_intCast]
  decide

-- The hypothesis `p ≠ 2` is needed: for `p = 2` the sum is `2 (1 - 1/2 + 1/6) = 4/3`, whose
-- residue modulo `2` is `0`, while that of `-1` is `1`.
example :
    ratResidue 2 (∑ j ∈ range (2 + 1), ((2 : ℕ) : ℚ) * bernoulli j) ≠ ratResidue 2 (-1) := by
  rw [show ∑ j ∈ range (2 + 1), ((2 : ℕ) : ℚ) * bernoulli j = 4 / 3 by
      simp only [sum_range_succ, sum_range_zero, bernoulli_zero, bernoulli_one, bernoulli_two]
      norm_num,
    ratResidue, show (4 / 3 : ℚ).num = 4 by norm_num, show (4 / 3 : ℚ).den = 3 by norm_num,
    show (-1 : ℚ) = ((-1 : ℤ) : ℚ) by norm_num, ratResidue_intCast,
    ZMod.inv_eq_of_mul_eq_one 2 _ 1 (by decide)]
  decide

end MetaMathlibExt
