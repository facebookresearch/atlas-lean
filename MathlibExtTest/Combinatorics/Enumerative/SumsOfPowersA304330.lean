/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import Mathlib.Tactic.NormNum
import MathlibExt.Combinatorics.Enumerative.SumsOfPowersA304330

namespace MathlibExt.Combinatorics.Enumerative.SumsOfPowersA304330Wanted

-- Every term vanishes below the first nonzero binomial coefficient.
example (k n : ℕ) (hn : 1 ≤ n) (hnk : n < k) :
    (∑ i ∈ Finset.Icc 1 n, (i : ℚ) * (i + k - 1).choose (2 * k - 1)) = 0 := by
  rw [sum_mul_choose_eq k n (by omega) hn, Nat.choose_eq_zero_of_lt (show n + k < 2 * k by omega)]
  simp

-- At k = 2 and n = 3, the prefactor is 14/5 and the binomial coefficient is 5.
example : (∑ i ∈ Finset.Icc 1 (3 : ℕ), (i : ℚ) * (i + 2 - 1).choose 3) = 14 := by
  rw [sum_mul_choose_eq 2 3 (by decide) (by decide)]
  norm_num [Nat.choose]

end MathlibExt.Combinatorics.Enumerative.SumsOfPowersA304330Wanted
