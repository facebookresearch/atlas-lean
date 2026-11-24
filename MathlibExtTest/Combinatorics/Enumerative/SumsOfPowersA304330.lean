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

-- Even the last binomial coefficient vanishes when k exceeds twice the upper endpoint.
example (k n : ℕ) (hn : 1 ≤ n) (hk : 2 * n < k) :
    (∑ i ∈ Finset.Icc 1 n, (2 * i) * (2 * i + k - 1).choose (2 * k - 1)) = 0 := by
  rw [sum_two_mul_choose_eq k n (by omega) hn,
    Nat.choose_eq_zero_of_lt (show 2 * n + k + 1 < 2 * k + 1 by omega), mul_zero]

-- At k = 2n, the final summand is the first nonzero one.
example (n : ℕ) (hn : 1 ≤ n) :
    (∑ i ∈ Finset.Icc 1 n, (2 * i) * (2 * i + 2 * n - 1).choose (2 * (2 * n) - 1)) =
      2 * n := by
  rw [sum_two_mul_choose_eq (2 * n) n (by omega) hn, ← two_mul (2 * n), Nat.choose_self, mul_one]

-- Every term vanishes below the first nonzero binomial coefficient.
example (k n : ℕ) (hn : 1 ≤ n) (hnk : n < k) :
    (∑ i ∈ Finset.Icc 1 n, (i : ℚ) * (i + k - 1).choose (2 * k - 1)) = 0 := by
  rw [sum_mul_choose_eq k n (by omega) hn, Nat.choose_eq_zero_of_lt (show n + k < 2 * k by omega)]
  simp

-- At k = 2 and n = 3, the prefactor is 14/5 and the binomial coefficient is 5.
example : (∑ i ∈ Finset.Icc 1 (3 : ℕ), (i : ℚ) * (i + 2 - 1).choose 3) = 14 := by
  rw [sum_mul_choose_eq 2 3 (by decide) (by decide)]
  norm_num [Nat.choose]

-- The first row covered by the theorem has two nonzero entries.
example : arrayR 2 1 = 1 ∧ arrayR 2 2 = 12 ∧ arrayR 2 3 = 0 := by decide

-- At k = 1 the only summand survives, so the lower bound is sharp.
example : (∑ m ∈ Finset.Icc 1 (1 : ℕ),
    (-1 : ℚ) ^ m * ((Nat.factorial (m - 1) : ℚ) ^ 2 / ((2 * m).factorial : ℚ)) *
      (arrayR 1 m : ℚ)) = -1 / 2 := by
  norm_num [show arrayR 1 1 = 1 by decide, Nat.factorial]

end MathlibExt.Combinatorics.Enumerative.SumsOfPowersA304330Wanted
