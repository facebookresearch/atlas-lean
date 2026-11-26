/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Combinatorics.Enumerative.RascalNumberIdentities

namespace MathlibExt.Combinatorics.Enumerative.RascalNumbersWanted

-- With `ℓ = u = 1` the generalized recurrence is the diamond recurrence of Angorro et al.
example (n k : ℤ) (h1 : 1 ≤ k) (h2 : k ≤ n - 1) :
    rascalZ n k * rascalZ (n - 2) (k - 1) =
      rascalZ (n - 1) k * rascalZ (n - 1) (k - 1) + 1 := by
  simpa [sub_sub] using
    rascalZ_mul_eq n k 1 1 zero_le_one zero_le_one h1 h2

-- Fleron's recurrence fails at the end `k = 0` of a row: the right side is `2`.
example : rascalZ 3 0 ≠ rascalZ 2 0 + rascalZ 2 (-1) - rascalZ 1 (-1) + 1 := by decide

-- The row-shift identity fails without `k ≤ n`.
example : rascalZ (0 + 1) 2 ≠ rascalZ 0 2 + rascalZ (1 + 2) 2 - 1 := by decide

-- Row 4 is `1, 4, 5, 4, 1`.
example : ∑ k ∈ Finset.range (4 + 1), rascalZ ((4 : ℕ) : ℤ) (k : ℤ) = 15 := by
  rw [sum_rascalZ_row]
  decide

-- Column 0 is constant: every `R_{i,0}` is `1`.
example (r : ℕ) :
    ∑ i ∈ Finset.range (r + 1), rascalZ ((0 + i : ℕ) : ℤ) ((0 : ℕ) : ℤ) = r + 1 := by
  simpa using sum_rascalZ_column 0 r

-- At `n = 2` the binomial-weighted row sum is `1 + 2 * 2 + 1 = 6`; the printed exponent
-- `n - 2` would give `5`.
example :
    2 * ∑ k ∈ Finset.range (2 + 1), (Nat.choose 2 k : ℤ) * rascalZ ((2 : ℕ) : ℤ) (k : ℤ) =
      2 * 6 := by
  rw [two_mul_sum_choose_mul_rascalZ]
  decide

-- The interior of rows 2 to 4 is `2`, then `3, 3`, then `4, 5, 4`.
example :
    ∑ i ∈ Finset.Icc (1 : ℕ) 4, ∑ j ∈ Finset.Icc (1 : ℕ) (i - 1), rascalZ (i : ℤ) (j : ℤ) =
      21 := by
  rw [sum_sum_rascalZ 4 (by decide)]
  decide

-- Row 4 alternates to `1 - 4 + 5 - 4 + 1 = -1`, and row 5 to `0`.
example :
    ∑ k ∈ Finset.range (2 * 2 + 1), (-1 : ℤ) ^ k * rascalZ ((2 * 2 : ℕ) : ℤ) (k : ℤ) =
      -1 := by
  rw [sum_rascalZ_alternating_even]
  decide

example :
    ∑ k ∈ Finset.range (2 * 2 + 2), (-1 : ℤ) ^ k * rascalZ ((2 * 2 + 1 : ℕ) : ℤ) (k : ℤ) =
      0 :=
  sum_rascalZ_alternating_odd 2

-- `(R_{5,1} - 1) (R_{5,2} - 1) = 4 * 6`, which is `2! * (4 * 3)` and `(2!) ^ 2 * C(4, 2)`.
example : ∏ k ∈ Finset.Icc (1 : ℕ) 2, (rascalZ ((5 : ℕ) : ℤ) (k : ℤ) - 1) = 24 := by
  rw [prod_rascalZ_sub_one_eq_factorial_mul 5 2 (by decide) (by decide)]
  decide

example : ∏ k ∈ Finset.Icc (1 : ℕ) 2, (rascalZ ((5 : ℕ) : ℤ) (k : ℤ) - 1) = 24 := by
  rw [← factorial_sq_mul_choose_eq_prod 5 2 (by decide) (by decide)]
  decide

-- At `m = n` the product vanishes, since `R_{n,n} = 1`.
example (n : ℕ) (hn : 1 ≤ n) :
    ∏ k ∈ Finset.Icc 1 n, (rascalZ (n : ℤ) (k : ℤ) - 1) = 0 := by
  rw [← factorial_sq_mul_choose_eq_prod n n hn le_rfl, Nat.choose_eq_zero_of_lt (by omega)]
  simp

end MathlibExt.Combinatorics.Enumerative.RascalNumbersWanted
