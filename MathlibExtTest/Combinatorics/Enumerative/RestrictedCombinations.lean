/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Combinatorics.Enumerative.RestrictedCombinations

-- With no forbidden differences, the count is the binomial coefficient.
example : MetaMathlibExt.restrictedCombinationCount ∅ 3 2 = 3 := by decide

-- The 2-subsets of `{1, 2, 3, 4}` with no two elements differing by `2`.
example : MetaMathlibExt.restrictedCombinationCount {2} 4 2 = 4 := by decide

-- The same count as tilings of a `6`-board, shifted by the largest forbidden difference.
example : MetaMathlibExt.restrictedOverlapTilingCount {2} 6 2 = 4 := by decide

-- No two consecutive elements: the 2-subsets of `{1, 2, 3, 4}`.
example : MetaMathlibExt.restrictedCombinationCount {1} 4 2 = 3 := by decide

-- The empty tiling is the only tiling of the empty board.
example : MetaMathlibExt.restrictedOverlapTilingCount {1} 0 0 = 1 := by decide

-- The coefficient of `x ^ 2` on the left of the generating-function identity for `Q = {1}`:
-- the subsets of `{1}` with no two consecutive elements give `1 + y`.
example :
    PowerSeries.coeff 2 (PowerSeries.X ^ ({1} : Finset ℕ).sup id * PowerSeries.mk
      (fun n => ∑ k ∈ Finset.range (n + 1),
        (MetaMathlibExt.restrictedCombinationCount {1} n k : Polynomial ℤ) *
          Polynomial.X ^ k)) = 1 + Polynomial.X := by
  have h0 : MetaMathlibExt.restrictedCombinationCount {1} 1 0 = 1 := by decide
  have h1 : MetaMathlibExt.restrictedCombinationCount {1} 1 1 = 1 := by decide
  rw [PowerSeries.coeff_X_pow_mul']
  simp only [show (({1} : Finset ℕ).sup id) = 1 by decide,
    show (1 : ℕ) ≤ 2 by decide, ↓reduceIte]
  simp only [PowerSeries.coeff_mk]
  rw [Finset.sum_range_succ, Finset.sum_range_one]
  simp [h0, h1]

-- The coefficient of `x ^ 2` on the right of the generating-function identity for `Q = {1}`:
-- the tilings of a `2`-board with dominoes give `1 + y`.
example :
    PowerSeries.coeff 2 (PowerSeries.mk (fun n => ∑ k ∈ Finset.range (n + 1),
        (MetaMathlibExt.restrictedOverlapTilingCount {1} n k : Polynomial ℤ) *
          Polynomial.X ^ k) -
        ∑ n ∈ Finset.range (({1} : Finset ℕ).sup id), PowerSeries.X ^ n) =
      1 + Polynomial.X := by
  have h0 : MetaMathlibExt.restrictedOverlapTilingCount {1} 2 0 = 1 := by decide
  have h1 : MetaMathlibExt.restrictedOverlapTilingCount {1} 2 1 = 1 := by decide
  have h2 : MetaMathlibExt.restrictedOverlapTilingCount {1} 2 2 = 0 := by decide
  rw [map_sub, PowerSeries.coeff_mk]
  simp only [show (({1} : Finset ℕ).sup id) = 1 by decide, Finset.sum_range_one,
    pow_zero, PowerSeries.coeff_one, show (2 : ℕ) ≠ 0 by decide, ↓reduceIte]
  rw [Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_one]
  simp [h0, h1, h2]
