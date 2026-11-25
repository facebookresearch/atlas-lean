/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Combinatorics.Enumerative.TrinomialDiagonalTribonacci
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

open MetaMathlibExt

-- At `n = 0` the correction sum is empty and the centre is the entire diagonal.
example : (∑ k ∈ Finset.range (0 + 1), (trinomialCoefficient (0 + k) (0 - k) : ℚ)) = 1 := by
  rw [sum_trinomialCoefficient_add_sub_eq_tribonacci]
  norm_num [tribonacci, trinomialCoefficient_zero_zero]

-- At `n = 1` the correction has a single term, involving `T₂ + T₀`.
example : (∑ k ∈ Finset.range (1 + 1), (trinomialCoefficient (1 + k) (1 - k) : ℚ)) = 2 := by
  rw [sum_trinomialCoefficient_add_sub_eq_tribonacci]
  norm_num [tribonacci, trinomialCoefficient_zero_zero, trinomialCoefficient_one_one]

-- At `n = 2` the correction contains two central coefficients and the diagonal has three entries.
private theorem central_two : trinomialCoefficient 2 2 = 3 := by
  have h : (1 + Polynomial.X + Polynomial.X ^ 2 : Polynomial ℕ) ^ 2 =
      1 + Polynomial.X + Polynomial.X + 3 * Polynomial.X ^ 2 +
        Polynomial.X ^ 3 + Polynomial.X ^ 3 + Polynomial.X ^ 4 := by ring
  rw [trinomialCoefficient, h]
  norm_num [Polynomial.coeff_X_pow, Polynomial.coeff_X, Polynomial.coeff_one]

example : (∑ k ∈ Finset.range (2 + 1), (trinomialCoefficient (2 + k) (2 - k) : ℚ)) = 7 := by
  rw [sum_trinomialCoefficient_add_sub_eq_tribonacci]
  norm_num [Finset.sum_range_succ, tribonacci, trinomialCoefficient_zero_zero,
    trinomialCoefficient_one_one, central_two]
