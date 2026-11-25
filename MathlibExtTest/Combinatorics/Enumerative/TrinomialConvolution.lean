/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Combinatorics.Enumerative.TrinomialConvolution
import Mathlib.Tactic.NormNum

open MetaMathlibExt

-- At shift -1 the first summand vanishes and the next two contribute.
example (n : ℕ) :
    trinomialCoefficient n 0 + trinomialCoefficient n 1 = trinomialCoefficient (n + 1) 1 := by
  have h := sum_trinomialCoefficient_convolution n 1 (-1)
  norm_num [Finset.sum_range_succ, trinomialCoefficient, Polynomial.coeff_add,
    Polynomial.coeff_one, Polynomial.coeff_X, Polynomial.coeff_X_pow] at h
  exact h

-- Below the first column even the last summand has negative index.
example (n m : ℕ) (l : ℤ) (hl : l < -(2 * (m : ℤ))) :
    ∑ k ∈ Finset.range (2 * m + 1),
        (if 0 ≤ l + k then trinomialCoefficient n (l + k).toNat else 0) *
          trinomialCoefficient m k = 0 := by
  rw [sum_trinomialCoefficient_convolution, ite_eq_right (by omega)]
