/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Algebra.Polynomial.ChebyshevCPartialSumTopCoeffs
import Mathlib.Tactic.NormNum

/-! # Tests for the leading coefficients of the Chebyshev partial sums -/

open Polynomial

namespace MetaMathlibExt

-- At `n = 5` both tails are empty: the leading terms give the entire polynomial.
example : chebyshevCPartialSum 5 = (X ^ 5 + X ^ 4 - 4 * X ^ 3 - 3 * X ^ 2 + 3 * X + 1 : ℤ[X]) := by
  ext k
  have h := (degree_lt_iff_coeff_zero _ _).mp (chebyshevCPartialSum_top_coeffs 5 (by decide)) k
    (Nat.zero_le k)
  rw [coeff_sub, sub_eq_zero] at h
  norm_num [Nat.choose] at h
  simpa using h

-- At `n = 6` the remainder need not vanish, but it is constant.
example : (chebyshevCPartialSum 6).coeff 1 = 3 := by
  have h := (degree_lt_iff_coeff_zero _ _).mp (chebyshevCPartialSum_top_coeffs 6 (by decide)) 1
    (by decide)
  rw [coeff_sub, sub_eq_zero] at h
  norm_num [Nat.choose, coeff_sub, coeff_add, coeff_X_pow, coeff_X] at h
  exact h

end MetaMathlibExt
