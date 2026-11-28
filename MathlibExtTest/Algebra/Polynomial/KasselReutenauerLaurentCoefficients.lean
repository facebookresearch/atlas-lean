/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Algebra.Polynomial.KasselReutenauerLaurentCoefficients

/-! # Tests for the absolute coefficient sum of the Kassel–Reutenauer Laurent polynomial -/

open LaurentPolynomial Polynomial

namespace MetaMathlibExt

-- At the smallest positive index, the two negative monomials have exponent zero.
example : ((T 1 - 2 + T (-1)) * aeval (T 1 + T (-1) : LaurentPolynomial ℤ)
    (kasselReutenauerPoly 1)).coeff.sum (fun _ c => |c|) = 4 := by
  rw [kasselReutenauer_C_abs_coeff_sum 1 (by decide)]
  decide

-- A power of two has only the trivial odd divisor despite its even divisors.
example : ((T 1 - 2 + T (-1)) * aeval (T 1 + T (-1) : LaurentPolynomial ℤ)
    (kasselReutenauerPoly 8)).coeff.sum (fun _ c => |c|) = 4 := by
  rw [kasselReutenauer_C_abs_coeff_sum 8 (by decide)]
  decide

-- With several odd divisors, both signs of the Chebyshev endpoints occur.
example : ((T 1 - 2 + T (-1)) * aeval (T 1 + T (-1) : LaurentPolynomial ℤ)
    (kasselReutenauerPoly 15)).coeff.sum (fun _ c => |c|) = 16 := by
  rw [kasselReutenauer_C_abs_coeff_sum 15 (by decide)]
  decide

end MetaMathlibExt
