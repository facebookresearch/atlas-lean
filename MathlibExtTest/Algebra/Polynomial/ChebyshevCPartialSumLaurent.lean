/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Algebra.Polynomial.ChebyshevCPartialSumLaurent

/-! # Tests for the Laurent polynomial identity for Chebyshev partial sums -/

open LaurentPolynomial MetaMathlibExt Polynomial

-- The two subtracted monomials both contribute to the constant term exactly at r = 0.
example (r : ℕ) :
    (T (-1) * (T 1 - 1) ^ 2 *
      aeval (T 1 + T (-1) : LaurentPolynomial ℤ) (chebyshevCPartialSum r)).coeff 0 =
        if r = 0 then -2 else 0 := by
  rw [← chebyshevCPartialSum_laurent_identity]
  simp only [AddMonoidAlgebra.coeff_add, AddMonoidAlgebra.coeff_sub, Finsupp.add_apply,
    Finsupp.sub_apply, T_apply]
  split_ifs <;> omega
