/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.NumberTheory.FranelDiagonalCoeff
import Mathlib.Tactic.NormNum

/-! # Tests for Franel numbers as diagonal coefficients -/

open MvPolynomial MathlibExt.NumberTheory.OeisA265233Wanted

-- For `m = 0` the polynomial is `1`, whose constant coefficient is `f_0 = 1`.
example :
    ((((X 0 + X 1) * (X 1 + X 2) * (X 2 + X 0)) ^ 0 : MvPolynomial (Fin 3) ℚ)).coeff
      (Finsupp.single 0 0 + Finsupp.single 1 0 + Finsupp.single 2 0) = 1 := by
  rw [coeff_pow_eq_franel, show MetaMathlibExt.binomialPowerSeq 3 0 0 = 1 by rfl]
  norm_num

-- For `m = 1` the theorem gives the coefficient `f_1 = 2` of `xyz` in `(x + y)(y + z)(z + x)`.
example :
    ((X 0 + X 1) * (X 1 + X 2) * (X 2 + X 0) : MvPolynomial (Fin 3) ℚ).coeff
      (Finsupp.single 0 1 + Finsupp.single 1 1 + Finsupp.single 2 1) = 2 := by
  rw [← pow_one ((X 0 + X 1) * (X 1 + X 2) * (X 2 + X 0) : MvPolynomial (Fin 3) ℚ),
    coeff_pow_eq_franel, show MetaMathlibExt.binomialPowerSeq 3 0 1 = 2 by rfl]
  norm_num

-- The same coefficient by direct expansion, without the theorem: of the eight products of
-- variables, `x * y * z` and `y * z * x` are the two equal to `xyz`.
example :
    ((X 0 + X 1) * (X 1 + X 2) * (X 2 + X 0) : MvPolynomial (Fin 3) ℚ).coeff
      (Finsupp.single 0 1 + Finsupp.single 1 1 + Finsupp.single 2 1) = 2 := by
  simp only [add_mul, mul_add, X, monomial_mul_monomial, mul_one, AddMonoidAlgebra.coeff_add,
    Finsupp.add_apply, coeff_monomial]
  simp [Finsupp.ext_iff, Fin.forall_fin_succ]
  norm_num

-- The next diagonal coefficients are the Franel numbers `f_2 = 10` and `f_3 = 56`.
example :
    ((((X 0 + X 1) * (X 1 + X 2) * (X 2 + X 0)) ^ 2 : MvPolynomial (Fin 3) ℚ)).coeff
      (Finsupp.single 0 2 + Finsupp.single 1 2 + Finsupp.single 2 2) = 10 := by
  rw [coeff_pow_eq_franel, show MetaMathlibExt.binomialPowerSeq 3 0 2 = 10 by rfl]
  norm_num

example :
    ((((X 0 + X 1) * (X 1 + X 2) * (X 2 + X 0)) ^ 3 : MvPolynomial (Fin 3) ℚ)).coeff
      (Finsupp.single 0 3 + Finsupp.single 1 3 + Finsupp.single 2 3) = 56 := by
  rw [coeff_pow_eq_franel, show MetaMathlibExt.binomialPowerSeq 3 0 3 = 56 by rfl]
  norm_num
