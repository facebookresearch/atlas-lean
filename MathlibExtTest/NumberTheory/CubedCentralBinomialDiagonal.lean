/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.NumberTheory.CubedCentralBinomialDiagonal
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Ring

/-! # Tests for cubed central binomial coefficients as diagonal coefficients -/

open MathlibExt.NumberTheory.OeisA002897Wanted MvPolynomial

-- At zero the exponent vector is empty and the whole product is the constant one.
example : (pPoly 0).coeff (xyzPowN 0) = 1 := by
  have h : xyzPowN 0 = 0 := by ext; rfl
  simp [pPoly, h]

-- Extract the coefficient of xyz directly from the quartic.
example : (pPoly 1).coeff (xyzPowN 1) = 8 := by
  unfold pPoly
  ring_nf
  simp only [X_pow_eq_monomial]
  simp only [X, ← map_ofNat (C : ℤ →+* MvPolynomial Vars ℤ), C_apply, monomial_mul_monomial,
    add_zero, one_mul, mul_one, AddMonoidAlgebra.coeff_add, AddMonoidAlgebra.coeff_sub]
  simp [AddMonoidAlgebra.one_def, xyzPowN, Finsupp.ext_iff, Fin.forall_fin_succ]

-- Use the theorem with the explicit exponent vector for x²y²z².
example : (pPoly 2).coeff (Finsupp.single 0 2 + Finsupp.single 1 2 + Finsupp.single 2 2) = 216 := by
  have h : Finsupp.single 0 2 + Finsupp.single 1 2 + Finsupp.single 2 2 = xyzPowN 2 := by
    ext v
    fin_cases v <;> simp [xyzPowN]
  rw [h, ← a_eq_coeff_holds 2]
  decide
