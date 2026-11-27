/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.NumberTheory.RadicalCoefficientGcdStep
import Mathlib.Algebra.Polynomial.RingDivision
import Mathlib.Tactic.NormNum

open MetaMathlibExt

private def degreeOneCoeffs (c : ℤ) (n : ℕ) (_ : Fin 1) : ℤ := c ^ n

-- In degree one the gcd is the sole coefficient, here growing from 5 to 25.
example : Finset.univ.gcd (degreeOneCoeffs 5 1) ∣ Finset.univ.gcd (degreeOneCoeffs 5 2) := by
  exact gcd_radical_expansion_coeffs_dvd_succ (N := 1) (u := 3) (v := 2)
    (by simpa using Polynomial.irreducible_X_sub_C (2 : ℚ))
    (degreeOneCoeffs 5)
    (by intro n _; norm_num [degreeOneCoeffs, Fin.sum_univ_one, Real.rpow_one]) 1 (by decide)

-- The theorem also applies when the coefficient gcd is zero.
example : Finset.univ.gcd (degreeOneCoeffs 0 1) ∣ Finset.univ.gcd (degreeOneCoeffs 0 2) := by
  exact gcd_radical_expansion_coeffs_dvd_succ (N := 1) (u := 0) (v := 0)
    (by simpa using Polynomial.irreducible_X_sub_C (0 : ℚ))
    (degreeOneCoeffs 0)
    (by intro n _; norm_num [degreeOneCoeffs, Fin.sum_univ_one, Real.rpow_one]) 1 (by decide)
