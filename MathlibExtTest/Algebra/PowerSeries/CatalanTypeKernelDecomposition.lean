/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Algebra.PowerSeries.CatalanTypeKernelDecomposition

/-! # Tests for the Catalan-type kernel decomposition -/

open MetaMathlibExt PowerSeries

-- The constant coefficient is unaffected by `A`, even for `j = m = 0`.
example (a b c lam x y : ℝ) (A : Polynomial ℤ) :
    let K := trinomialNegPowSeries lam c (a * x) (b * (2 * x - 1) ^ 0) 0
    let S : PowerSeries ℝ :=
      PowerSeries.mk fun i ↦ if 0 ≤ i ∧ 0 ∣ i - 0 then y ^ i / (i.factorial : ℝ) else 0
    let At : PowerSeries ℝ := C (Polynomial.aeval x A) * X
    coeff 0 ((S + At) * K) = coeff 0 K := by
  intro K S At
  rw [coeff_catalanTypeKernel_decomposition 0 0 0 0 0 a b c lam x y A]
  change coeff 0 (S * K) + coeff 0 ((1 + At) * K) - coeff 0 K = coeff 0 K
  norm_num [S, At, coeff_mul, Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk,
    Finset.sum_range_succ, coeff_mk, coeff_C_mul, coeff_X, coeff_one]

-- In degree one the pseudo-Bessel term contributes `3` and the polynomial term contributes `2`.
-- The kernel `1 - X` has a nonzero linear coefficient, so the subtracted term matters as well.
example :
    let K := trinomialNegPowSeries (-1) 1 (1 * 1) (0 * (2 * 1 - 1) ^ 0) 1
    let S : PowerSeries ℝ :=
      PowerSeries.mk fun i ↦ if 1 ≤ i ∧ 2 ∣ i - 1 then (3 : ℝ) ^ i / (i.factorial : ℝ) else 0
    let At : PowerSeries ℝ := C (Polynomial.aeval (1 : ℝ) (Polynomial.X + 1 : Polynomial ℤ)) * X
    coeff 1 ((S + At) * K) = 5 := by
  intro K S At
  rw [coeff_catalanTypeKernel_decomposition 2 1 1 0 1 1 0 1 (-1) 1 3 (Polynomial.X + 1)]
  change coeff 1 (S * K) + coeff 1 ((1 + At) * K) - coeff 1 K = 5
  have hK : K = 1 - X := by
    dsimp [K]
    rw [trinomialNegPowSeries_neg_one _ _ one_ne_zero]
    simp
  rw [hK]
  norm_num [S, At, coeff_mul, Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk,
    Finset.sum_range_succ, coeff_mk, coeff_C_mul, coeff_X, coeff_one]
