/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Algebra.PowerSeries.UnifiedCatalanTypePolynomials

/-! # Tests for unified Catalan-type polynomials -/

open MetaMathlibExt PowerSeries

-- For m = 0 the defining sum has only its r = 0 term, also over a general real algebra.
example {A : Type*} [CommRing A] [Algebra ℝ A] (n : ℕ) (x y : A) :
    kampeDeFerietHermite 0 n x y = x ^ n := by
  simp [kampeDeFerietHermite, Nat.factorial_ne_zero]

-- The generating series is 1. For n ≥ 2, its coefficients satisfy P_{n-1} = 0,
-- so the sole nonzero recurrence coefficient lies strictly between the endpoints.
example (N : ℕ) (hN : 2 ≤ N) :
    hankelTransform (fun n ↦ coeff n (1 : PowerSeries ℝ)) N = 0 := by
  have hseries : trinomialNegPowSeries (-1) 1 1 1 1 = 1 := by
    rw [trinomialNegPowSeries_neg_one _ _ one_ne_zero]
    simp
  have h := det_catalanTypeHankel_eq_zero 1 N 2 (-1) 1 0 (fun k ↦ if k = 1 then 1 else 0)
  simp only [Nat.cast_one, map_zero, zero_mul, add_zero, one_mul, hseries] at h
  apply h hN ⟨1, by decide, by norm_num⟩
  intro n hn
  have hpos : n - 1 ≠ 0 := by omega
  simp [Finset.sum_range_succ, coeff_one, hpos]
