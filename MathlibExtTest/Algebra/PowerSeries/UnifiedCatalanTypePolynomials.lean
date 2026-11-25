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

-- For j = 0 the series F keeps only its coefficient at k, and the sum has the single term n = 0.
example (k m r : ℕ) (lam x y : ℝ) (hkr : k ≤ r) :
    let E : PowerSeries ℝ := (exp ℝ).subst (C (2 * y) * X - X ^ 2 : PowerSeries ℝ)
    let F : PowerSeries ℝ := PowerSeries.mk fun n ↦ if n = k then coeff n E else 0
    coeff r (F * trinomialNegPowSeries lam 1 m x m) =
      coeff k E * coeff (r - k) (trinomialNegPowSeries lam 1 m x m) := by
  intro E F
  have hF : F = PowerSeries.mk fun n ↦ if k ≤ n ∧ 0 ∣ n - k then coeff n E else 0 := by
    ext n
    have hiff : n = k ↔ k ≤ n ∧ 0 ∣ n - k := by
      rw [zero_dvd_iff]
      omega
    simp only [F, coeff_mk, hiff]
  rw [hF, (coeff_nietoHermiteSeries_mul_trinomialNegPowSeries 0 k m r lam x y hkr).1]
  simp [E]

-- With j = 2, k = 1 and r = 4 the sum runs over the indices 1 and 3 of the progression.
example (m : ℕ) (lam x y : ℝ) :
    let E : PowerSeries ℝ := (exp ℝ).subst (C (2 * y) * X - X ^ 2 : PowerSeries ℝ)
    let F : PowerSeries ℝ := PowerSeries.mk fun n ↦ if 1 ≤ n ∧ 2 ∣ n - 1 then coeff n E else 0
    let T : PowerSeries ℝ := trinomialNegPowSeries lam 1 m x m
    coeff 4 (F * T) = coeff 1 E * coeff 3 T + coeff 3 E * coeff 1 T := by
  intro E F T
  rw [(coeff_nietoHermiteSeries_mul_trinomialNegPowSeries 2 1 m 4 lam x y (by norm_num)).1]
  simp [E, T, Finset.sum_range_succ]

-- At r = k only the lowest term of F meets the constant term 1 of the trinomial series.
example (j k m : ℕ) (hm : m ≠ 0) (lam x y : ℝ) :
    let E : PowerSeries ℝ := (exp ℝ).subst (C (2 * y) * X - X ^ 2 : PowerSeries ℝ)
    let F : PowerSeries ℝ := PowerSeries.mk fun n ↦ if k ≤ n ∧ j ∣ n - k then coeff n E else 0
    coeff k (F * trinomialNegPowSeries lam 1 (m * x) 1 m) = coeff k E := by
  intro E F
  rw [(coeff_nietoHermiteSeries_mul_trinomialNegPowSeries j k m k lam x y le_rfl).2]
  simp [E, constantCoeff_trinomialNegPowSeries _ _ _ _ hm]
