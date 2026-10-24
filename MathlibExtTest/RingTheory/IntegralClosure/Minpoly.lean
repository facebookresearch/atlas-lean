/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.RingTheory.IntegralClosure.Minpoly
public import Mathlib.Algebra.GCDMonoid.IntegrallyClosed

@[expose] public section

/-!
# Tests for Proposition 1.28 (minimal polynomial criterion for integrality)

All examples are over `ℤ` with fraction field `ℚ`: `(2 : ℚ)` is integral,
`(1 / 2 : ℚ)` is not, and every element in the image of `algebraMap ℤ ℚ`
is integral.
-/

open Polynomial

/-- `(2 : ℚ)` is integral over `ℤ`, via the lift form of Proposition 1.28. -/
example : IsIntegral ℤ (2 : ℚ) := by
  have hα : IsIntegral ℚ (2 : ℚ) := Algebra.IsIntegral.isIntegral _
  rw [IsIntegrallyClosed.isIntegral_iff_minpoly_mem_lifts hα, Polynomial.mem_lifts,
    minpoly.eq_X_sub_C']
  refine ⟨X - C (2 : ℤ), ?_⟩
  simp only [Polynomial.map_sub, Polynomial.map_X, Polynomial.map_C, algebraMap_int_eq]
  norm_num

/-- `(1 / 2 : ℚ)` is not integral over `ℤ`, via the coefficient form:
the constant coefficient `-1 / 2` of its minimal polynomial is not an integer. -/
example : ¬ IsIntegral ℤ (1 / 2 : ℚ) := by
  have hα : IsIntegral ℚ (1 / 2 : ℚ) := Algebra.IsIntegral.isIntegral _
  intro hInt
  have h0 := (IsIntegrallyClosed.isIntegral_iff_minpoly_coeff_mem_range hα).mp hInt 0
  rw [minpoly.eq_X_sub_C'] at h0
  simp only [coeff_sub, coeff_X_zero, coeff_C_zero, zero_sub] at h0
  obtain ⟨n, hn⟩ := h0
  have hn' : (n : ℚ) = -(1 / 2 : ℚ) := hn
  have key : ((2 * n : ℤ) : ℚ) = ((-1 : ℤ) : ℚ) := by push_cast; linarith [hn']
  have h2 : 2 * n = -1 := Int.cast_injective key
  omega

/-- Every element in the image of `algebraMap ℤ ℚ` is integral over `ℤ`,
via the lift form of Proposition 1.28. -/
example (a : ℤ) : IsIntegral ℤ (algebraMap ℤ ℚ a) := by
  have hα : IsIntegral ℚ (algebraMap ℤ ℚ a) := Algebra.IsIntegral.isIntegral _
  rw [IsIntegrallyClosed.isIntegral_iff_minpoly_mem_lifts hα]
  have hmin : minpoly ℚ (algebraMap ℤ ℚ a) = X - C (algebraMap ℤ ℚ a) := by
    simpa using minpoly.eq_X_sub_C (B := ℚ) (algebraMap ℤ ℚ a)
  rw [hmin]
  exact ⟨X - C a, by simp⟩

/-- Equality form of Proposition 1.28, checked at `algebraMap ℤ ℚ a`. -/
example (a : ℤ) : IsIntegral ℤ (algebraMap ℤ ℚ a) := by
  have hα : IsIntegral ℚ (algebraMap ℤ ℚ a) := Algebra.IsIntegral.isIntegral _
  have hkey : minpoly ℚ (algebraMap ℤ ℚ a) =
      (minpoly ℤ (algebraMap ℤ ℚ a)).map (algebraMap ℤ ℚ) := by
    show minpoly ℚ (algebraMap ℤ ℚ a) =
      (minpoly ℤ (algebraMap ℤ ℚ a)).map (algebraMap ℤ ℚ)
    rw [minpoly.eq_X_sub_C',
      minpoly.eq_X_sub_C_of_algebraMap_inj a (IsFractionRing.injective ℤ ℚ),
      Polynomial.map_sub, Polynomial.map_X, Polynomial.map_C]
  exact (IsIntegrallyClosed.minpoly_eq_map_iff_isIntegral hα).mp hkey
