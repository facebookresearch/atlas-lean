/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.FieldTheory.Minpoly.IntegrallyClosed
public import Mathlib.Algebra.GCDMonoid.IntegrallyClosed

@[expose] public section

/-!
# Tests for integrality via minimal polynomials over integrally closed domains
-/

variable {R K L : Type*} [CommRing R] [IsDomain R] [IsIntegrallyClosed R]
variable [Field K] [Algebra R K] [IsFractionRing R K]
variable [Field L] [Algebra K L] [Algebra R L] [IsScalarTower R K L]

/-- Forward direction of the lifts characterization. -/
example {x : L} (hx : IsAlgebraic K x) (h : IsIntegral R x) :
    minpoly K x ∈ Polynomial.lifts (algebraMap R K) :=
  (minpoly.isIntegral_iff_mem_lifts hx).mp h

/-- Backward direction of the lifts characterization. -/
example {x : L} (hx : IsAlgebraic K x)
    (h : minpoly K x ∈ Polynomial.lifts (algebraMap R K)) : IsIntegral R x :=
  (minpoly.isIntegral_iff_mem_lifts hx).mpr h

/-- Forward direction of the coefficient-range characterization. -/
example {x : L} (hx : IsAlgebraic K x) (h : IsIntegral R x) (n : ℕ) :
    (minpoly K x).coeff n ∈ Set.range (algebraMap R K) :=
  (minpoly.isIntegral_iff_coeff_mem_range hx).mp h n

/-- Backward direction of the coefficient-range characterization. -/
example {x : L} (hx : IsAlgebraic K x)
    (h : ∀ n, (minpoly K x).coeff n ∈ Set.range (algebraMap R K)) :
    IsIntegral R x :=
  (minpoly.isIntegral_iff_coeff_mem_range hx).mpr h

/-- An integer-cast rational is integral, so its rational minimal polynomial lifts. -/
example (n : ℤ) (hx : IsAlgebraic ℚ ((n : ℤ) : ℚ)) :
    minpoly ℚ ((n : ℤ) : ℚ) ∈ Polynomial.lifts (algebraMap ℤ ℚ) :=
  (minpoly.isIntegral_iff_mem_lifts hx).mp (isIntegral_intCast n)

/-- Every coefficient of the minimal polynomial of an integer-cast rational lies in
the range of the integer map. -/
example (n : ℤ) (hx : IsAlgebraic ℚ ((n : ℤ) : ℚ)) (m : ℕ) :
    (minpoly ℚ ((n : ℤ) : ℚ)).coeff m ∈ Set.range (algebraMap ℤ ℚ) :=
  (minpoly.isIntegral_iff_coeff_mem_range hx).mp (isIntegral_intCast n) m

section ConcreteRationalExamples

open Polynomial

/-- `(2 : ℚ)` is integral over `ℤ`, via the lift criterion. -/
example : IsIntegral ℤ (2 : ℚ) := by
  have hα : IsIntegral ℚ (2 : ℚ) := Algebra.IsIntegral.isIntegral _
  rw [minpoly.isIntegral_iff_mem_lifts hα.isAlgebraic, Polynomial.mem_lifts,
    minpoly.eq_X_sub_C']
  refine ⟨X - C (2 : ℤ), ?_⟩
  simp only [Polynomial.map_sub, Polynomial.map_X, Polynomial.map_C, algebraMap_int_eq]
  norm_num

/-- `(1 / 2 : ℚ)` is not integral over `ℤ`: its minimal polynomial has
constant coefficient `-1 / 2`, which is not an integer. -/
example : ¬ IsIntegral ℤ (1 / 2 : ℚ) := by
  have hα : IsIntegral ℚ (1 / 2 : ℚ) := Algebra.IsIntegral.isIntegral _
  intro hInt
  have h0 := (minpoly.isIntegral_iff_coeff_mem_range hα.isAlgebraic).mp hInt 0
  rw [minpoly.eq_X_sub_C'] at h0
  simp only [coeff_sub, coeff_X_zero, coeff_C_zero, zero_sub] at h0
  obtain ⟨n, hn⟩ := h0
  have hn' : (n : ℚ) = -(1 / 2 : ℚ) := hn
  have key : ((2 * n : ℤ) : ℚ) = ((-1 : ℤ) : ℚ) := by push_cast; linarith [hn']
  have h2 : 2 * n = -1 := Int.cast_injective key
  omega

/-- Every integer in `ℚ` is integral, via the lift criterion. -/
example (a : ℤ) : IsIntegral ℤ (algebraMap ℤ ℚ a) := by
  have hα : IsIntegral ℚ (algebraMap ℤ ℚ a) := Algebra.IsIntegral.isIntegral _
  rw [minpoly.isIntegral_iff_mem_lifts hα.isAlgebraic]
  have hmin : minpoly ℚ (algebraMap ℤ ℚ a) = X - C (algebraMap ℤ ℚ a) := by
    simpa using minpoly.eq_X_sub_C (B := ℚ) (algebraMap ℤ ℚ a)
  rw [hmin]
  exact ⟨X - C a, by simp⟩

/-- Equality form at an integer in `ℚ`, preserving the named arguments. -/
example (a : ℤ) : IsIntegral ℤ (algebraMap ℤ ℚ a) := by
  have hα : IsIntegral ℚ (algebraMap ℤ ℚ a) := Algebra.IsIntegral.isIntegral _
  have hkey : minpoly ℚ (algebraMap ℤ ℚ a) =
      (minpoly ℤ (algebraMap ℤ ℚ a)).map (algebraMap ℤ ℚ) := by
    show minpoly ℚ (algebraMap ℤ ℚ a) =
      (minpoly ℤ (algebraMap ℤ ℚ a)).map (algebraMap ℤ ℚ)
    rw [minpoly.eq_X_sub_C',
      minpoly.eq_X_sub_C_of_algebraMap_inj a (IsFractionRing.injective ℤ ℚ),
      Polynomial.map_sub, Polynomial.map_X, Polynomial.map_C]
  exact (IsIntegrallyClosed.minpoly_eq_map_iff_isIntegral
    (A := ℤ) (K := ℚ) (L := ℚ) hα).mp hkey

end ConcreteRationalExamples
