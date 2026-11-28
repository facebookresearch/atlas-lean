/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.RingTheory.DiscreteValuationRing.Basic
public import Mathlib.RingTheory.Localization.Away.Basic
public import Mathlib.RingTheory.Localization.FractionRing

/-!
# The fraction field of a discrete valuation ring as a localization away from a uniformizer

The fraction field of a discrete valuation ring `R` is the localization of `R` away from any
uniformizer (`IsDiscreteValuationRing.isLocalization_away_of_irreducible`): every nonzero element
of `R` is a unit times a power of the uniformizer.
-/

@[expose] public section

/-- The fraction field `K` of a discrete valuation ring `R` is the localization of `R` away from
any uniformizer `ϖ`: every nonzero element of `R` is a unit times a power of `ϖ`. -/
theorem IsDiscreteValuationRing.isLocalization_away_of_irreducible {R : Type*} [CommRing R]
    [IsDomain R] [IsDiscreteValuationRing R] (K : Type*) [Field K] [Algebra R K]
    [IsFractionRing R K] {ϖ : R} (hϖ : Irreducible ϖ) : IsLocalization.Away ϖ K := by
  refine IsLocalization.Away.mk ϖ ?_ ?_ ?_
  · exact (IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors
      (mem_nonZeroDivisors_of_ne_zero hϖ.ne_zero)).isUnit
  · intro z
    obtain ⟨a, b, hb, rfl⟩ := IsFractionRing.div_surjective (A := R) z
    obtain ⟨n, u, rfl⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible
      (nonZeroDivisors.ne_zero hb) hϖ
    refine ⟨n, a * ↑u⁻¹, ?_⟩
    have hu : algebraMap R K (u : R) ≠ 0 := (u.isUnit.map _).ne_zero
    have hp : algebraMap R K (ϖ ^ n) ≠ 0 :=
      IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors
        (mem_nonZeroDivisors_of_ne_zero (pow_ne_zero _ hϖ.ne_zero))
    rw [map_mul, map_mul, ← map_pow]
    have hu' : algebraMap R K (↑u⁻¹ : R) * algebraMap R K (u : R) = 1 := by
      rw [← map_mul, Units.inv_mul, map_one]
    field_simp
    linear_combination (-(algebraMap R K) a) * hu'
  · intro a b hab
    exact ⟨0, by simpa using IsFractionRing.injective R K hab⟩
