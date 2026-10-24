/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Algebra.Polynomial.Lifts
public import Mathlib.FieldTheory.Minpoly.IsIntegrallyClosed
public import Mathlib.RingTheory.Polynomial.Tower

@[expose] public section

/-!
# Minimal polynomial criterion for integrality over an integrally closed domain

ATLAS `NumberTheoryI`, Proposition 1.28: let `A` be an integrally closed
domain with fraction field `K`, and let `α` be an element of an extension
`L` of `K` with minimal polynomial `f ∈ K[X]` over `K`. Then `α` is
integral over `A` if and only if `f ∈ A[X]`, i.e. `f` lifts along
`algebraMap A K`.

The three formulations below are equivalent: the lift form stated in the
book, the coefficient form (every coefficient of `minpoly K α` lies in the
range of `algebraMap A K`), and the equality
`minpoly K α = (minpoly A α).map (algebraMap A K)`. Mathlib has the
one-way ingredient `minpoly.isIntegrallyClosed_eq_field_fractions'`
(integrality implies the equality) but none of these iff statements.
-/

open Polynomial

variable {A : Type*} [CommRing A] [IsDomain A] [IsIntegrallyClosed A]
  {K : Type*} [Field K] [Algebra A K] [IsFractionRing A K]
  {L : Type*} [Field L] [Algebra K L] [Algebra A L] [IsScalarTower A K L]

namespace IsIntegrallyClosed

/-- Coefficient form of Proposition 1.28: over an integrally closed domain,
an element `α` of an extension of the fraction field is integral over `A`
if and only if every coefficient of its minimal polynomial over `K` lies in
the range of `algebraMap A K`. -/
theorem isIntegral_iff_minpoly_coeff_mem_range {α : L} (hα : IsIntegral K α) :
    IsIntegral A α ↔
      ∀ i, (minpoly K α).coeff i ∈ Set.range (algebraMap A K) := by
  constructor
  · intro hInt
    rw [minpoly.isIntegrallyClosed_eq_field_fractions' K hInt]
    intro i
    rw [Polynomial.coeff_map]
    exact ⟨_, rfl⟩
  · intro hcoeff
    have hlifts : minpoly K α ∈ Polynomial.lifts (algebraMap A K) :=
      (Polynomial.lifts_iff_coeff_lifts _).mpr hcoeff
    have hmonic : (minpoly K α).Monic := minpoly.monic hα
    obtain ⟨q, hq_map, _, hq_monic⟩ :=
      Polynomial.lifts_and_natDegree_eq_and_monic hlifts hmonic
    have hq_root : Polynomial.aeval α q = 0 := by
      have h : Polynomial.aeval α (q.map (algebraMap A K)) = 0 := by
        rw [hq_map]
        exact minpoly.aeval K α
      rwa [Polynomial.aeval_map_algebraMap] at h
    exact ⟨q, hq_monic, hq_root⟩

/-- Proposition 1.28 as stated in the book: over an integrally closed domain,
`α` is integral over `A` if and only if its minimal polynomial over the
fraction field lifts to a polynomial over `A`. -/
theorem isIntegral_iff_minpoly_mem_lifts {α : L} (hα : IsIntegral K α) :
    IsIntegral A α ↔ minpoly K α ∈ Polynomial.lifts (algebraMap A K) := by
  rw [Polynomial.lifts_iff_coeff_lifts]
  exact isIntegral_iff_minpoly_coeff_mem_range hα

/-- Proposition 1.28 in equality form: `α` is integral over `A` if and only
if its minimal polynomial over `K` is the image of its minimal polynomial
over `A` under `algebraMap A K`. -/
theorem minpoly_eq_map_iff_isIntegral {α : L} (hα : IsIntegral K α) :
    minpoly K α = (minpoly A α).map (algebraMap A K) ↔ IsIntegral A α := by
  constructor
  · intro h
    rw [isIntegral_iff_minpoly_coeff_mem_range hα]
    intro i
    rw [h, Polynomial.coeff_map]
    exact ⟨_, rfl⟩
  · intro hInt
    exact minpoly.isIntegrallyClosed_eq_field_fractions' K hInt

end IsIntegrallyClosed
