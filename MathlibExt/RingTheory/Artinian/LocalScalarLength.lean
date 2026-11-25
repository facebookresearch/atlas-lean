/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Author: @toskua
-/

module

public import MathlibExt.RingTheory.Artinian.LengthDecomposition
public import MathlibExt.RingTheory.LocalRing.IntegralHom
public import Mathlib.RingTheory.LocalRing.Length
public import Mathlib.RingTheory.HopkinsLevitzki

/-!
# Residue-weighted length over an arbitrary local base ring

A finite Artinian algebra over a local ring has actual prime-localization
factors, including every nilpotent multiplicity. The finite local maps
are derived from their true integral scalar homomorphisms. The original
base-ring length is the sum of local ring lengths weighted by the finite
degrees of their genuine residue fields over the base residue field.

The base ring need not be a field or act faithfully on the algebra. This
is the local scalar calculation for principal-divisor quotients on
singular curves. Zero algebras give the empty sum.
-/

@[expose] public section
noncomputable section
set_option autoImplicit false
open scoped BigOperators

universe u v

namespace IsArtinianRing

variable (R : Type u) (A : Type v) [CommRing R] [CommRing A] [Algebra R A]
  [Module.Finite R A] [IsArtinianRing A]

/-- The actual Artinian prime localization remains finite over the original base ring. -/
local instance primeLocalizationFinite (p : PrimeSpectrum A) :
    Module.Finite R (Localization.AtPrime p.asIdeal) :=
  Module.Finite.of_surjective
    (IsScalarTower.toAlgHom R A (Localization.AtPrime p.asIdeal)).toLinearMap
    (localization_surjective p.asIdeal.primeCompl (Localization.AtPrime p.asIdeal))

variable [IsLocalRing R]

/-- The true scalar homomorphism into a prime factor is local, including nonfaithful quotients. -/
local instance primeLocalizationIsLocalHom (p : PrimeSpectrum A) :
    IsLocalHom (algebraMap R (Localization.AtPrime p.asIdeal)) := by
  have h : (algebraMap R (Localization.AtPrime p.asIdeal)).IsIntegral :=
    algebraMap_isIntegral_iff.mpr inferInstance
  exact h.isLocalHom_of_isLocalRing

/-- The actual residue-field degree at a prime Artinian factor, over the original base residue field. -/
def residueDegreeAtPrime (p : PrimeSpectrum A) : ℕ :=
  Module.finrank (IsLocalRing.ResidueField R)
    (IsLocalRing.ResidueField (Localization.AtPrime p.asIdeal))

/-- The prime residue degree is computed in the actual canonical residue-field scalar structure. -/
theorem residueDegreeAtPrime_eq_finrank (p : PrimeSpectrum A) :
    residueDegreeAtPrime R A p =
      Module.finrank (IsLocalRing.ResidueField R)
        (IsLocalRing.ResidueField (Localization.AtPrime p.asIdeal)) :=
  rfl

/-- The original base-ring length is the genuine sum of local multiplicities times actual residue degrees. -/
theorem length_eq_sum_primeSpectrum_mul_residueDegree :
    letI : Fintype (PrimeSpectrum A) := Fintype.ofFinite (PrimeSpectrum A)
    Module.length R A = ∑ p : PrimeSpectrum A,
      Module.length (Localization.AtPrime p.asIdeal) (Localization.AtPrime p.asIdeal) *
        (residueDegreeAtPrime R A p : ℕ∞) := by
  classical
  let : Fintype (PrimeSpectrum A) := Fintype.ofFinite (PrimeSpectrum A)
  refine (length_eq_sum_primeSpectrum R A).trans (Finset.sum_congr rfl ?_)
  intro p _
  have h := IsLocalRing.length_restrictScalars R
    (Localization.AtPrime p.asIdeal) (Localization.AtPrime p.asIdeal)
  rw [Module.length_eq_finrank] at h
  exact h

/-- Natural-valued scalar length retains every actual local nilpotent multiplicity and residue-field degree. -/
theorem length_toNat_eq_sum_primeSpectrum_mul_residueDegree :
    letI : Fintype (PrimeSpectrum A) := Fintype.ofFinite (PrimeSpectrum A)
    (Module.length R A).toNat = ∑ p : PrimeSpectrum A,
      (Module.length (Localization.AtPrime p.asIdeal) (Localization.AtPrime p.asIdeal)).toNat *
        residueDegreeAtPrime R A p := by
  classical
  let : Fintype (PrimeSpectrum A) := Fintype.ofFinite (PrimeSpectrum A)
  have hcast : Module.length R A = ((∑ p : PrimeSpectrum A,
      (Module.length (Localization.AtPrime p.asIdeal) (Localization.AtPrime p.asIdeal)).toNat *
        residueDegreeAtPrime R A p : ℕ) : ℕ∞) := by
    rw [length_eq_sum_primeSpectrum_mul_residueDegree R A, Nat.cast_sum]
    apply Finset.sum_congr rfl
    intro p _
    have hp : Module.length (Localization.AtPrime p.asIdeal)
        (Localization.AtPrime p.asIdeal) ≠ ⊤ := Module.length_ne_top
    rw [Nat.cast_mul, ENat.natCast_toNat_eq_self.mpr hp]
  simpa only [ENat.toNat_natCast] using congrArg ENat.toNat hcast

end IsArtinianRing
