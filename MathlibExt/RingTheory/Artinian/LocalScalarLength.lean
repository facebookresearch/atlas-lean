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
# Residue-degree weights in local scalar length

Let R be a commutative local ring and A a commutative Artinian R-algebra finite as an
R-module. Each prime localization A_p is finite over R, and the integral scalar homomorphism R
→ A_p is local. It induces the residue-field action κ(R) → κ(A_p).

Write f_p = dim_{κ(R)} κ(A_p). Restriction of scalars gives ℓ_R(A_p) = ℓ_{A_p}(A_p) · f_p, and
the Artinian product decomposition yields ℓ_R(A) = Σ_p ℓ_{A_p}(A_p) · f_p. A natural-number
form records the same finite lengths and degrees. The ring and algebra universes are
independent.
-/

@[expose] public section
noncomputable section
set_option autoImplicit false
open scoped BigOperators

universe u v

namespace IsArtinianRing

variable (R : Type u) (A : Type v) [CommRing R] [CommRing A] [Algebra R A]
  [Module.Finite R A] [IsArtinianRing A]

/-- Finite scalar module structure on an Artinian prime localization.

If A is a commutative Artinian R-algebra finite over R, then A_p is finite over R for every p
∈ Spec A. The Artinian localization map A → A_p is surjective, so finite generation descends
to the localization. -/
local instance primeLocalizationFinite (p : PrimeSpectrum A) :
    Module.Finite R (Localization.AtPrime p.asIdeal) :=
  Module.Finite.of_surjective
    (IsScalarTower.toAlgHom R A (Localization.AtPrime p.asIdeal)).toLinearMap
    (localization_surjective p.asIdeal.primeCompl (Localization.AtPrime p.asIdeal))

variable [IsLocalRing R]

/-- Local scalar homomorphism into an Artinian prime factor.

For a finite commutative Artinian R-algebra A with R local, the scalar map R → A_p is a local
homomorphism. The map is integral by finite generation, and both source and prime-localization
target are local rings. -/
local instance primeLocalizationIsLocalHom (p : PrimeSpectrum A) :
    IsLocalHom (algebraMap R (Localization.AtPrime p.asIdeal)) := by
  have h : (algebraMap R (Localization.AtPrime p.asIdeal)).IsIntegral :=
    algebraMap_isIntegral_iff.mpr inferInstance
  exact h.isLocalHom_of_isLocalRing

/-- Residue-field degree at a prime Artinian factor.

For a finite Artinian algebra A over a commutative local ring R, define f_p = dim_{κ(R)}
κ(A_p), using the residue-field scalar structure induced by the local map R → A_p. -/
def residueDegreeAtPrime (p : PrimeSpectrum A) : ℕ :=
  Module.finrank (IsLocalRing.ResidueField R)
    (IsLocalRing.ResidueField (Localization.AtPrime p.asIdeal))

/-- Finrank formula for the prime residue degree.

The degree residueDegreeAtPrime R A p is Module.finrank over κ(R) of κ(A_p), with its induced
residue-field algebra structure. -/
theorem residueDegreeAtPrime_eq_finrank (p : PrimeSpectrum A) :
    residueDegreeAtPrime R A p =
      Module.finrank (IsLocalRing.ResidueField R)
        (IsLocalRing.ResidueField (Localization.AtPrime p.asIdeal)) :=
  rfl

/-- Local multiplicity and residue-degree formula for scalar length.

For a finite commutative Artinian algebra A over a local ring R, ℓ_R(A) = Σ_{p∈Spec A}
ℓ_{A_p}(A_p) · f_p in ℕ∞, where f_p = dim_{κ(R)} κ(A_p). The local ring lengths retain all
nilpotent multiplicities. -/
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

/-- Natural-number local multiplicity and residue-degree formula.

For a finite Artinian algebra A over a commutative local ring R, ℓ_R(A).toNat = Σ_p
ℓ_{A_p}(A_p).toNat · f_p. The local lengths are finite and the residue degrees use the scalar
maps induced from R. -/
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
