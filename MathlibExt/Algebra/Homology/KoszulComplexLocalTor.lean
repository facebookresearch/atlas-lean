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

public import MathlibExt.Algebra.Homology.KoszulComplexTensorTor
public import MathlibExt.Algebra.Category.ModuleCat.Length
public import MathlibExt.RingTheory.Localization.AtPrimeSurjective
public import MathlibExt.AlgebraicGeometry.Correspondence.LocalizedDiagonalKoszul
public import Mathlib.RingTheory.Regular.Flat
public import Mathlib.RingTheory.Localization.Module

/-!
# Actual local Tor groups from regular intersection equations

The actual local ring map is induced by the original coefficient map and
the original support prime. Flat localization preserves the proved regular
sequence. The native Tor groups over that local source ring are therefore
the original local Koszul homology on the literal images of the equations.
For a surjective support coefficient map, its actual local map is also
surjective, giving equality of the module lengths used by Serre.
-/

@[expose] public section

noncomputable section

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits

namespace KoszulComplex

universe u

variable (R S : Type u) [CommRing R] [CommRing S]

/-- The actual coefficient algebra between the original local rings. -/
@[instance_reducible]
def localRegularCoefficientAlgebra (f : R →+* S) (p : Ideal S) [p.IsPrime] :
    Algebra (Localization.AtPrime (p.comap f)) (Localization.AtPrime p) :=
  (Localization.localRingHom (p.comap f) p f rfl).toAlgebra

/-- The actual original equations localized in the source local ring. -/
def localRegularFamilyCoefficients
    {n : ℕ} (f : R →+* S) (a : Fin n → R) (p : Ideal S) [p.IsPrime] :
    Fin n → Localization.AtPrime (p.comap f) :=
  fun i => algebraMap R (Localization.AtPrime (p.comap f)) (a i)

/-- Flat localization of the actual source ring preserves its proved
regular coefficient sequence. -/
theorem localRegularFamily_isWeaklyRegular
    {n : ℕ} (f : R →+* S) (a : Fin n → R)
    (ha : RingTheory.Sequence.IsWeaklyRegular R (List.ofFn a))
    (p : Ideal S) [p.IsPrime] :
    RingTheory.Sequence.IsWeaklyRegular (Localization.AtPrime (p.comap f))
      (List.ofFn (localRegularFamilyCoefficients R S f a p)) := by
  let _ : Module.Flat R (Localization.AtPrime (p.comap f)) :=
    IsLocalization.flat _ (p.comap f).primeCompl
  have h := ha.of_flat (S := Localization.AtPrime (p.comap f))
  have hlist : (List.ofFn a).map (algebraMap R (Localization.AtPrime (p.comap f))) =
      List.ofFn (localRegularFamilyCoefficients R S f a p) := by
    rw [List.map_ofFn]
    rfl
  rw [hlist] at h
  exact h

/-- The actual local map sends the original localized equation to the
localization of its original image. No compatibility equation is supplied. -/
theorem localRegularFamily_mapped_eq
    {n : ℕ} (f : R →+* S) (a : Fin n → R) (p : Ideal S) [p.IsPrime] :
    letI := localRegularCoefficientAlgebra R S f p
    mappedFamily (Localization.AtPrime (p.comap f)) (Localization.AtPrime p)
        (localRegularFamilyCoefficients R S f a p) =
      AlgebraicGeometry.FiniteCorrespondenceIntersection.localizedDiagonalFamily S
        (fun i => f (a i)) p := by
  let _ := localRegularCoefficientAlgebra R S f p
  funext i
  exact Localization.localRingHom_to_map (p.comap f) p f rfl (a i)

/-- Native Tor over the actual local ambient ring is the actual local
Koszul homology of the original image equations. -/
def localRegularFamilyTorIso
    {n : ℕ} (f : R →+* S) (a : Fin n → R)
    (ha : RingTheory.Sequence.IsWeaklyRegular R (List.ofFn a))
    (p : Ideal S) [p.IsPrime] (j : ℕ) :
    letI := localRegularCoefficientAlgebra R S f p
    (((Tor (ModuleCat.{u} (Localization.AtPrime (p.comap f))) j).obj
      (ModuleCat.of (Localization.AtPrime (p.comap f)) (Localization.AtPrime p))).obj
        (ModuleCat.of (Localization.AtPrime (p.comap f))
          (Localization.AtPrime (p.comap f) ⧸
            ideal (Localization.AtPrime (p.comap f)) (Fin n → Localization.AtPrime (p.comap f))
              (familyFunctional (Localization.AtPrime (p.comap f))
                (localRegularFamilyCoefficients R S f a p))))) ≅
      (ModuleCat.restrictScalars (Localization.localRingHom (p.comap f) p f rfl)).obj
        ((familyComplex (Localization.AtPrime p)
          (AlgebraicGeometry.FiniteCorrespondenceIntersection.localizedDiagonalFamily S
            (fun i => f (a i)) p)).homology j) := by
  let _ := localRegularCoefficientAlgebra R S f p
  have e := regularFiniteFamilyTorIsoMappedHomology (Localization.AtPrime (p.comap f))
    (Localization.AtPrime p) (localRegularFamilyCoefficients R S f a p)
      (localRegularFamily_isWeaklyRegular R S f a ha p) j
  rw [localRegularFamily_mapped_eq] at e
  exact e

/-- The original native Tor object, defined from the actual local
coefficient map and original quotient, independently of regularity. -/
abbrev localRegularFamilyTorObject
    {n : ℕ} (f : R →+* S) (a : Fin n → R) (p : Ideal S) [p.IsPrime] (j : ℕ) :
    letI := localRegularCoefficientAlgebra R S f p
    ModuleCat.{u} (Localization.AtPrime (p.comap f)) :=
  letI := localRegularCoefficientAlgebra R S f p
  (((Tor (ModuleCat.{u} (Localization.AtPrime (p.comap f))) j).obj
    (ModuleCat.of (Localization.AtPrime (p.comap f)) (Localization.AtPrime p))).obj
      (ModuleCat.of (Localization.AtPrime (p.comap f))
        (Localization.AtPrime (p.comap f) ⧸
          ideal (Localization.AtPrime (p.comap f)) (Fin n → Localization.AtPrime (p.comap f))
            (familyFunctional (Localization.AtPrime (p.comap f))
              (localRegularFamilyCoefficients R S f a p)))))

/-- Along the actual local map of a surjective support map, native Tor
and local Koszul homology have the same module lengths. -/
theorem localRegularFamilyTor_length_eq
    {n : ℕ} (f : R →+* S) (hf : Function.Surjective f) (a : Fin n → R)
    (ha : RingTheory.Sequence.IsWeaklyRegular R (List.ofFn a))
    (p : Ideal S) [p.IsPrime] (j : ℕ) :
    letI := localRegularCoefficientAlgebra R S f p
    Module.length (Localization.AtPrime (p.comap f)) (localRegularFamilyTorObject R S f a p j) =
      Module.length (Localization.AtPrime p)
        ((familyComplex (Localization.AtPrime p)
          (AlgebraicGeometry.FiniteCorrespondenceIntersection.localizedDiagonalFamily S
            (fun i => f (a i)) p)).homology j) := by
  let _ := localRegularCoefficientAlgebra R S f p
  let H := (familyComplex (Localization.AtPrime p)
    (AlgebraicGeometry.FiniteCorrespondenceIntersection.localizedDiagonalFamily S
      (fun i => f (a i)) p)).homology j
  calc
    _ = Module.length (Localization.AtPrime (p.comap f))
        ((ModuleCat.restrictScalars (Localization.localRingHom (p.comap f) p f rfl)).obj H) :=
      (localRegularFamilyTorIso R S f a ha p j).toLinearEquiv.length_eq
    _ = Module.length (Localization.AtPrime p) H :=
      ModuleCat.restrictScalars_length_eq (Localization.localRingHom (p.comap f) p f rfl)
        (Localization.localRingHom_surjective f hf p) H

/-- At an actual generic intersection support, every original local Tor
group has finite length. Its finiteness follows from the actual minimal
prime, the actual quotient map, and the proved regular resolution. -/
theorem localRegularFamilyTor_length_ne_top
    [IsNoetherianRing S] {n : ℕ} (f : R →+* S) (hf : Function.Surjective f) (a : Fin n → R)
    (ha : RingTheory.Sequence.IsWeaklyRegular R (List.ofFn a))
    (p : Ideal S) [p.IsPrime]
    (hp : p ∈ (Ideal.span (Set.range fun i => f (a i))).minimalPrimes) (j : ℕ) :
    letI := localRegularCoefficientAlgebra R S f p
    Module.length (Localization.AtPrime (p.comap f)) (localRegularFamilyTorObject R S f a p j) ≠ ⊤ := by
  let _ := localRegularCoefficientAlgebra R S f p
  rw [localRegularFamilyTor_length_eq R S f hf a ha p j]
  exact AlgebraicGeometry.FiniteCorrespondenceIntersection.localizedDiagonalKoszul_homology_length_ne_top
    S (fun i => f (a i)) p hp j

/-- The original local Tor groups vanish above the actual length of the
regular coefficient sequence. This cutoff is proved from the original
projective Koszul resolution. -/
theorem localRegularFamilyTor_isZero_above
    {n : ℕ} (f : R →+* S) (a : Fin n → R)
    (ha : RingTheory.Sequence.IsWeaklyRegular R (List.ofFn a))
    (p : Ideal S) [p.IsPrime] (j : ℕ) (hj : n < j) :
    letI := localRegularCoefficientAlgebra R S f p
    IsZero (localRegularFamilyTorObject R S f a p j) := by
  let _ := localRegularCoefficientAlgebra R S f p
  let K := familyComplex (Localization.AtPrime p)
    (AlgebraicGeometry.FiniteCorrespondenceIntersection.localizedDiagonalFamily S
      (fun i => f (a i)) p)
  have hX : IsZero (K.X j) := familyComplex_isZero_above (Localization.AtPrime p) _ j
    (by simpa only [Fintype.card_fin] using hj)
  have hH : IsZero (K.homology j) := (HomologicalComplex.ExactAt.of_isZero hX).isZero_homology
  have hTarget : IsZero
      ((ModuleCat.restrictScalars (Localization.localRingHom (p.comap f) p f rfl)).obj (K.homology j)) :=
    Functor.map_isZero _ hH
  exact IsZero.of_iso hTarget (localRegularFamilyTorIso R S f a ha p j)

/-- Serre's actual finite alternating sum of original local Tor lengths
for these proved regular intersection equations. -/
def localRegularFamilyTorEuler
    [IsNoetherianRing S] {n : ℕ} (f : R →+* S) (hf : Function.Surjective f) (a : Fin n → R)
    (ha : RingTheory.Sequence.IsWeaklyRegular R (List.ofFn a))
    (p : Ideal S) [p.IsPrime]
    (hp : p ∈ (Ideal.span (Set.range fun i => f (a i))).minimalPrimes) : ℤ :=
  letI := localRegularCoefficientAlgebra R S f p
  let _ := localRegularFamilyTor_length_ne_top R S f hf a ha p hp
  let _ := localRegularFamilyTor_isZero_above R S f a ha p
  ∑ j ∈ Finset.range (n + 1), (-1 : ℤ) ^ j *
    (Module.length (Localization.AtPrime (p.comap f))
      (localRegularFamilyTorObject R S f a p j)).toNat

/-- The genuine original local Tor multiplicity equals the Euler
invariant of the actual local Koszul complex on the image equations. -/
theorem localRegularFamilyTorEuler_eq_localizedDiagonalKoszulEuler
    [IsNoetherianRing S] {n : ℕ} (f : R →+* S) (hf : Function.Surjective f) (a : Fin n → R)
    (ha : RingTheory.Sequence.IsWeaklyRegular R (List.ofFn a))
    (p : Ideal S) [p.IsPrime]
    (hp : p ∈ (Ideal.span (Set.range fun i => f (a i))).minimalPrimes) :
    localRegularFamilyTorEuler R S f hf a ha p hp =
      AlgebraicGeometry.FiniteCorrespondenceIntersection.localizedDiagonalKoszulEuler S
        (fun i => f (a i)) p hp := by
  let _ := localRegularCoefficientAlgebra R S f p
  rw [AlgebraicGeometry.FiniteCorrespondenceIntersection.localizedDiagonalKoszulEuler_eq]
  change (∑ j ∈ Finset.range (n + 1), (-1 : ℤ) ^ j *
      (Module.length (Localization.AtPrime (p.comap f))
        (localRegularFamilyTorObject R S f a p j)).toNat) = _
  simp only [Fintype.card_fin]
  apply Finset.sum_congr rfl
  intro j hj
  rw [localRegularFamilyTor_length_eq R S f hf a ha p j]

end KoszulComplex
