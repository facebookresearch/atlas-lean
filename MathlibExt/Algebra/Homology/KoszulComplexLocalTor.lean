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
# Local Tor computed by a localized regular-family Koszul complex

Let f : R → S be a map of commutative rings, p a prime of S and q=f⁻¹p. A weakly regular
family a in R remains weakly regular in R_q. The induced map R_q → S_p identifies
Tor_j^{R_q}(S_p,R_q/(a)) with the homology of the localized image-family Koszul complex,
restricted to R_q.

If f is surjective, the local map is surjective and the Tor length over R_q equals the Koszul
homology length over S_p. For noetherian S and p minimal over the image-family ideal, these
lengths are finite, vanish above the family size, and give the same signed local Euler sum.
-/

@[expose] public section

noncomputable section

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits

namespace KoszulComplex

universe u

variable (R S : Type u) [CommRing R] [CommRing S]

/-- The coefficient algebra between the two local rings.

Use the canonical local ring homomorphism R_q → S_p induced by f and q=p.comap f. -/
@[instance_reducible]
def localRegularCoefficientAlgebra (f : R →+* S) (p : Ideal S) [p.IsPrime] :
    Algebra (Localization.AtPrime (p.comap f)) (Localization.AtPrime p) :=
  (Localization.localRingHom (p.comap f) p f rfl).toAlgebra

/-- The family localized in the source local ring.

Send each a_i to its image under R → R_q. -/
def localRegularFamilyCoefficients
    {n : ℕ} (f : R →+* S) (a : Fin n → R) (p : Ideal S) [p.IsPrime] :
    Fin n → Localization.AtPrime (p.comap f) :=
  fun i => algebraMap R (Localization.AtPrime (p.comap f)) (a i)

/-- Weak regularity survives source localization.

A weakly regular family in R remains weakly regular after localization at q. -/
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

/-- The family images under the local coefficient map.

Mapping the source-localized family to S_p gives the localized images of f(a_i). -/
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

/-- The local Tor-to-Koszul homology isomorphism.

For weakly regular a, Tor_j^{R_q}(S_p,R_q/(a)) is isomorphic to the restricted S_p-Koszul
homology of the localized image family. -/
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

/-- The local Tor module of the regular-family quotient.

Take Tor_j over R_q with first coefficient S_p and second coefficient the quotient of R_q by
the localized family ideal. -/
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

/-- Local Tor and image-family homology have equal lengths under surjectivity.

For surjective f, the Tor length over R_q equals the image-family Koszul homology length over
S_p. -/
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

/-- Finite local Tor lengths at a minimal image-family prime.

For noetherian S, surjective f, weakly regular a and p minimal over its image ideal, the local
Tor module has finite length in every degree. -/
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

/-- The local regular-family Tor vanishes above the family size.

For a family of size n, its local Tor module is zero for j>n. -/
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

/-- The local regular-family Tor Euler sum.

Under the stated minimal-prime finiteness hypotheses, sum (−1)^j times the Tor lengths for
0≤j≤n. -/
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

/-- The local Tor Euler sum equals the localized image-family Koszul sum.

The signed Tor length sum equals the signed local Koszul homology length sum of the images
f(a_i), with the stated regularity, surjectivity and minimal-prime assumptions. -/
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
