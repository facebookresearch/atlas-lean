/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

import MathlibExt.AlgebraicGeometry.RapoportZinkContracts

/-! # Tests for the geometric traits of a semistable degeneration

The Galois actions on the generic fibre and on the normalized model are compatible with the
generic arrow, and inertia acts trivially on the special fibre, by instance search; the identity
acts as the identity of the generic fibre; the logarithm of the nearby monodromy truncated at degree
zero vanishes.
-/

namespace MathlibExtTest.AlgebraicGeometry.GeometricSemistableTraits

open _root_.CategoryTheory _root_.AlgebraicGeometry
open MathlibExt.AlgebraicGeometry.GeometricSemistableTraits

variable {R : Type} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
  {K L : Type} [Field K] [Field L] [Algebra R K] [IsFractionRing R K]
  [Algebra K L] [Algebra R L] [IsScalarTower R K L] [IsAlgClosure K L]
  (π : R) (T : GeometricTrait R K L π) (X : Over (Spec (.of R)))

example : InertiaSchemeCompatibility π T X := inferInstance

/-- The generic arrow intertwines the Galois actions of an inertia element. -/
example (σ : Inertia π T) :
    genericGalois (K := K) X σ.1.1 ≫ genericArrow X =
      genericArrow X ≫ normalGalois (K := K) X σ.1.1 :=
  InertiaSchemeCompatibility.genericSquare σ

/-- Inertia fixes the special fibre inside the normalized model. -/
example (σ : Inertia π T) :
    specialArrow π T X ≫ normalGalois (K := K) X σ.1.1 = specialArrow π T X :=
  InertiaSchemeCompatibility.specialSquare σ

/-- The identity of the Galois group acts as the identity of the generic fibre. -/
example : genericGalois (K := K) X (1 : Galois K L) = 𝟙 _ := by
  apply Limits.pullback.hom_ext
  · simp
  · rw [genericGalois_snd, Category.id_comp]
    have h : CommRingCat.ofHom (1 : Galois K L).toRingHom = 𝟙 (CommRingCat.of L) := rfl
    rw [h, Spec.map_id, Category.comp_id]

section Nearby

open MathlibExt.AlgebraicGeometry.RapoportZinkContracts
open MathlibExt.AlgebraicGeometry.AdicDerivedContracts
open MathlibExt.AlgebraicGeometry.SemistableWeilDeligne
open MathlibExt.AlgebraicGeometry.ProEtaleCohomologyFunctoriality
open MathlibExt.AlgebraicGeometry.GeometricAdicGaloisOperators

variable (ell : ℕ) [Fact ell.Prime] [IsProper X.hom] [DerivedFunctorTheory ℚ_[ell]]
  [∀ σ : Galois K L, IsIso (coefficientPullback ℚ_[ell] (RationalCoefficients.{0} ell)
    (genericGalois (K := K) X σ))]

/-- The logarithm truncated at degree zero is zero. -/
example (B : TameCoordinate ell R K L π T) : nearbyLog ell R K L π T X 0 B = 0 := by
  simp [nearbyLog, Finset.sum_filter]

end Nearby

end MathlibExtTest.AlgebraicGeometry.GeometricSemistableTraits
