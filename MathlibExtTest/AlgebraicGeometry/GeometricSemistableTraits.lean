/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

import MathlibExt.AlgebraicGeometry.GeometricSemistableTraits

/-! # Tests for the geometric traits of a semistable degeneration

The Galois actions on the generic fibre and on the normalized model are compatible with the
generic arrow, and inertia acts trivially on the special fibre, by instance search.
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

end MathlibExtTest.AlgebraicGeometry.GeometricSemistableTraits
