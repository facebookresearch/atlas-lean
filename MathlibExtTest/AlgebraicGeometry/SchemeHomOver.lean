/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.AlgebraicGeometry.SchemeHomOver

@[expose] public section

open CategoryTheory AlgebraicGeometry

namespace SchemeHomOverTest

/-- Consumer with the original binders. -/
theorem exactSource
    {R : Type} [CommRing R] {J : Scheme.{0}} {f : J ⟶ Spec (CommRingCat.of R)}
    [IsSeparated f]
    (A : Type) [CommRing A] [IsDomain A] [ValuationRing A] [Algebra R A]
    (K : Type) [Field K] [Algebra A K] [IsFractionRing A K] [Algebra R K]
    [IsScalarTower R A K]
    (x y : SchemeHomOver (Spec.map (CommRingCat.ofHom (algebraMap R A))) f)
    (h : Spec.map (CommRingCat.ofHom (algebraMap A K)) ≫ x.1 =
      Spec.map (CommRingCat.ofHom (algebraMap A K)) ≫ y.1) :
    x = y :=
  SchemeHomOver.eq_of_isSeparated_of_valuationRing_of_fst_eq A K x y h

/-- The same consumer in a higher universe. -/
theorem exactSource_univ1
    {R : Type 1} [CommRing R] {J : Scheme.{1}} {f : J ⟶ Spec (CommRingCat.of R)}
    [IsSeparated f]
    (A : Type 1) [CommRing A] [IsDomain A] [ValuationRing A] [Algebra R A]
    (K : Type 1) [Field K] [Algebra A K] [IsFractionRing A K] [Algebra R K]
    [IsScalarTower R A K]
    (x y : SchemeHomOver (Spec.map (CommRingCat.ofHom (algebraMap R A))) f)
    (h : Spec.map (CommRingCat.ofHom (algebraMap A K)) ≫ x.1 =
      Spec.map (CommRingCat.ofHom (algebraMap A K)) ≫ y.1) :
    x = y :=
  SchemeHomOver.eq_of_isSeparated_of_valuationRing_of_fst_eq A K x y h

end SchemeHomOverTest
