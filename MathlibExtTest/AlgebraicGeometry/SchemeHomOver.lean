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

/-- Consumer with the original binders, in the original subtype form:
morphisms over the base are given by an underlying morphism and its
commuting proof, and agreement is stated with the underlying morphisms. -/
theorem exactSource
    {R : Type} [CommRing R] {J : Scheme.{0}} {f : J ⟶ Spec (CommRingCat.of R)}
    [IsSeparated f]
    (A : Type) [CommRing A] [IsDomain A] [ValuationRing A] [Algebra R A]
    (K : Type) [Field K] [Algebra A K] [IsFractionRing A K] [Algebra R K]
    [IsScalarTower R A K]
    (x y : { φ : Spec (CommRingCat.of A) ⟶ J //
      φ ≫ f = Spec.map (CommRingCat.ofHom (algebraMap R A)) })
    (h : Spec.map (CommRingCat.ofHom (algebraMap A K)) ≫ x.1 =
      Spec.map (CommRingCat.ofHom (algebraMap A K)) ≫ y.1) :
    x = y := by
  let x' : SchemeHomOver (Spec.map (CommRingCat.ofHom (algebraMap R A))) f :=
    Over.homMk x.1 x.2
  let y' : SchemeHomOver (Spec.map (CommRingCat.ofHom (algebraMap R A))) f :=
    Over.homMk y.1 y.2
  have h' : Spec.map (CommRingCat.ofHom (algebraMap A K)) ≫ x'.left =
      Spec.map (CommRingCat.ofHom (algebraMap A K)) ≫ y'.left :=
    h
  have hxy : x' = y' :=
    SchemeHomOver.eq_of_isSeparated_of_valuationRing_of_fst_eq A K x' y' h'
  exact Subtype.ext (congrArg (fun φ => φ.left) hxy)

/-- The same consumer in a higher universe, in the original subtype form. -/
theorem exactSource_univ1
    {R : Type 1} [CommRing R] {J : Scheme.{1}} {f : J ⟶ Spec (CommRingCat.of R)}
    [IsSeparated f]
    (A : Type 1) [CommRing A] [IsDomain A] [ValuationRing A] [Algebra R A]
    (K : Type 1) [Field K] [Algebra A K] [IsFractionRing A K] [Algebra R K]
    [IsScalarTower R A K]
    (x y : { φ : Spec (CommRingCat.of A) ⟶ J //
      φ ≫ f = Spec.map (CommRingCat.ofHom (algebraMap R A)) })
    (h : Spec.map (CommRingCat.ofHom (algebraMap A K)) ≫ x.1 =
      Spec.map (CommRingCat.ofHom (algebraMap A K)) ≫ y.1) :
    x = y := by
  let x' : SchemeHomOver (Spec.map (CommRingCat.ofHom (algebraMap R A))) f :=
    Over.homMk x.1 x.2
  let y' : SchemeHomOver (Spec.map (CommRingCat.ofHom (algebraMap R A))) f :=
    Over.homMk y.1 y.2
  have h' : Spec.map (CommRingCat.ofHom (algebraMap A K)) ≫ x'.left =
      Spec.map (CommRingCat.ofHom (algebraMap A K)) ≫ y'.left :=
    h
  have hxy : x' = y' :=
    SchemeHomOver.eq_of_isSeparated_of_valuationRing_of_fst_eq A K x' y' h'
  exact Subtype.ext (congrArg (fun φ => φ.left) hxy)

end SchemeHomOverTest
