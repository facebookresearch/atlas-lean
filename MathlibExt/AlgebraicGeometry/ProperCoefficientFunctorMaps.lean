/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import MathlibExt.AlgebraicGeometry.ProperGeometricCoefficientFamilies

/-!
# The actual ordinary coefficient test functor

The test functor uses the original Spec ring maps, with identity and
composition proved on those same native maps. Every test arrow remains
over the fixed original proper source; its geometric X_A arrow is the
original fibre-product map rather than a new coefficient action.

References: Stacks0DLD/0DLE and Toen--Vaquie math/0503269v5,
Sections3.1/3.5. The original native source-family notices remain in
the imported models.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section

namespace MathlibExt.AlgebraicGeometry.ProperCoefficientFunctorMaps

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.Opposite _root_.AlgebraicGeometry
open _root_.AlgebraicGeometry.EtaleSpacePresentations
open MathlibExt.AlgebraicGeometry.AlgebraicSpaceComplexSourceSites
open MathlibExt.AlgebraicGeometry.ProperSpaceComplexFamilies
open MathlibExt.AlgebraicGeometry.GeometricPerfectTestModels
open MathlibExt.AlgebraicGeometry.DerivedOrdinaryComplexModels
open MathlibExt.AlgebraicGeometry.ProperGeometricCoefficientFamilies

universe u

variable (D : ProperSpaceSituation.{u}) (B : AffineProperFamily D)

/-- The original coefficient ring identity is unchanged under forgetting the algebra structure. -/
theorem coefficientRingArrow_id (A : CommAlgCat.{u} B.ring) :
    coefficientRingArrow D B (𝟙 A) = 𝟙 (ordinaryRing A) := rfl

/-- The same original coefficient ring map preserves actual composition. -/
theorem coefficientRingArrow_comp {A A' A'' : CommAlgCat.{u} B.ring} (f : A ⟶ A') (g : A' ⟶ A'') :
    coefficientRingArrow D B (f ≫ g) = coefficientRingArrow D B f ≫ coefficientRingArrow D B g := rfl

/-- Native source-family arrows are determined by their actual ordinary scheme maps. -/
theorem nativeFamilyHom_ext {T T' : MathlibExt.AlgebraicGeometry.ProperSpaceComplexFamilies.FamilyTest D}
    {f g : MathlibExt.AlgebraicGeometry.ProperSpaceComplexFamilies.FamilyHom T T'}
    (h : f.schemeMap = g.schemeMap) : f = g := by
  cases f
  cases g
  cases h
  rfl

/-- The actual coefficient test functor has the literal contravariant Spec action on all arrows. -/
def coefficientTests : (CommAlgCat.{u} B.ring)ᵒᵖ ⥤ FamilyTest D where
  obj A := (coefficientFamily D B A.unop).test
  map f := coefficientArrow D B f.unop
  map_id A := by
    apply nativeFamilyHom_ext D
    change Scheme.Spec.map (coefficientRingArrow D B (𝟙 A.unop)).op = 𝟙 _
    rw [coefficientRingArrow_id, op_id]
    exact Scheme.Spec.map_id _
  map_comp f g := by
    apply nativeFamilyHom_ext D
    change Scheme.Spec.map (coefficientRingArrow D B (g.unop ≫ f.unop)).op =
      Scheme.Spec.map (coefficientRingArrow D B f.unop).op ≫
        Scheme.Spec.map (coefficientRingArrow D B g.unop).op
    rw [coefficientRingArrow_comp, op_comp, _root_.CategoryTheory.Functor.map_comp]

/-- The native geometric family arrow retains the original coefficient projection equation. -/
theorem coefficientGeometricArrow_projection {A A' : CommAlgCat.{u} B.ring} (f : A ⟶ A') :
    sheafMap (coefficientGeometricArrow D B f) ≫ coefficientProjection D B A =
      coefficientProjection D B A' ≫ represented.map (Spec.map (coefficientRingArrow D B f)) := by
  simpa only [coefficientGeometricArrow, coefficientProjection, coefficientSpace, affineProperProjection,
    coefficientFamily, coefficientArrow, eqToHom_refl, _root_.CategoryTheory.Functor.map_id, Category.comp_id] using
    ProperGeometricCoefficientFamilies.familyMap_projection D (coefficientArrow D B f)

end MathlibExt.AlgebraicGeometry.ProperCoefficientFunctorMaps
