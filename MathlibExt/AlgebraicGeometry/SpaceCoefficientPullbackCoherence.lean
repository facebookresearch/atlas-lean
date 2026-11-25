/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import MathlibExt.AlgebraicGeometry.ProperCoefficientFunctorMaps
public import MathlibExt.AlgebraicGeometry.SpaceGeometricDGHomSources

/-!
# Native algebraic-space pullback units and composition

Raw coherence is fixed by the actual ModulePullbackSource units on
every chart and every compatible chart triple. Cochain coherence is
fixed termwise by those same raw maps. Derived coherence is normalized
on EVERY source complex by the original total-left-derived counit.
These maps operate on the original X_A family spaces and coefficient
scheme arrows. They supply the source normalization for ordinary
complexes groupoid identity, composition and coefficient transport.

Source: Stacks 03G8/06YY/0DLD/0DLE, and Toën--Vaquié
arXiv:math/0503269v5 Section 3.5. Native source notices remain.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section

namespace MathlibExt.AlgebraicGeometry.SpaceCoefficientPullbackCoherence

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.Opposite _root_.AlgebraicGeometry
open _root_.AlgebraicGeometry.EtaleSpacePresentations
open MathlibExt.AlgebraicGeometry.AlgebraicSpaceComplexSourceSites
open MathlibExt.AlgebraicGeometry.ProperSpaceComplexFamilies

universe u
variable [SourceTheory.{u}]
attribute [local instance] HasDerivedCategory.standard

/-- The actual source identity chart square. -/
def identityPullbackChart {X : SourceSpace.{u}} (U : EtaleChart X)
    (h : U.map ≫ (𝟙 X) = represented.map (𝟙 U.scheme) ≫ U.map) : PullbackChart (𝟙 X) where
  source := U
  target := U
  schemeMap := 𝟙 U.scheme
  commutes := h

/-- Native chart squares compose through their actual shared middle chart. -/
def composePullbackCharts {X Y Z : SourceSpace.{u}} {f : X ⟶ Y} {g : Y ⟶ Z}
    (P : PullbackChart f) (Q : PullbackChart g) (h : P.target = Q.source)
    (hc : P.source.map ≫ (f ≫ g) =
      represented.map (P.schemeMap ≫ eqToHom (congrArg EtaleChart.scheme h) ≫ Q.schemeMap) ≫ Q.target.map) :
    PullbackChart (f ≫ g) :=
  ⟨P.source, Q.target, P.schemeMap ≫ eqToHom (congrArg EtaleChart.scheme h) ≫ Q.schemeMap, hc⟩

/-- Coherence concerns the original all-chart module inverse image and its actual derivation.
No unrelated functor or derived comparison equivalence is a constructor input. -/
structure SpacePullbackCoherence (P : PullbackSystem.{u}) where
  identityChartProof : ∀ (X : SourceSpace.{u}) (U : EtaleChart X),
    U.map ≫ (𝟙 X) = represented.map (𝟙 U.scheme) ≫ U.map
  compositeChartProof : ∀ {X Y Z : SourceSpace.{u}} (f : X ⟶ Y) (g : Y ⟶ Z)
    (a : PullbackChart f) (b : PullbackChart g) (h : a.target = b.source),
    a.source.map ≫ (f ≫ g) =
      represented.map (a.schemeMap ≫ eqToHom (congrArg EtaleChart.scheme h) ≫ b.schemeMap) ≫ b.target.map
  rawIdentity : ∀ X : SourceSpace.{u}, (P.module (𝟙 X)).functor ≅ 𝟭 (Modules X)
  rawIdentityUnit : ∀ (X : SourceSpace.{u}) (M : Modules X) (U : EtaleChart X) (m : M.val.obj (op U)),
    (((rawIdentity X).hom.app M).val.app (op U)).hom
      (((P.module (𝟙 X)).unit M).map (identityPullbackChart U (identityChartProof X U)) m) = m
  rawComposition : ∀ {X Y Z : SourceSpace.{u}} (f : X ⟶ Y) (g : Y ⟶ Z),
    (P.module g).functor ⋙ (P.module f).functor ≅ (P.module (f ≫ g)).functor
  rawCompositionUnit : ∀ {X Y Z : SourceSpace.{u}} (f : X ⟶ Y) (g : Y ⟶ Z)
    (M : Modules Z) (a : PullbackChart f) (b : PullbackChart g) (h : a.target = b.source)
    (m : M.val.obj (op b.target)),
    HEq
      (((rawComposition f g).hom.app M).val.app (op a.source)
        (((P.module f).unit ((P.module g).functor.obj M)).map a
          (cast (congrArg (fun U : EtaleChart Y =>
            ↥(((P.module g).functor.obj M).val.obj (op U))) h.symm)
            (((P.module g).unit M).map b m))))
      (((P.module (f ≫ g)).unit M).map (composePullbackCharts a b h (compositeChartProof f g a b h)) m)
  complexIdentity : ∀ X : SourceSpace.{u},
    (P.module (𝟙 X)).functor.mapHomologicalComplex (.up ℤ) ≅
      𝟭 (CochainComplex (Modules X) ℤ)
  complexIdentity_normalized : ∀ (X : SourceSpace.{u}) (K : CochainComplex (Modules X) ℤ) (n : ℤ),
    ((complexIdentity X).hom.app K).f n = (rawIdentity X).hom.app (K.X n)
  complexComposition : ∀ {X Y Z : SourceSpace.{u}} (f : X ⟶ Y) (g : Y ⟶ Z),
    (P.module g).functor.mapHomologicalComplex (.up ℤ) ⋙
      (P.module f).functor.mapHomologicalComplex (.up ℤ) ≅
    (P.module (f ≫ g)).functor.mapHomologicalComplex (.up ℤ)
  complexComposition_normalized : ∀ {X Y Z : SourceSpace.{u}} (f : X ⟶ Y) (g : Y ⟶ Z)
    (K : CochainComplex (Modules Z) ℤ) (n : ℤ),
    ((complexComposition f g).hom.app K).f n = (rawComposition f g).hom.app (K.X n)
  identity : ∀ X : SourceSpace.{u}, pull P (𝟙 X) ≅ 𝟭 (Derived X)
  identity_normalized : ∀ X : SourceSpace.{u},
    Functor.whiskerLeft DerivedCategory.Q (identity X).hom ≫
      (Functor.rightUnitor DerivedCategory.Q).hom =
    pullCounit P (𝟙 X) ≫ Functor.whiskerRight (complexIdentity X).hom DerivedCategory.Q ≫
      (Functor.leftUnitor DerivedCategory.Q).hom
  composition : ∀ {X Y Z : SourceSpace.{u}} (f : X ⟶ Y) (g : Y ⟶ Z),
    pull P g ⋙ pull P f ≅ pull P (f ≫ g)
  composition_normalized : ∀ {X Y Z : SourceSpace.{u}} (f : X ⟶ Y) (g : Y ⟶ Z),
    (Functor.associator DerivedCategory.Q (pull P g) (pull P f)).hom ≫
      Functor.whiskerLeft DerivedCategory.Q (composition f g).hom ≫ pullCounit P (f ≫ g) =
    Functor.whiskerRight (pullCounit P g) (pull P f) ≫
      (Functor.associator ((P.module g).functor.mapHomologicalComplex (.up ℤ)) DerivedCategory.Q (pull P f)).hom ≫
      Functor.whiskerLeft ((P.module g).functor.mapHomologicalComplex (.up ℤ)) (pullCounit P f) ≫
      (Functor.associator ((P.module g).functor.mapHomologicalComplex (.up ℤ))
        ((P.module f).functor.mapHomologicalComplex (.up ℤ)) DerivedCategory.Q).inv ≫
      Functor.whiskerRight (complexComposition f g).hom DerivedCategory.Q

/-- The coefficient identity uses the actual geometric arrow equality and native derived identity counit. -/
def coefficientIdentity (P : PullbackSystem.{u}) (C : SpacePullbackCoherence P)
    (D : ProperSpaceSituation.{u}) (B : MathlibExt.AlgebraicGeometry.GeometricPerfectTestModels.AffineProperFamily D)
    (A : CommAlgCat.{u} B.ring)
    (h : MathlibExt.AlgebraicGeometry.ProperGeometricCoefficientFamilies.coefficientGeometricArrow D B (𝟙 A) =
      𝟙 (MathlibExt.AlgebraicGeometry.ProperGeometricCoefficientFamilies.coefficientSpace D B A)) :
    pull P (MathlibExt.AlgebraicGeometry.ProperGeometricCoefficientFamilies.coefficientGeometricArrow D B (𝟙 A)) ≅
      𝟭 (Derived (MathlibExt.AlgebraicGeometry.ProperGeometricCoefficientFamilies.coefficientSpace D B A)) :=
  eqToIso (congrArg (fun f => pull P f) h) ≪≫ C.identity _

/-- Coefficient composition is the same native X_g then X_f composition, followed by its actual arrow equality. -/
def coefficientComposition (P : PullbackSystem.{u}) (C : SpacePullbackCoherence P)
    (D : ProperSpaceSituation.{u}) (B : MathlibExt.AlgebraicGeometry.GeometricPerfectTestModels.AffineProperFamily D)
    {A A' A'' : CommAlgCat.{u} B.ring} (f : A ⟶ A') (g : A' ⟶ A'')
    (h : MathlibExt.AlgebraicGeometry.ProperGeometricCoefficientFamilies.coefficientGeometricArrow D B (f ≫ g) =
      MathlibExt.AlgebraicGeometry.ProperGeometricCoefficientFamilies.coefficientGeometricArrow D B g ≫
        MathlibExt.AlgebraicGeometry.ProperGeometricCoefficientFamilies.coefficientGeometricArrow D B f) :
    pull P (MathlibExt.AlgebraicGeometry.ProperGeometricCoefficientFamilies.coefficientGeometricArrow D B f) ⋙
      pull P (MathlibExt.AlgebraicGeometry.ProperGeometricCoefficientFamilies.coefficientGeometricArrow D B g) ≅
    pull P (MathlibExt.AlgebraicGeometry.ProperGeometricCoefficientFamilies.coefficientGeometricArrow D B (f ≫ g)) :=
  C.composition
      (MathlibExt.AlgebraicGeometry.ProperGeometricCoefficientFamilies.coefficientGeometricArrow D B g)
      (MathlibExt.AlgebraicGeometry.ProperGeometricCoefficientFamilies.coefficientGeometricArrow D B f) ≪≫
    eqToIso (congrArg (fun f => pull P f) h.symm)

end MathlibExt.AlgebraicGeometry.SpaceCoefficientPullbackCoherence
