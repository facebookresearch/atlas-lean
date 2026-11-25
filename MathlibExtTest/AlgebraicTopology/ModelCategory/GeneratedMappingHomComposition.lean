/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.ModelCategory.GeneratedRightMappingEnrichment

set_option autoImplicit false

noncomputable section

universe w uC vC uH vH

open CategoryTheory MonoidalCategory
open scoped Simplicial MonoidalCategory SSet.modelCategoryQuillen

namespace GeneratedMappingHomCompositionClients

open HomotopicalAlgebra HomotopyMappingSpaceCategory
open CanonicalGeneratedFrameEnrichment GeneratedFrameHomComplex GeneratedFrameEnrichmentComparison
open GeneratedMappingHomComposition

variable {C : Type uC} [Category.{vC} C] [ModelCategory C]
  {κ : Cardinal.{w}} [Fact κ.IsRegular] [OrderBot κ.ord.ToType]
  (d : CofibrantGenerationData C κ)
  {H : Type uH} [Category.{vH} H] (L : C ⥤ H) [L.IsLocalization (weakEquivalences C)]

def componentComparisonClient (X Y : C) : SSet.π₀ (nativeSpace d X Y) ≃ SSet.π₀ (rightSpace d X Y) :=
  componentComparison d X Y

theorem nativeCompHomClient (X Y Z : C) (f : SSet.π₀ (rightSpace d X Y)) (g : SSet.π₀ (rightSpace d Y Z)) :
    rightPiZeroEquiv d L X Z (componentComp d X Y Z f g) =
      rightPiZeroEquiv d L X Y f ≫ rightPiZeroEquiv d L Y Z g :=
  componentComp_toHom d L X Y Z f g

theorem localizedCompHomClient (X Y Z : C) (f : SSet.π₀ (rightSpace d X Y)) (g : SSet.π₀ (rightSpace d Y Z)) :
    rightPiZeroEquiv d L X Z (localizedComponentComp d X Y Z f g) =
      rightPiZeroEquiv d L X Y f ≫ rightPiZeroEquiv d L Y Z g :=
  localizedComponentComp_toHom d L X Y Z f g

set_option backward.isDefEq.respectTransparency false in
theorem entireLocalizedCompHomClient (X Y Z : C) (f : SSet.π₀ (rightSpace d X Y)) (g : SSet.π₀ (rightSpace d Y Z)) :
    rightPiZeroEquiv d L X Z
      ((componentsIso (rightSpace d X Z)).hom
        (components.map (GeneratedRightMappingEnrichment.comp d X Y Z)
          (Functor.LaxMonoidal.μ components (GeneratedRightMappingEnrichment.space d X Y)
            (GeneratedRightMappingEnrichment.space d Y Z)
              ((componentsIso (rightSpace d X Y)).inv f,
                (componentsIso (rightSpace d Y Z)).inv g)))) =
    rightPiZeroEquiv d L X Y f ≫ rightPiZeroEquiv d L Y Z g :=
  localizedComponentComp_toHom d L X Y Z f g

theorem inverseComponentCompClient (X Y Z : C) (f : L.obj X ⟶ L.obj Y) (g : L.obj Y ⟶ L.obj Z) :
    (rightPiZeroEquiv d L X Z).symm (f ≫ g) =
      componentComp d X Y Z ((rightPiZeroEquiv d L X Y).symm f)
        ((rightPiZeroEquiv d L Y Z).symm g) :=
  componentComp_ofHom d L X Y Z f g

theorem inverseLocalizedCompClient (X Y Z : C) (f : L.obj X ⟶ L.obj Y) (g : L.obj Y ⟶ L.obj Z) :
    (rightPiZeroEquiv d L X Z).symm (f ≫ g) =
      localizedComponentComp d X Y Z ((rightPiZeroEquiv d L X Y).symm f)
        ((rightPiZeroEquiv d L Y Z).symm g) := by
  rw [localizedComponentComp_eq, componentComp_ofHom]

theorem localizedUnitHomClient (X : C) (t : 𝟙_ (Type vC)) :
    rightPiZeroEquiv d L X X (localizedUnitMap d X t) = 𝟙 (L.obj X) :=
  localizedUnitMap_toHom d L X t

set_option backward.isDefEq.respectTransparency false in
theorem entireLocalizedUnitHomClient (X : C) (t : 𝟙_ (Type vC)) :
    rightPiZeroEquiv d L X X
      ((componentsIso (rightSpace d X X)).hom
        (components.map (GeneratedRightMappingEnrichment.unit d X)
          (Functor.LaxMonoidal.ε components t))) = 𝟙 (L.obj X) :=
  localizedUnitMap_toHom d L X t

theorem nativeVertexWordClient (X Y : C) (f : (nativeSpace d X Y).obj (.op ⦋0⦌)) :
    nativeComponentsToHom d L X Y (SSet.π₀.mk f) =
      inv (L.map ((GeneratedFunctorialReplacements.counit d).app X)) ≫
        L.map (frameInclusionZero d X) ≫ L.map (f.app (.op ⦋0⦌) (𝟙 _)) ≫
          inv (L.map (frameInclusionZero d Y)) ≫
            L.map ((GeneratedFunctorialReplacements.counit d).app Y) :=
  nativeComponentsToHom_mk d L X Y f

theorem nativeAllComponentsCompClient (X Y Z : C) (f : SSet.π₀ (nativeSpace d X Y)) (g : SSet.π₀ (nativeSpace d Y Z)) :
    nativeComponentsToHom d L X Z (nativeComponentComp d X Y Z f g) =
      nativeComponentsToHom d L X Y f ≫ nativeComponentsToHom d L Y Z g :=
  nativeComponentsToHom_comp d L X Y Z f g

theorem entireOriginalPointCompClient {X Y Z : C} (f : X ⟶ Y) (g : Y ⟶ Z) :
    point d (f ≫ g) = (λ_ (𝟙_ SpaceHo.{vC})).inv ≫
      (point d f ⊗ₘ point d g) ≫ GeneratedRightMappingEnrichment.comp d X Y Z :=
  point_comp d f g

theorem originalPointUnitClient (X : C) : point d (𝟙 X) = GeneratedRightMappingEnrichment.unit d X := point_id d X

theorem originalCompositeHomClient {X Y Z : C} (f : X ⟶ Y) (g : Y ⟶ Z) :
    rightPiZeroEquiv d L X Z (SSet.π₀.mk (representedRightVertex d (f ≫ g))) =
      L.map f ≫ L.map g := point_comp_components d L f g

theorem originalIdentityHomClient (X : C) :
    rightPiZeroEquiv d L X X (SSet.π₀.mk (representedRightVertex d (𝟙 X))) = 𝟙 (L.obj X) :=
  point_id_components d L X

def originalComponentsIsoClient (K : SSet.{vC}) : components.obj (localize.obj K) ≅ SSet.π₀ K := componentsIso K

theorem componentMapForwardClient {K N : SSet.{vC}} (f : K ⟶ N) :
    components.map (localize.map f) ≫ (componentsIso N).hom =
      (componentsIso K).hom ≫ SSet.π₀Functor.map f := componentsIso_naturality f

theorem componentMapInverseClient {K N : SSet.{vC}} (f : K ⟶ N) :
    SSet.π₀Functor.map f ≫ (componentsIso N).inv =
      (componentsIso K).inv ≫ components.map (localize.map f) := componentsIso_inverse_naturality f

theorem originalMonoidalPairClient (K N : SSet.{vC}) (q : SSet.π₀ K × SSet.π₀ N) :
    Functor.LaxMonoidal.μ SSet.π₀Functor K N q = (SSet.piZeroTensorEquiv K N).symm q :=
  piZeroFunctor_tensor K N q

theorem smallHomUniverseClient {D : Type} [Category.{0} D] [ModelCategory D]
    {κ₀ : Cardinal} [Fact κ₀.IsRegular] [OrderBot κ₀.ord.ToType]
    (d₀ : CofibrantGenerationData D κ₀) (X Y Z : D)
    (f : SSet.π₀ (GeneratedFrameHomComplex.rightSpace d₀ X Y))
    (g : SSet.π₀ (GeneratedFrameHomComplex.rightSpace d₀ Y Z)) :
    GeneratedFrameHomComplex.rightPiZeroEquiv d₀ ((weakEquivalences D).Q) X Z
      (localizedComponentComp d₀ X Y Z f g) =
    GeneratedFrameHomComplex.rightPiZeroEquiv d₀ ((weakEquivalences D).Q) X Y f ≫
      GeneratedFrameHomComplex.rightPiZeroEquiv d₀ ((weakEquivalences D).Q) Y Z g :=
  localizedComponentComp_toHom d₀ ((weakEquivalences D).Q) X Y Z f g

end GeneratedMappingHomCompositionClients
