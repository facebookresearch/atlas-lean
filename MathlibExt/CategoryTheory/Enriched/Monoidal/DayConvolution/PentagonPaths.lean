/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua
module

public import MathlibExt.CategoryTheory.Enriched.Monoidal.DayConvolution.MonoidalNaturality
public import MathlibExt.CategoryTheory.Enriched.Monoidal.DayConvolution.AssociatorQuadNested

/-!
# Pentagon Paths

Original enriched Day objects, full Hom maps and chosen coend presentations.
-/

@[expose] public section

set_option autoImplicit false
noncomputable section
universe uV vV uI vI
open CategoryTheory CategoryTheory.Limits MonoidalCategory Opposite
open scoped MonoidalClosed
namespace CategoryTheory.EnrichedDayKernel.AssociatorPentagon
variable {V : Type uV} [Category.{vV} V] [MonoidalCategory V]
  [SymmetricCategory V] [MonoidalClosed V]
  {I : Type uI} [Category.{vI} I] [MonoidalCategory I] [EnrichedOrdinaryCategory V I]
  (d : EnrichedMonoidalCategoryData V I)
attribute [local instance] Enriched.prodCategory
variable
  [∀ (F G : EnrichedFunctor V I V) (k : I), HasCoproduct (EnrichedDayKernel.objects
    d.tensorEnrichedFunctor F G k)]
  [∀ (F G : EnrichedFunctor V I V) (k : I), HasCoproduct (EnrichedDayKernel.relations
    d.tensorEnrichedFunctor F G k)]
  [∀ (F G : EnrichedFunctor V I V) (k : I), HasCoequalizer (EnrichedDayKernel.leftMap
    d.tensorEnrichedFunctor F G k)
    (EnrichedDayKernel.rightMap d.tensorEnrichedFunctor F G k)]

variable
  [∀ (F G H : EnrichedFunctor V I V) (m : I), HasCoproduct (AssociatorFlat.leftObjects d F G H m)]
  [∀ (F G H : EnrichedFunctor V I V) (m : I), HasCoproduct (AssociatorFlat.leftRelations d F G H m)]
  [∀ (F G H : EnrichedFunctor V I V) (m : I), HasCoequalizer (AssociatorFlat.leftMap0 d F G H m)
    (AssociatorFlat.leftMap1 d F G H m)]
  [∀ (F G H : EnrichedFunctor V I V) (m : I), HasCoproduct
    (AssociatorPresentation.Left.simultaneousObjects d.tensorEnrichedFunctor d.tensorEnrichedFunctor
    F G H m)]
  [∀ (F G H : EnrichedFunctor V I V) (m : I), HasCoproduct
    (AssociatorPresentation.Left.simultaneousRelations d.tensorEnrichedFunctor
    d.tensorEnrichedFunctor F G H m)]
  [∀ (F G H : EnrichedFunctor V I V) (m : I), HasCoequalizer
    (AssociatorPresentation.Left.simultaneousLeftMap d.tensorEnrichedFunctor d.tensorEnrichedFunctor
      F G H m)
    (AssociatorPresentation.Left.simultaneousRightMap d.tensorEnrichedFunctor
      d.tensorEnrichedFunctor F G H m)]
  [∀ (F G H : EnrichedFunctor V I V) (m : I), ∀ p : I × I, HasCoproduct
    (AssociatorFaces.Left.objects d.tensorEnrichedFunctor d.tensorEnrichedFunctor F G H m p)]
  [∀ (F G H : EnrichedFunctor V I V) (m : I), ∀ p : I × I, HasCoproduct
    (AssociatorFaces.Left.innerRelations d.tensorEnrichedFunctor d.tensorEnrichedFunctor F G H m p)]
  [∀ (F G H : EnrichedFunctor V I V) (m : I), ∀ p : I × I, HasCoequalizer
    (AssociatorFaces.Left.innerLeftMap d.tensorEnrichedFunctor d.tensorEnrichedFunctor F G H m p)
    (AssociatorFaces.Left.innerRightMap d.tensorEnrichedFunctor d.tensorEnrichedFunctor F G H m p)]
  [∀ (F G H : EnrichedFunctor V I V) (m : I), ∀ pq : (I × I) × (I × I), HasCoproduct
    (AssociatorPresentation.Left.relationObjects d.tensorEnrichedFunctor d.tensorEnrichedFunctor F G
      H m pq)]
  [∀ (F G H : EnrichedFunctor V I V) (m : I), ∀ pq : (I × I) × (I × I), HasCoproduct
    (AssociatorPresentation.Left.relationRelations d.tensorEnrichedFunctor d.tensorEnrichedFunctor F
      G H m pq)]
  [∀ (F G H : EnrichedFunctor V I V) (m : I), ∀ pq : (I × I) × (I × I), HasCoequalizer
    (AssociatorPresentation.Left.relationLeftMap d.tensorEnrichedFunctor d.tensorEnrichedFunctor F G
      H m pq)
    (AssociatorPresentation.Left.relationRightMap d.tensorEnrichedFunctor d.tensorEnrichedFunctor F
      G H m pq)]
  [∀ (F G H : EnrichedFunctor V I V) (m : I), HasCoproduct (AssociatorPresentation.Left.innerObjects
    d.tensorEnrichedFunctor d.tensorEnrichedFunctor F G H m)]
  [∀ (F G H : EnrichedFunctor V I V) (m : I), HasCoproduct
    (AssociatorPresentation.Left.outerRelations d.tensorEnrichedFunctor d.tensorEnrichedFunctor F G
    H m)]
  [∀ (F G H : EnrichedFunctor V I V) (m : I), HasCoequalizer
    (AssociatorPresentation.Left.outerLeftMap d.tensorEnrichedFunctor d.tensorEnrichedFunctor F G H
      m)
    (AssociatorPresentation.Left.outerRightMap d.tensorEnrichedFunctor d.tensorEnrichedFunctor F G H
      m)]
  [∀ (F G H : EnrichedFunctor V I V) (m : I), HasCoproduct (AssociatorFlat.rightObjects d F G H m)]
  [∀ (F G H : EnrichedFunctor V I V) (m : I), HasCoproduct (AssociatorFlat.rightRelations d F G H
    m)]
  [∀ (F G H : EnrichedFunctor V I V) (m : I), HasCoequalizer (AssociatorFlat.rightMap0 d F G H m)
    (AssociatorFlat.rightMap1 d F G H m)]
  [∀ (F G H : EnrichedFunctor V I V) (m : I), HasCoproduct
    (AssociatorPresentation.Right.simultaneousObjects d.tensorEnrichedFunctor
    d.tensorEnrichedFunctor G H F m)]
  [∀ (F G H : EnrichedFunctor V I V) (m : I), HasCoproduct
    (AssociatorPresentation.Right.simultaneousRelations d.tensorEnrichedFunctor
    d.tensorEnrichedFunctor G H F m)]
  [∀ (F G H : EnrichedFunctor V I V) (m : I), HasCoequalizer
    (AssociatorPresentation.Right.simultaneousLeftMap d.tensorEnrichedFunctor
      d.tensorEnrichedFunctor G H F m)
    (AssociatorPresentation.Right.simultaneousRightMap d.tensorEnrichedFunctor
      d.tensorEnrichedFunctor G H F m)]
  [∀ (F G H : EnrichedFunctor V I V) (m : I), ∀ p : I × I, HasCoproduct
    (AssociatorFaces.Right.objects d.tensorEnrichedFunctor d.tensorEnrichedFunctor G H F m p)]
  [∀ (F G H : EnrichedFunctor V I V) (m : I), ∀ p : I × I, HasCoproduct
    (AssociatorFaces.Right.innerRelations d.tensorEnrichedFunctor d.tensorEnrichedFunctor G H F m
    p)]
  [∀ (F G H : EnrichedFunctor V I V) (m : I), ∀ p : I × I, HasCoequalizer
    (AssociatorFaces.Right.innerLeftMap d.tensorEnrichedFunctor d.tensorEnrichedFunctor G H F m p)
    (AssociatorFaces.Right.innerRightMap d.tensorEnrichedFunctor d.tensorEnrichedFunctor G H F m p)]
  [∀ (F G H : EnrichedFunctor V I V) (m : I), ∀ pq : (I × I) × (I × I), HasCoproduct
    (AssociatorPresentation.Right.relationObjects d.tensorEnrichedFunctor d.tensorEnrichedFunctor G
      H F m pq)]
  [∀ (F G H : EnrichedFunctor V I V) (m : I), ∀ pq : (I × I) × (I × I), HasCoproduct
    (AssociatorPresentation.Right.relationRelations d.tensorEnrichedFunctor d.tensorEnrichedFunctor
      G H F m pq)]
  [∀ (F G H : EnrichedFunctor V I V) (m : I), ∀ pq : (I × I) × (I × I), HasCoequalizer
    (AssociatorPresentation.Right.relationLeftMap d.tensorEnrichedFunctor d.tensorEnrichedFunctor G
      H F m pq)
    (AssociatorPresentation.Right.relationRightMap d.tensorEnrichedFunctor d.tensorEnrichedFunctor G
      H F m pq)]
  [∀ (F G H : EnrichedFunctor V I V) (m : I), HasCoproduct
    (AssociatorPresentation.Right.innerObjects d.tensorEnrichedFunctor d.tensorEnrichedFunctor G H F
    m)]
  [∀ (F G H : EnrichedFunctor V I V) (m : I), HasCoproduct
    (AssociatorPresentation.Right.outerRelations d.tensorEnrichedFunctor d.tensorEnrichedFunctor G H
    F m)]
  [∀ (F G H : EnrichedFunctor V I V) (m : I), HasCoequalizer
    (AssociatorPresentation.Right.outerLeftMap d.tensorEnrichedFunctor d.tensorEnrichedFunctor G H F
      m)
    (AssociatorPresentation.Right.outerRightMap d.tensorEnrichedFunctor d.tensorEnrichedFunctor G H
      F m)]



open AssociatorQuadNested

/-- The original short nested pentagon path on the actual Day bifunctor. -/
abbrev firstPath (F G H J : EnrichedFunctorCat V I) :
    (⟨day d (day d (day d F.toEnrichedFunctor G.toEnrichedFunctor) H.toEnrichedFunctor)
      J.toEnrichedFunctor⟩ :
      EnrichedFunctorCat V I) ⟶
    (⟨day d F.toEnrichedFunctor (day d G.toEnrichedFunctor (day d H.toEnrichedFunctor
      J.toEnrichedFunctor))⟩ :
      EnrichedFunctorCat V I) :=
  (AssociatorConstruction.functorIso d (day d F.toEnrichedFunctor G.toEnrichedFunctor)
    H.toEnrichedFunctor J.toEnrichedFunctor).hom ≫
    (AssociatorConstruction.functorIso d F.toEnrichedFunctor G.toEnrichedFunctor
      (day d H.toEnrichedFunctor J.toEnrichedFunctor)).hom

/-- The original long nested pentagon path, using precisely both Day tensor maps. -/
abbrev secondPath (F G H J : EnrichedFunctorCat V I) :
    (⟨day d (day d (day d F.toEnrichedFunctor G.toEnrichedFunctor) H.toEnrichedFunctor)
      J.toEnrichedFunctor⟩ :
      EnrichedFunctorCat V I) ⟶
    (⟨day d F.toEnrichedFunctor (day d G.toEnrichedFunctor (day d H.toEnrichedFunctor
      J.toEnrichedFunctor))⟩ :
      EnrichedFunctorCat V I) :=
  (Input.bifunctor d.tensorEnrichedFunctor).map
    (X := (⟨day d (day d F.toEnrichedFunctor G.toEnrichedFunctor) H.toEnrichedFunctor⟩, J))
    (Y := (⟨day d F.toEnrichedFunctor (day d G.toEnrichedFunctor H.toEnrichedFunctor)⟩, J))
    ((AssociatorConstruction.functorIso d F.toEnrichedFunctor G.toEnrichedFunctor
      H.toEnrichedFunctor).hom, 𝟙 J) ≫
  (AssociatorConstruction.functorIso d F.toEnrichedFunctor
    (day d G.toEnrichedFunctor H.toEnrichedFunctor) J.toEnrichedFunctor).hom ≫
  (Input.bifunctor d.tensorEnrichedFunctor).map
    (X := (F, ⟨day d (day d G.toEnrichedFunctor H.toEnrichedFunctor) J.toEnrichedFunctor⟩))
    (Y := (F, ⟨day d G.toEnrichedFunctor (day d H.toEnrichedFunctor J.toEnrichedFunctor)⟩))
    (𝟙 F, (AssociatorConstruction.functorIso d G.toEnrichedFunctor H.toEnrichedFunctor
      J.toEnrichedFunctor).hom)

/-- Each short-path component keeps both actual original component associators. -/
theorem firstPath_component (F G H J : EnrichedFunctorCat V I) (m : I) :
    EnrichedFunctorCat.component (firstPath d F G H J) m =
      (AssociatorConstruction.componentIso d (day d F.toEnrichedFunctor G.toEnrichedFunctor)
        H.toEnrichedFunctor J.toEnrichedFunctor m).hom ≫
      (AssociatorConstruction.componentIso d F.toEnrichedFunctor G.toEnrichedFunctor
        (day d H.toEnrichedFunctor J.toEnrichedFunctor) m).hom := by
  rw [EnrichedFunctorCat.component_comp, AssociatorConstruction.functorIso_hom_component,
    AssociatorConstruction.functorIso_hom_component]

/-- Each long-path component keeps both full tensor maps and the original middle associator. -/
theorem secondPath_component (F G H J : EnrichedFunctorCat V I) (m : I) :
    EnrichedFunctorCat.component (secondPath d F G H J) m =
      Input.mapAt d.tensorEnrichedFunctor
        (AssociatorConstruction.functorIso d F.toEnrichedFunctor G.toEnrichedFunctor
          H.toEnrichedFunctor).hom
        (GradedNatTrans.unitId J.toEnrichedFunctor) m ≫
      (AssociatorConstruction.componentIso d F.toEnrichedFunctor
        (day d G.toEnrichedFunctor H.toEnrichedFunctor) J.toEnrichedFunctor m).hom ≫
      Input.mapAt d.tensorEnrichedFunctor (GradedNatTrans.unitId F.toEnrichedFunctor)
        (AssociatorConstruction.functorIso d G.toEnrichedFunctor H.toEnrichedFunctor
          J.toEnrichedFunctor).hom m := by
  rw [EnrichedFunctorCat.component_comp, EnrichedFunctorCat.component_comp,
    Input.bifunctor_map_component, AssociatorConstruction.functorIso_hom_component,
    Input.bifunctor_map_component]
  rfl

end CategoryTheory.EnrichedDayKernel.AssociatorPentagon
