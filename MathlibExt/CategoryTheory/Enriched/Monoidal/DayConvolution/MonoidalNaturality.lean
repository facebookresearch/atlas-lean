/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua
module

public import MathlibExt.CategoryTheory.Enriched.Monoidal.DayConvolution.MonoidalStructure

/-!
# Monoidal Naturality

Original enriched Day objects, full Hom maps and chosen coend presentations.
-/

@[expose] public section

set_option autoImplicit false
noncomputable section
universe uV vV uI vI
open CategoryTheory CategoryTheory.Limits MonoidalCategory Opposite
open scoped MonoidalClosed
namespace CategoryTheory.EnrichedDayKernel.AssociatorMonoidal
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



/-- The fixed original Day tensor data maps both identities to the actual identity. -/
theorem tensor_id (F G : EnrichedFunctorCat V I) :
    let : MonoidalCategoryStruct (EnrichedFunctorCat V I) := monoidalStruct d
    (𝟙 F) ⊗ₘ (𝟙 G) = 𝟙 (F ⊗ G) := by
  let : MonoidalCategoryStruct (EnrichedFunctorCat V I) := monoidalStruct d
  exact (Input.bifunctor d.tensorEnrichedFunctor).map_id (F, G)

/-- The fixed original Day tensor data preserves source-first composition. -/
theorem tensor_comp {F F' F'' G G' G'' : EnrichedFunctorCat V I}
    (f : F ⟶ F') (g : G ⟶ G') (f' : F' ⟶ F'') (g' : G' ⟶ G'') :
    let : MonoidalCategoryStruct (EnrichedFunctorCat V I) := monoidalStruct d
    (f ⊗ₘ g) ≫ (f' ⊗ₘ g') = (f ≫ f') ⊗ₘ (g ≫ g') := by
  let : MonoidalCategoryStruct (EnrichedFunctorCat V I) := monoidalStruct d
  change (Input.bifunctor d.tensorEnrichedFunctor).map (X := (F, G)) (Y := (F', G')) (f, g) ≫
      (Input.bifunctor d.tensorEnrichedFunctor).map (X := (F', G')) (Y := (F'', G'')) (f', g') =
    (Input.bifunctor d.tensorEnrichedFunctor).map (X := (F, G)) (Y := (F'', G'')) (f ≫ f', g ≫ g')
  exact ((Input.bifunctor d.tensorEnrichedFunctor).map_comp (X := (F, G)) (Y := (F', G'))
    (Z := (F'', G'')) (f, g) (f', g')).symm

/-- The actual three-input natural isomorphism is the fixed Day associator's naturality. -/
theorem associator_natural {F F' G G' H H' : EnrichedFunctorCat V I}
    (f : F ⟶ F') (g : G ⟶ G') (h : H ⟶ H') :
    let : MonoidalCategoryStruct (EnrichedFunctorCat V I) := monoidalStruct d
    ((f ⊗ₘ g) ⊗ₘ h) ≫ (α_ F' G' H').hom = (α_ F G H).hom ≫ (f ⊗ₘ (g ⊗ₘ h)) := by
  let : MonoidalCategoryStruct (EnrichedFunctorCat V I) := monoidalStruct d
  change (AssociatorConstruction.leftTripleFunctor d).map ((f, g), h) ≫
      (AssociatorConstruction.associator d).hom.app ((F', G'), H') =
    (AssociatorConstruction.associator d).hom.app ((F, G), H) ≫
      (AssociatorConstruction.rightTripleFunctor d).map ((f, g), h)
  exact (AssociatorConstruction.associator d).hom.naturality (X := ((F, G), H))
    (Y := ((F', G'), H')) ((f, g), h)

/-- The original fixed-unit genuine natural isomorphism gives the actual Day left unitor's
  naturality. -/
theorem leftUnitor_natural {F G : EnrichedFunctorCat V I} (f : F ⟶ G) :
    let : MonoidalCategoryStruct (EnrichedFunctorCat V I) := monoidalStruct d
    ((𝟙 (𝟙_ (EnrichedFunctorCat V I))) ⊗ₘ f) ≫ (λ_ G).hom = (λ_ F).hom ≫ f := by
  let : MonoidalCategoryStruct (EnrichedFunctorCat V I) := monoidalStruct d
  change (Unitors.leftUnitEndofunctor d).map f ≫ (Unitors.leftUnitorNatIso d).hom.app G =
    (Unitors.leftUnitorNatIso d).hom.app F ≫ (𝟭 (EnrichedFunctorCat V I)).map f
  exact (Unitors.leftUnitorNatIso d).hom.naturality f

/-- The original right unitor is natural for the same chosen genuine Day tensor data. -/
theorem rightUnitor_natural {F G : EnrichedFunctorCat V I} (f : F ⟶ G) :
    let : MonoidalCategoryStruct (EnrichedFunctorCat V I) := monoidalStruct d
    (f ⊗ₘ (𝟙 (𝟙_ (EnrichedFunctorCat V I)))) ≫ (ρ_ G).hom = (ρ_ F).hom ≫ f := by
  let : MonoidalCategoryStruct (EnrichedFunctorCat V I) := monoidalStruct d
  change (Unitors.rightUnitEndofunctor d).map f ≫ (Unitors.rightUnitorNatIso d).hom.app G =
    (Unitors.rightUnitorNatIso d).hom.app F ≫ (𝟭 (EnrichedFunctorCat V I)).map f
  exact (Unitors.rightUnitorNatIso d).hom.naturality f
end CategoryTheory.EnrichedDayKernel.AssociatorMonoidal
