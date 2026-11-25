/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua
module

public import MathlibExt.CategoryTheory.Enriched.Monoidal.DayConvolution.MonoidalTriangle
public import MathlibExt.CategoryTheory.Enriched.Monoidal.DayConvolution.Pentagon

/-!
# Monoidal

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


variable
  [∀ (F G H J : EnrichedFunctor V I V) (m : I), HasCoproduct (AssociatorQuadLeft.objects d F G H J
    m)]
  [∀ (F G H J : EnrichedFunctor V I V) (m : I), HasCoproduct (AssociatorQuadLeft.relations d F G H J
    m)]
  [∀ (F G H J : EnrichedFunctor V I V) (m : I), HasCoequalizer (AssociatorQuadLeft.map0 d F G H J m)
    (AssociatorQuadLeft.map1 d F G H J m)]
  [∀ (F G H J : EnrichedFunctor V I V) (m : I), HasCoproduct
    (AssociatorPresentation.Left.simultaneousObjects
    (AssociatorIndex.leftIndex d) d.tensorEnrichedFunctor (F.externalTensor G) H J m)]
  [∀ (F G H J : EnrichedFunctor V I V) (m : I), HasCoproduct
    (AssociatorPresentation.Left.simultaneousRelations
    (AssociatorIndex.leftIndex d) d.tensorEnrichedFunctor (F.externalTensor G) H J m)]
  [∀ (F G H J : EnrichedFunctor V I V) (m : I), HasCoequalizer
    (AssociatorPresentation.Left.simultaneousLeftMap
      (AssociatorIndex.leftIndex d) d.tensorEnrichedFunctor (F.externalTensor G) H J m)
    (AssociatorPresentation.Left.simultaneousRightMap
      (AssociatorIndex.leftIndex d) d.tensorEnrichedFunctor (F.externalTensor G) H J m)]
  [∀ (F G H J : EnrichedFunctor V I V) (m : I), ∀ p : I × I, HasCoproduct
    (AssociatorFaces.Left.objects
    (AssociatorIndex.leftIndex d) d.tensorEnrichedFunctor (F.externalTensor G) H J m p)]
  [∀ (F G H J : EnrichedFunctor V I V) (m : I), ∀ p : I × I, HasCoproduct
    (AssociatorFaces.Left.innerRelations
    (AssociatorIndex.leftIndex d) d.tensorEnrichedFunctor (F.externalTensor G) H J m p)]
  [∀ (F G H J : EnrichedFunctor V I V) (m : I), ∀ p : I × I, HasCoequalizer
    (AssociatorFaces.Left.innerLeftMap
      (AssociatorIndex.leftIndex d) d.tensorEnrichedFunctor (F.externalTensor G) H J m p)
    (AssociatorFaces.Left.innerRightMap
      (AssociatorIndex.leftIndex d) d.tensorEnrichedFunctor (F.externalTensor G) H J m p)]
  [∀ (F G H J : EnrichedFunctor V I V) (m : I), ∀ pq : (I × I) × (I × I), HasCoproduct
    (AssociatorPresentation.Left.relationObjects
    (AssociatorIndex.leftIndex d) d.tensorEnrichedFunctor (F.externalTensor G) H J m pq)]
  [∀ (F G H J : EnrichedFunctor V I V) (m : I), ∀ pq : (I × I) × (I × I), HasCoproduct
    (AssociatorPresentation.Left.relationRelations
    (AssociatorIndex.leftIndex d) d.tensorEnrichedFunctor (F.externalTensor G) H J m pq)]
  [∀ (F G H J : EnrichedFunctor V I V) (m : I), ∀ pq : (I × I) × (I × I), HasCoequalizer
    (AssociatorPresentation.Left.relationLeftMap
      (AssociatorIndex.leftIndex d) d.tensorEnrichedFunctor (F.externalTensor G) H J m pq)
    (AssociatorPresentation.Left.relationRightMap
      (AssociatorIndex.leftIndex d) d.tensorEnrichedFunctor (F.externalTensor G) H J m pq)]
  [∀ (F G H J : EnrichedFunctor V I V) (m : I), HasCoproduct
    (AssociatorPresentation.Left.innerObjects
    (AssociatorIndex.leftIndex d) d.tensorEnrichedFunctor (F.externalTensor G) H J m)]
  [∀ (F G H J : EnrichedFunctor V I V) (m : I), HasCoproduct
    (AssociatorPresentation.Left.outerRelations
    (AssociatorIndex.leftIndex d) d.tensorEnrichedFunctor (F.externalTensor G) H J m)]
  [∀ (F G H J : EnrichedFunctor V I V) (m : I), HasCoequalizer
    (AssociatorPresentation.Left.outerLeftMap
      (AssociatorIndex.leftIndex d) d.tensorEnrichedFunctor (F.externalTensor G) H J m)
    (AssociatorPresentation.Left.outerRightMap
      (AssociatorIndex.leftIndex d) d.tensorEnrichedFunctor (F.externalTensor G) H J m)]

/-- The selected genuine Day tensor, associator and tensor maps satisfy the constructor's pentagon.
-/
theorem pentagon (F G H J : EnrichedFunctorCat V I) :
    let : MonoidalCategoryStruct (EnrichedFunctorCat V I) := monoidalStruct d
    ((α_ F G H).hom ⊗ₘ (𝟙 J)) ≫ (α_ F (G ⊗ H) J).hom ≫ ((𝟙 F) ⊗ₘ (α_ G H J).hom) =
      (α_ (F ⊗ G) H J).hom ≫ (α_ F G (H ⊗ J)).hom := by
  let : MonoidalCategoryStruct (EnrichedFunctorCat V I) := monoidalStruct d
  change AssociatorPentagon.secondPath d F G H J = AssociatorPentagon.firstPath d F G H J
  exact AssociatorPentagon.pentagon d F G H J

/-- The monoidal category on the unchanged enriched functor category, with the original chosen Day
  maps. -/
@[instance_reducible]
def monoidalCategory : MonoidalCategory (EnrichedFunctorCat V I) := by
  let : MonoidalCategoryStruct (EnrichedFunctorCat V I) := monoidalStruct d
  refine MonoidalCategory.ofTensorHom ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
  · exact tensor_id d
  · intro F G H g
    rfl
  · intro F G f H
    rfl
  · intro F F' F'' G G' G'' f g f' g'
    exact tensor_comp d f g f' g'
  · intro F G H F' G' H' f g h
    exact associator_natural d f g h
  · intro F G f
    exact leftUnitor_natural d f
  · intro F G f
    exact rightUnitor_natural d f
  · exact pentagon d
  · exact triangle d

end CategoryTheory.EnrichedDayKernel.AssociatorMonoidal
