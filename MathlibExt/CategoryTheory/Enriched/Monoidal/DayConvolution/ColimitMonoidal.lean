/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua
module

public import MathlibExt.CategoryTheory.Enriched.Monoidal.DayConvolution.Monoidal

/-!
# Genuine Day convolution from ordinary colimits

Every required original pair, triple and four-input presentation is supplied
by ordinary colimits of the index size. The resulting category retains the
original selected tensor, maps, representable unit and continuous coherence.
The proof-valued suppliers retain the named choices in the exposed construction.
-/

@[expose] public section
set_option autoImplicit false
noncomputable section
universe uV vV uI vI
open CategoryTheory CategoryTheory.Limits MonoidalCategory
open CategoryTheory.EnrichedDayKernel
open scoped MonoidalClosed

namespace CategoryTheory.EnrichedDayKernel.ColimitMonoidal
/-- Colimits of the index size supply ordinary finite-size colimits. -/
theorem smallestColimits (V : Type uV) [Category.{vV} V]
    [HasColimitsOfSize.{uI, uI} V] : HasColimitsOfSize.{0, 0} V :=
  hasColimitsOfSizeShrink.{0, 0} V
attribute [local instance] smallestColimits

variable {V : Type uV} [Category.{vV} V] [MonoidalCategory V]
  [SymmetricCategory V] [MonoidalClosed V]
  {I : Type uI} [Category.{vI} I] [MonoidalCategory I]
  [EnrichedOrdinaryCategory V I] [HasColimitsOfSize.{uI, uI} V]
  (d : EnrichedMonoidalCategoryData V I)
attribute [local instance] Enriched.prodCategory

/-- Ordinary colimits supply this complete original Day presentation family. -/
theorem family_01 :
  ∀ (F G : EnrichedFunctor V I V) (k : I), HasCoproduct (EnrichedDayKernel.objects
      d.tensorEnrichedFunctor F G k) := by
  intros
  infer_instance

attribute [local instance] family_01

/-- Ordinary colimits supply this complete original Day presentation family. -/
theorem family_02 :
  ∀ (F G : EnrichedFunctor V I V) (k : I), HasCoproduct (EnrichedDayKernel.relations
      d.tensorEnrichedFunctor F G k) := by
  intros
  infer_instance

attribute [local instance] family_02

/-- Ordinary colimits supply this complete original Day presentation family. -/
theorem family_03 :
  ∀ (F G : EnrichedFunctor V I V) (k : I), HasCoequalizer (EnrichedDayKernel.leftMap
      d.tensorEnrichedFunctor F G k)
      (EnrichedDayKernel.rightMap d.tensorEnrichedFunctor F G k) := by
  intros
  infer_instance

attribute [local instance] family_03

/-- Ordinary colimits supply this complete original Day presentation family. -/
theorem family_04 :
  ∀ (F G H : EnrichedFunctor V I V) (m : I), HasCoproduct (AssociatorFlat.leftObjects d F G H m) :=
      by
  intros
  infer_instance

attribute [local instance] family_04

/-- Ordinary colimits supply this complete original Day presentation family. -/
theorem family_05 :
  ∀ (F G H : EnrichedFunctor V I V) (m : I), HasCoproduct (AssociatorFlat.leftRelations d F G H m)
      := by
  intros
  infer_instance

attribute [local instance] family_05

/-- Ordinary colimits supply this complete original Day presentation family. -/
theorem family_06 :
  ∀ (F G H : EnrichedFunctor V I V) (m : I), HasCoequalizer (AssociatorFlat.leftMap0 d F G H m)
      (AssociatorFlat.leftMap1 d F G H m) := by
  intros
  infer_instance

attribute [local instance] family_06

/-- Ordinary colimits supply this complete original Day presentation family. -/
theorem family_07 :
  ∀ (F G H : EnrichedFunctor V I V) (m : I), HasCoproduct
      (AssociatorPresentation.Left.simultaneousObjects d.tensorEnrichedFunctor
      d.tensorEnrichedFunctor F G H m) := by
  intros
  infer_instance

attribute [local instance] family_07

/-- Ordinary colimits supply this complete original Day presentation family. -/
theorem family_08 :
  ∀ (F G H : EnrichedFunctor V I V) (m : I), HasCoproduct
      (AssociatorPresentation.Left.simultaneousRelations d.tensorEnrichedFunctor
      d.tensorEnrichedFunctor F G H m) := by
  intros
  infer_instance

attribute [local instance] family_08

/-- Ordinary colimits supply this complete original Day presentation family. -/
theorem family_09 :
  ∀ (F G H : EnrichedFunctor V I V) (m : I), HasCoequalizer
      (AssociatorPresentation.Left.simultaneousLeftMap d.tensorEnrichedFunctor
        d.tensorEnrichedFunctor F G H m)
      (AssociatorPresentation.Left.simultaneousRightMap d.tensorEnrichedFunctor
        d.tensorEnrichedFunctor F G H m) := by
  intros
  infer_instance

attribute [local instance] family_09

/-- Ordinary colimits supply this complete original Day presentation family. -/
theorem family_10 :
  ∀ (F G H : EnrichedFunctor V I V) (m : I), ∀ p : I × I, HasCoproduct
      (AssociatorFaces.Left.objects d.tensorEnrichedFunctor d.tensorEnrichedFunctor F G H m p) := by
  intros
  infer_instance

attribute [local instance] family_10

/-- Ordinary colimits supply this complete original Day presentation family. -/
theorem family_11 :
  ∀ (F G H : EnrichedFunctor V I V) (m : I), ∀ p : I × I, HasCoproduct
      (AssociatorFaces.Left.innerRelations d.tensorEnrichedFunctor d.tensorEnrichedFunctor F G H m
      p) := by
  intros
  infer_instance

attribute [local instance] family_11

/-- Ordinary colimits supply this complete original Day presentation family. -/
theorem family_12 :
  ∀ (F G H : EnrichedFunctor V I V) (m : I), ∀ p : I × I, HasCoequalizer
      (AssociatorFaces.Left.innerLeftMap d.tensorEnrichedFunctor d.tensorEnrichedFunctor F G H m p)
      (AssociatorFaces.Left.innerRightMap d.tensorEnrichedFunctor d.tensorEnrichedFunctor F G H m
        p) := by
  intros
  infer_instance

attribute [local instance] family_12

/-- Ordinary colimits supply this complete original Day presentation family. -/
theorem family_13 :
  ∀ (F G H : EnrichedFunctor V I V) (m : I), ∀ pq : (I × I) × (I × I), HasCoproduct
      (AssociatorPresentation.Left.relationObjects d.tensorEnrichedFunctor d.tensorEnrichedFunctor
        F G H m pq) := by
  intros
  infer_instance

attribute [local instance] family_13

/-- Ordinary colimits supply this complete original Day presentation family. -/
theorem family_14 :
  ∀ (F G H : EnrichedFunctor V I V) (m : I), ∀ pq : (I × I) × (I × I), HasCoproduct
      (AssociatorPresentation.Left.relationRelations d.tensorEnrichedFunctor
        d.tensorEnrichedFunctor F G H m pq) := by
  intros
  infer_instance

attribute [local instance] family_14

/-- Ordinary colimits supply this complete original Day presentation family. -/
theorem family_15 :
  ∀ (F G H : EnrichedFunctor V I V) (m : I), ∀ pq : (I × I) × (I × I), HasCoequalizer
      (AssociatorPresentation.Left.relationLeftMap d.tensorEnrichedFunctor d.tensorEnrichedFunctor
        F G H m pq)
      (AssociatorPresentation.Left.relationRightMap d.tensorEnrichedFunctor d.tensorEnrichedFunctor
        F G H m pq) := by
  intros
  infer_instance

attribute [local instance] family_15

/-- Ordinary colimits supply this complete original Day presentation family. -/
theorem family_16 :
  ∀ (F G H : EnrichedFunctor V I V) (m : I), HasCoproduct (AssociatorPresentation.Left.innerObjects
      d.tensorEnrichedFunctor d.tensorEnrichedFunctor F G H m) := by
  intros
  infer_instance

attribute [local instance] family_16

/-- Ordinary colimits supply this complete original Day presentation family. -/
theorem family_17 :
  ∀ (F G H : EnrichedFunctor V I V) (m : I), HasCoproduct
      (AssociatorPresentation.Left.outerRelations d.tensorEnrichedFunctor d.tensorEnrichedFunctor F
      G H m) := by
  intros
  infer_instance

attribute [local instance] family_17

/-- Ordinary colimits supply this complete original Day presentation family. -/
theorem family_18 :
  ∀ (F G H : EnrichedFunctor V I V) (m : I), HasCoequalizer
      (AssociatorPresentation.Left.outerLeftMap d.tensorEnrichedFunctor d.tensorEnrichedFunctor F G
        H m)
      (AssociatorPresentation.Left.outerRightMap d.tensorEnrichedFunctor d.tensorEnrichedFunctor F
        G H m) := by
  intros
  infer_instance

attribute [local instance] family_18

/-- Ordinary colimits supply this complete original Day presentation family. -/
theorem family_19 :
  ∀ (F G H : EnrichedFunctor V I V) (m : I), HasCoproduct (AssociatorFlat.rightObjects d F G H m)
      := by
  intros
  infer_instance

attribute [local instance] family_19

/-- Ordinary colimits supply this complete original Day presentation family. -/
theorem family_20 :
  ∀ (F G H : EnrichedFunctor V I V) (m : I), HasCoproduct (AssociatorFlat.rightRelations d F G H m)
      := by
  intros
  infer_instance

attribute [local instance] family_20

/-- Ordinary colimits supply this complete original Day presentation family. -/
theorem family_21 :
  ∀ (F G H : EnrichedFunctor V I V) (m : I), HasCoequalizer (AssociatorFlat.rightMap0 d F G H m)
      (AssociatorFlat.rightMap1 d F G H m) := by
  intros
  infer_instance

attribute [local instance] family_21

/-- Ordinary colimits supply this complete original Day presentation family. -/
theorem family_22 :
  ∀ (F G H : EnrichedFunctor V I V) (m : I), HasCoproduct
      (AssociatorPresentation.Right.simultaneousObjects d.tensorEnrichedFunctor
      d.tensorEnrichedFunctor G H F m) := by
  intros
  infer_instance

attribute [local instance] family_22

/-- Ordinary colimits supply this complete original Day presentation family. -/
theorem family_23 :
  ∀ (F G H : EnrichedFunctor V I V) (m : I), HasCoproduct
      (AssociatorPresentation.Right.simultaneousRelations d.tensorEnrichedFunctor
      d.tensorEnrichedFunctor G H F m) := by
  intros
  infer_instance

attribute [local instance] family_23

/-- Ordinary colimits supply this complete original Day presentation family. -/
theorem family_24 :
  ∀ (F G H : EnrichedFunctor V I V) (m : I), HasCoequalizer
      (AssociatorPresentation.Right.simultaneousLeftMap d.tensorEnrichedFunctor
        d.tensorEnrichedFunctor G H F m)
      (AssociatorPresentation.Right.simultaneousRightMap d.tensorEnrichedFunctor
        d.tensorEnrichedFunctor G H F m) := by
  intros
  infer_instance

attribute [local instance] family_24

/-- Ordinary colimits supply this complete original Day presentation family. -/
theorem family_25 :
  ∀ (F G H : EnrichedFunctor V I V) (m : I), ∀ p : I × I, HasCoproduct
      (AssociatorFaces.Right.objects d.tensorEnrichedFunctor d.tensorEnrichedFunctor G H F m p) :=
      by
  intros
  infer_instance

attribute [local instance] family_25

/-- Ordinary colimits supply this complete original Day presentation family. -/
theorem family_26 :
  ∀ (F G H : EnrichedFunctor V I V) (m : I), ∀ p : I × I, HasCoproduct
      (AssociatorFaces.Right.innerRelations d.tensorEnrichedFunctor d.tensorEnrichedFunctor G H F m
      p) := by
  intros
  infer_instance

attribute [local instance] family_26

/-- Ordinary colimits supply this complete original Day presentation family. -/
theorem family_27 :
  ∀ (F G H : EnrichedFunctor V I V) (m : I), ∀ p : I × I, HasCoequalizer
      (AssociatorFaces.Right.innerLeftMap d.tensorEnrichedFunctor d.tensorEnrichedFunctor G H F m p)
      (AssociatorFaces.Right.innerRightMap d.tensorEnrichedFunctor d.tensorEnrichedFunctor G H F m
        p) := by
  intros
  infer_instance

attribute [local instance] family_27

/-- Ordinary colimits supply this complete original Day presentation family. -/
theorem family_28 :
  ∀ (F G H : EnrichedFunctor V I V) (m : I), ∀ pq : (I × I) × (I × I), HasCoproduct
      (AssociatorPresentation.Right.relationObjects d.tensorEnrichedFunctor d.tensorEnrichedFunctor
        G H F m pq) := by
  intros
  infer_instance

attribute [local instance] family_28

/-- Ordinary colimits supply this complete original Day presentation family. -/
theorem family_29 :
  ∀ (F G H : EnrichedFunctor V I V) (m : I), ∀ pq : (I × I) × (I × I), HasCoproduct
      (AssociatorPresentation.Right.relationRelations d.tensorEnrichedFunctor
        d.tensorEnrichedFunctor G H F m pq) := by
  intros
  infer_instance

attribute [local instance] family_29

/-- Ordinary colimits supply this complete original Day presentation family. -/
theorem family_30 :
  ∀ (F G H : EnrichedFunctor V I V) (m : I), ∀ pq : (I × I) × (I × I), HasCoequalizer
      (AssociatorPresentation.Right.relationLeftMap d.tensorEnrichedFunctor d.tensorEnrichedFunctor
        G H F m pq)
      (AssociatorPresentation.Right.relationRightMap d.tensorEnrichedFunctor
        d.tensorEnrichedFunctor G H F m pq) := by
  intros
  infer_instance

attribute [local instance] family_30

/-- Ordinary colimits supply this complete original Day presentation family. -/
theorem family_31 :
  ∀ (F G H : EnrichedFunctor V I V) (m : I), HasCoproduct
      (AssociatorPresentation.Right.innerObjects d.tensorEnrichedFunctor d.tensorEnrichedFunctor G
      H F m) := by
  intros
  infer_instance

attribute [local instance] family_31

/-- Ordinary colimits supply this complete original Day presentation family. -/
theorem family_32 :
  ∀ (F G H : EnrichedFunctor V I V) (m : I), HasCoproduct
      (AssociatorPresentation.Right.outerRelations d.tensorEnrichedFunctor d.tensorEnrichedFunctor
      G H F m) := by
  intros
  infer_instance

attribute [local instance] family_32

/-- Ordinary colimits supply this complete original Day presentation family. -/
theorem family_33 :
  ∀ (F G H : EnrichedFunctor V I V) (m : I), HasCoequalizer
      (AssociatorPresentation.Right.outerLeftMap d.tensorEnrichedFunctor d.tensorEnrichedFunctor G
        H F m)
      (AssociatorPresentation.Right.outerRightMap d.tensorEnrichedFunctor d.tensorEnrichedFunctor G
        H F m) := by
  intros
  infer_instance

attribute [local instance] family_33

/-- Ordinary colimits supply this complete original Day presentation family. -/
theorem family_34 :
  ∀ (F G H J : EnrichedFunctor V I V) (m : I), HasCoproduct (AssociatorQuadLeft.objects d F G H J
      m) := by
  intros
  infer_instance

attribute [local instance] family_34

/-- Ordinary colimits supply this complete original Day presentation family. -/
theorem family_35 :
  ∀ (F G H J : EnrichedFunctor V I V) (m : I), HasCoproduct (AssociatorQuadLeft.relations d F G H J
      m) := by
  intros
  infer_instance

attribute [local instance] family_35

/-- Ordinary colimits supply this complete original Day presentation family. -/
theorem family_36 :
  ∀ (F G H J : EnrichedFunctor V I V) (m : I), HasCoequalizer (AssociatorQuadLeft.map0 d F G H J m)
      (AssociatorQuadLeft.map1 d F G H J m) := by
  intros
  infer_instance

attribute [local instance] family_36

/-- Ordinary colimits supply this complete original Day presentation family. -/
theorem family_37 :
  ∀ (F G H J : EnrichedFunctor V I V) (m : I), HasCoproduct
      (AssociatorPresentation.Left.simultaneousObjects
      (AssociatorIndex.leftIndex d) d.tensorEnrichedFunctor (F.externalTensor G) H J m) := by
  intros
  infer_instance

attribute [local instance] family_37

/-- Ordinary colimits supply this complete original Day presentation family. -/
theorem family_38 :
  ∀ (F G H J : EnrichedFunctor V I V) (m : I), HasCoproduct
      (AssociatorPresentation.Left.simultaneousRelations
      (AssociatorIndex.leftIndex d) d.tensorEnrichedFunctor (F.externalTensor G) H J m) := by
  intros
  infer_instance

attribute [local instance] family_38

/-- Ordinary colimits supply this complete original Day presentation family. -/
theorem family_39 :
  ∀ (F G H J : EnrichedFunctor V I V) (m : I), HasCoequalizer
      (AssociatorPresentation.Left.simultaneousLeftMap
        (AssociatorIndex.leftIndex d) d.tensorEnrichedFunctor (F.externalTensor G) H J m)
      (AssociatorPresentation.Left.simultaneousRightMap
        (AssociatorIndex.leftIndex d) d.tensorEnrichedFunctor (F.externalTensor G) H J m) := by
  intros
  infer_instance

attribute [local instance] family_39

/-- Ordinary colimits supply this complete original Day presentation family. -/
theorem family_40 :
  ∀ (F G H J : EnrichedFunctor V I V) (m : I), ∀ p : I × I, HasCoproduct
      (AssociatorFaces.Left.objects
      (AssociatorIndex.leftIndex d) d.tensorEnrichedFunctor (F.externalTensor G) H J m p) := by
  intros
  infer_instance

attribute [local instance] family_40

/-- Ordinary colimits supply this complete original Day presentation family. -/
theorem family_41 :
  ∀ (F G H J : EnrichedFunctor V I V) (m : I), ∀ p : I × I, HasCoproduct
      (AssociatorFaces.Left.innerRelations
      (AssociatorIndex.leftIndex d) d.tensorEnrichedFunctor (F.externalTensor G) H J m p) := by
  intros
  infer_instance

attribute [local instance] family_41

/-- Ordinary colimits supply this complete original Day presentation family. -/
theorem family_42 :
  ∀ (F G H J : EnrichedFunctor V I V) (m : I), ∀ p : I × I, HasCoequalizer
      (AssociatorFaces.Left.innerLeftMap
        (AssociatorIndex.leftIndex d) d.tensorEnrichedFunctor (F.externalTensor G) H J m p)
      (AssociatorFaces.Left.innerRightMap
        (AssociatorIndex.leftIndex d) d.tensorEnrichedFunctor (F.externalTensor G) H J m p) := by
  intros
  infer_instance

attribute [local instance] family_42

/-- Ordinary colimits supply this complete original Day presentation family. -/
theorem family_43 :
  ∀ (F G H J : EnrichedFunctor V I V) (m : I), ∀ pq : (I × I) × (I × I), HasCoproduct
      (AssociatorPresentation.Left.relationObjects
      (AssociatorIndex.leftIndex d) d.tensorEnrichedFunctor (F.externalTensor G) H J m pq) := by
  intros
  infer_instance

attribute [local instance] family_43

/-- Ordinary colimits supply this complete original Day presentation family. -/
theorem family_44 :
  ∀ (F G H J : EnrichedFunctor V I V) (m : I), ∀ pq : (I × I) × (I × I), HasCoproduct
      (AssociatorPresentation.Left.relationRelations
      (AssociatorIndex.leftIndex d) d.tensorEnrichedFunctor (F.externalTensor G) H J m pq) := by
  intros
  infer_instance

attribute [local instance] family_44

/-- Ordinary colimits supply this complete original Day presentation family. -/
theorem family_45 :
  ∀ (F G H J : EnrichedFunctor V I V) (m : I), ∀ pq : (I × I) × (I × I), HasCoequalizer
      (AssociatorPresentation.Left.relationLeftMap
        (AssociatorIndex.leftIndex d) d.tensorEnrichedFunctor (F.externalTensor G) H J m pq)
      (AssociatorPresentation.Left.relationRightMap
        (AssociatorIndex.leftIndex d) d.tensorEnrichedFunctor (F.externalTensor G) H J m pq) := by
  intros
  infer_instance

attribute [local instance] family_45

/-- Ordinary colimits supply this complete original Day presentation family. -/
theorem family_46 :
  ∀ (F G H J : EnrichedFunctor V I V) (m : I), HasCoproduct
      (AssociatorPresentation.Left.innerObjects
      (AssociatorIndex.leftIndex d) d.tensorEnrichedFunctor (F.externalTensor G) H J m) := by
  intros
  infer_instance

attribute [local instance] family_46

/-- Ordinary colimits supply this complete original Day presentation family. -/
theorem family_47 :
  ∀ (F G H J : EnrichedFunctor V I V) (m : I), HasCoproduct
      (AssociatorPresentation.Left.outerRelations
      (AssociatorIndex.leftIndex d) d.tensorEnrichedFunctor (F.externalTensor G) H J m) := by
  intros
  infer_instance

attribute [local instance] family_47

/-- Ordinary colimits supply this complete original Day presentation family. -/
theorem family_48 :
  ∀ (F G H J : EnrichedFunctor V I V) (m : I), HasCoequalizer
      (AssociatorPresentation.Left.outerLeftMap
        (AssociatorIndex.leftIndex d) d.tensorEnrichedFunctor (F.externalTensor G) H J m)
      (AssociatorPresentation.Left.outerRightMap
        (AssociatorIndex.leftIndex d) d.tensorEnrichedFunctor (F.externalTensor G) H J m) := by
  intros
  infer_instance

attribute [local instance] family_48

/-- The original genuine Day category is supplied by actual ordinary colimits of the index size. -/
@[instance_reducible]
def monoidalCategory : MonoidalCategory (EnrichedFunctorCat V I) :=
  AssociatorMonoidal.monoidalCategory d


/-- The tensor objects are the original selected genuine Day objects. -/
theorem tensorObj_eq (F G : EnrichedFunctorCat V I) :
    let : MonoidalCategory (EnrichedFunctorCat V I) := monoidalCategory d
    F ⊗ G = (Input.bifunctor d.tensorEnrichedFunctor).obj (F, G) := rfl

/-- Every whole tensor map is the original selected genuine Day input map. -/
theorem tensorHom_eq {F F' G G' : EnrichedFunctorCat V I} (f : F ⟶ F') (g : G ⟶ G') :
    let : MonoidalCategory (EnrichedFunctorCat V I) := monoidalCategory d
    f ⊗ₘ g = (Input.bifunctor d.tensorEnrichedFunctor).map
      (X := (F, G)) (Y := (F', G')) (f, g) := rfl

/-- The associator is the complete original continuous coend comparison. -/
theorem associator_eq (F G H : EnrichedFunctorCat V I) :
    let : MonoidalCategory (EnrichedFunctorCat V I) := monoidalCategory d
    (α_ F G H) = AssociatorConstruction.functorIso d
      F.toEnrichedFunctor G.toEnrichedFunctor H.toEnrichedFunctor := rfl

/-- The tensor unit is the original enriched representable at the index unit. -/
theorem tensorUnit_eq :
    let : MonoidalCategory (EnrichedFunctorCat V I) := monoidalCategory d
    𝟙_ (EnrichedFunctorCat V I) = ⟨GradedYoneda.representable (V := V) (𝟙_ I)⟩ := rfl

/-- The left unitor is the original continuous representable Day map. -/
theorem leftUnitor_eq (F : EnrichedFunctorCat V I) :
    let : MonoidalCategory (EnrichedFunctorCat V I) := monoidalCategory d
    (λ_ F) = Unitors.leftUnitor d F.toEnrichedFunctor := rfl

/-- The right unitor is the original continuous representable Day map. -/
theorem rightUnitor_eq (F : EnrichedFunctorCat V I) :
    let : MonoidalCategory (EnrichedFunctorCat V I) := monoidalCategory d
    (ρ_ F) = Unitors.rightUnitor d F.toEnrichedFunctor := rfl

/-- The actual original four-input maps satisfy the monoidal pentagon. -/
theorem pentagon (F G H J : EnrichedFunctorCat V I) :
    let : MonoidalCategory (EnrichedFunctorCat V I) := monoidalCategory d
    (α_ F G H).hom ▷ J ≫ (α_ F (G ⊗ H) J).hom ≫ F ◁ (α_ G H J).hom =
      (α_ (F ⊗ G) H J).hom ≫ (α_ F G (H ⊗ J)).hom := by
  let : MonoidalCategory (EnrichedFunctorCat V I) := monoidalCategory d
  exact MonoidalCategory.pentagon F G H J

/-- The actual original representable-unit maps satisfy the monoidal triangle. -/
theorem triangle (F G : EnrichedFunctorCat V I) :
    let : MonoidalCategory (EnrichedFunctorCat V I) := monoidalCategory d
    (α_ F (𝟙_ (EnrichedFunctorCat V I)) G).hom ≫ F ◁ (λ_ G).hom = (ρ_ F).hom ▷ G := by
  let : MonoidalCategory (EnrichedFunctorCat V I) := monoidalCategory d
  exact MonoidalCategory.triangle F G

end CategoryTheory.EnrichedDayKernel.ColimitMonoidal
