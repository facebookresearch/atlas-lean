/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua
module

public import MathlibExt.CategoryTheory.Enriched.Monoidal.DayConvolution.AssociatorQuadNested

/-!
# Associator Pentagon First Coefficients

Original enriched Day objects, full Hom maps and chosen coend presentations.
-/

@[expose] public section

set_option autoImplicit false
noncomputable section
universe uV vV uI vI
open CategoryTheory CategoryTheory.Limits MonoidalCategory Opposite
open scoped MonoidalClosed
namespace CategoryTheory.EnrichedDayKernel.AssociatorQuadFirstRoute
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
variable (F G H J : EnrichedFunctor V I V) (m : I)

/-- The original triple associator formula remains exact after arbitrary genuine coefficient arrows.
-/
theorem tripleGenerator_coefficients (F G H : EnrichedFunctor V I V) (X : (I × I) × I)
    {A B C : V} (a : A ⟶ F.obj X.1.1) (b : B ⟶ G.obj X.1.2) (c : C ⟶ H.obj X.2) :
    (𝟙 (((X.1.1 ⊗ X.1.2) ⊗ X.2) ⟶[V] m) ⊗ₘ ((a ⊗ₘ b) ⊗ₘ c)) ≫
      AssociatorFlat.leftGenerator d F G H m X ≫ AssociatorFlattening.flatToNested d F G H m ≫
        (AssociatorConstruction.componentIso d F G H m).hom =
    (eHomWhiskerRight V (α_ X.1.1 X.1.2 X.2).inv m ⊗ₘ (α_ A B C).hom) ≫
      (𝟙 ((X.1.1 ⊗ (X.1.2 ⊗ X.2)) ⟶[V] m) ⊗ₘ (a ⊗ₘ (b ⊗ₘ c))) ≫
        AssociatorFlat.rightGenerator d F G H m X ≫ AssociatorRightFlattening.flatToNested d F G H m
          := by
  let W : V := ((X.1.1 ⊗ X.1.2) ⊗ X.2) ⟶[V] m
  let W' : V := (X.1.1 ⊗ (X.1.2 ⊗ X.2)) ⟶[V] m
  let P := AssociatorFlat.leftPoint d F G H m
  let Q := AssociatorFlat.rightPoint d F G H m
  let N := EnrichedDayKernel.obj d.tensorEnrichedFunctor (Output.functor d.tensorEnrichedFunctor F
    G) H m
  let N' := EnrichedDayKernel.obj d.tensorEnrichedFunctor F (Output.functor d.tensorEnrichedFunctor
    G H) m
  let l : P ⟶ N := AssociatorFlattening.flatToNested d F G H m
  let r : Q ⟶ N' := AssociatorRightFlattening.flatToNested d F G H m
  let e : N ⟶ N' := (AssociatorConstruction.componentIso d F G H m).hom
  let gl : W ⊗ ((F.obj X.1.1 ⊗ G.obj X.1.2) ⊗ H.obj X.2) ⟶ P := AssociatorFlat.leftGenerator d F G H
    m X
  let gr : W' ⊗ (F.obj X.1.1 ⊗ (G.obj X.1.2 ⊗ H.obj X.2)) ⟶ Q := AssociatorFlat.rightGenerator d F G
    H m X
  let z : W ⊗ ((A ⊗ B) ⊗ C) ⟶ W ⊗ ((F.obj X.1.1 ⊗ G.obj X.1.2) ⊗ H.obj X.2) := 𝟙 W ⊗ₘ ((a ⊗ₘ b) ⊗ₘ
    c)
  let z' : W' ⊗ (A ⊗ (B ⊗ C)) ⟶ W' ⊗ (F.obj X.1.1 ⊗ (G.obj X.1.2 ⊗ H.obj X.2)) := 𝟙 W' ⊗ₘ (a ⊗ₘ (b
    ⊗ₘ c))
  let w : W ⟶ W' := eHomWhiskerRight V (α_ X.1.1 X.1.2 X.2).inv m
  let t : (A ⊗ B) ⊗ C ⟶ A ⊗ (B ⊗ C) := (α_ A B C).hom
  let t' : (F.obj X.1.1 ⊗ G.obj X.1.2) ⊗ H.obj X.2 ⟶ F.obj X.1.1 ⊗ (G.obj X.1.2 ⊗ H.obj X.2) :=
    (α_ (F.obj X.1.1) (G.obj X.1.2) (H.obj X.2)).hom
  have h : gl ≫ l ≫ e = (w ⊗ₘ t') ≫ gr ≫ r := AssociatorConstruction.tripleGenerator_hom d F G H m X
  have hs : z ≫ (w ⊗ₘ t') = (w ⊗ₘ t) ≫ z' := by
    simp only [z, z', tensorHom_comp_tensorHom, Category.id_comp, Category.comp_id]
    exact congrArg (fun q => w ⊗ₘ q) (associator_naturality a b c)
  have h₀ := congrArg (fun q => z ≫ q) h
  have h₁ := congrArg (fun q => q ≫ gr ≫ r) hs
  simp only [Category.assoc] at h₀ h₁
  change z ≫ gl ≫ l ≫ e = (w ⊗ₘ t) ≫ z' ≫ gr ≫ r
  exact h₀.trans h₁

end CategoryTheory.EnrichedDayKernel.AssociatorQuadFirstRoute
