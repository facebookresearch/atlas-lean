/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua
module

public import
  MathlibExt.CategoryTheory.Enriched.Monoidal.DayConvolution.AssociatorPentagonFirstCoefficients

/-!
# Associator Pentagon B C

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

/-- The second actual Day associator carries the original B generator to the original C word. -/
@[reassoc]
theorem genB_associator (X : ((I × I) × I) × I) :
    genB d F G H J m X ≫ (AssociatorConstruction.componentIso d F G (day d H J) m).hom =
      ((AssociatorQuadFlat.weightIsoBC d m X).hom ⊗ₘ (AssociatorQuadCoefficient.edgeBC F G H J
        X).hom) ≫
        genC d F G H J m X := by
  let a : I := X.1.1.1
  let b : I := X.1.1.2
  let c : I := X.1.2
  let e : I := X.2
  let A := F.obj a
  let B := G.obj b
  let C := H.obj c ⊗ J.obj e
  let HJ := day d H J
  let C' := HJ.obj (c ⊗ e)
  let U := (day d F G).obj (a ⊗ b)
  let Y := (day d G HJ).obj (b ⊗ (c ⊗ e))
  let W : V := ((a ⊗ b) ⊗ (c ⊗ e)) ⟶[V] m
  let W' : V := (a ⊗ (b ⊗ (c ⊗ e))) ⟶[V] m
  let u : A ⊗ B ⟶ U := AssociatorUnit.unitGenerator d.tensorEnrichedFunctor F G (a, b)
  let w : C ⟶ C' := AssociatorUnit.unitGenerator d.tensorEnrichedFunctor H J (c, e)
  let v : B ⊗ C' ⟶ Y := AssociatorUnit.unitGenerator d.tensorEnrichedFunctor G HJ (b, c ⊗ e)
  let PL := AssociatorFlat.leftPoint d F G HJ m
  let PR := AssociatorFlat.rightPoint d F G HJ m
  let NB := valueB d F G H J m
  let NC := valueC d F G H J m
  let gl : W ⊗ ((A ⊗ B) ⊗ C') ⟶ PL := AssociatorFlat.leftGenerator d F G HJ m ((a, b), c ⊗ e)
  let gr : W' ⊗ (A ⊗ (B ⊗ C')) ⟶ PR := AssociatorFlat.rightGenerator d F G HJ m ((a, b), c ⊗ e)
  let l : PL ⟶ NB := AssociatorFlattening.flatToNested d F G HJ m
  let r : PR ⟶ NC := AssociatorRightFlattening.flatToNested d F G HJ m
  let f : NB ⟶ NC := (AssociatorConstruction.componentIso d F G HJ m).hom
  let gb : W ⊗ (U ⊗ C') ⟶ NB := EnrichedDayKernel.gen d.tensorEnrichedFunctor (day d F G) HJ m (a ⊗
    b, c ⊗ e)
  let gc : W' ⊗ (A ⊗ Y) ⟶ NC := EnrichedDayKernel.gen d.tensorEnrichedFunctor F (day d G HJ) m (a, b
    ⊗ (c ⊗ e))
  let z : W ⊗ ((A ⊗ B) ⊗ C) ⟶ W ⊗ ((A ⊗ B) ⊗ C') := 𝟙 W ⊗ₘ (𝟙 (A ⊗ B) ⊗ₘ w)
  let q : W ⟶ W' := eHomWhiskerRight V (α_ a b (c ⊗ e)).inv m
  let t : (A ⊗ B) ⊗ C ⟶ A ⊗ (B ⊗ C) := (α_ A B C).hom
  let z' : W' ⊗ (A ⊗ (B ⊗ C)) ⟶ W' ⊗ (A ⊗ (B ⊗ C')) := 𝟙 W' ⊗ₘ (𝟙 A ⊗ₘ (𝟙 B ⊗ₘ w))
  let z'' : W' ⊗ (A ⊗ (B ⊗ C')) ⟶ W' ⊗ (A ⊗ Y) := 𝟙 W' ⊗ₘ (𝟙 A ⊗ₘ v)
  let n : W' ⊗ (A ⊗ (B ⊗ C)) ⟶ NC := genC d F G H J m X
  have hgl : gl ≫ l = (𝟙 W ⊗ₘ (u ⊗ₘ 𝟙 C')) ≫ gb := AssociatorFlattening.leftGenerator_flatToNested d
    F G HJ m ((a, b), c ⊗ e)
  have hgr : gr ≫ r = z'' ≫ gc := AssociatorRightFlattening.rightGenerator_flatToNested d F G HJ m
    ((a, b), c ⊗ e)
  have hsource : genB d F G H J m X = z ≫ gl ≫ l := by
    rw [hgl]
    change (𝟙 W ⊗ₘ (u ⊗ₘ w)) ≫ gb =
      (𝟙 W ⊗ₘ (𝟙 (A ⊗ B) ⊗ₘ w)) ≫ (𝟙 W ⊗ₘ (u ⊗ₘ 𝟙 C')) ≫ gb
    simp only [tensorHom_comp_tensorHom_assoc, tensorHom_comp_tensorHom, Category.id_comp,
      Category.comp_id]
  have h := tripleGenerator_coefficients d m F G HJ ((a, b), c ⊗ e) (𝟙 A) (𝟙 B) w
  simp only [id_tensorHom_id] at h
  change z ≫ gl ≫ l ≫ f = (q ⊗ₘ t) ≫ z' ≫ gr ≫ r at h
  have hh : z' ≫ z'' = 𝟙 W' ⊗ₘ (𝟙 A ⊗ₘ ((𝟙 B ⊗ₘ w) ≫ v)) := by
    simp only [z', z'', tensorHom_comp_tensorHom, Category.id_comp]
  have hgc : (𝟙 W' ⊗ₘ (𝟙 A ⊗ₘ ((𝟙 B ⊗ₘ w) ≫ v))) ≫ gc = n := rfl
  have htarget : z ≫ gl ≫ l ≫ f = (q ⊗ₘ t) ≫ n := by
    rw [h, hgr, ← Category.assoc z', hh, hgc]
  rw [hsource]
  change (z ≫ gl ≫ l) ≫ f =
    ((AssociatorQuadFlat.weightIsoBC d m X).hom ⊗ₘ (AssociatorQuadCoefficient.edgeBC F G H J X).hom)
      ≫ n
  simp only [AssociatorQuadFlat.weightIsoBC, AssociatorQuadMaps.weightIso,
    Iso.eHomCongr, Iso.refl_hom, eHomWhiskerLeft_id, Category.comp_id,
    AssociatorQuadCoefficient.edgeBC]
  change (z ≫ gl ≫ l) ≫ f = (q ⊗ₘ t) ≫ n
  simpa only [Category.assoc] using htarget

end CategoryTheory.EnrichedDayKernel.AssociatorQuadFirstRoute
