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
# Associator Pentagon A B

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

/-- The first actual Day associator carries the original A generator to the original B
  weight/coefficient word. -/
@[reassoc]
theorem genA_associator (X : ((I × I) × I) × I) :
    genA d F G H J m X ≫ (AssociatorConstruction.componentIso d (day d F G) H J m).hom =
      ((AssociatorQuadFlat.weightIsoAB d m X).hom ⊗ₘ (AssociatorQuadCoefficient.edgeAB F G H J
        X).hom) ≫
        genB d F G H J m X := by
  let a : I := X.1.1.1
  let b : I := X.1.1.2
  let c : I := X.1.2
  let e : I := X.2
  let A := F.obj a ⊗ G.obj b
  let B := H.obj c
  let C := J.obj e
  let FG := day d F G
  let A' := FG.obj (a ⊗ b)
  let U := (day d FG H).obj ((a ⊗ b) ⊗ c)
  let Y := (day d H J).obj (c ⊗ e)
  let W : V := (((a ⊗ b) ⊗ c) ⊗ e) ⟶[V] m
  let W' : V := ((a ⊗ b) ⊗ (c ⊗ e)) ⟶[V] m
  let u : A ⟶ A' := AssociatorUnit.unitGenerator d.tensorEnrichedFunctor F G (a, b)
  let v : A' ⊗ B ⟶ U := AssociatorUnit.unitGenerator d.tensorEnrichedFunctor FG H (a ⊗ b, c)
  let w : B ⊗ C ⟶ Y := AssociatorUnit.unitGenerator d.tensorEnrichedFunctor H J (c, e)
  let PL := AssociatorFlat.leftPoint d FG H J m
  let PR := AssociatorFlat.rightPoint d FG H J m
  let NA := valueA d F G H J m
  let NB := valueB d F G H J m
  let gl : W ⊗ ((A' ⊗ B) ⊗ C) ⟶ PL := AssociatorFlat.leftGenerator d FG H J m ((a ⊗ b, c), e)
  let gr : W' ⊗ (A' ⊗ (B ⊗ C)) ⟶ PR := AssociatorFlat.rightGenerator d FG H J m ((a ⊗ b, c), e)
  let l : PL ⟶ NA := AssociatorFlattening.flatToNested d FG H J m
  let r : PR ⟶ NB := AssociatorRightFlattening.flatToNested d FG H J m
  let f : NA ⟶ NB := (AssociatorConstruction.componentIso d FG H J m).hom
  let ga : W ⊗ (U ⊗ C) ⟶ NA := EnrichedDayKernel.gen d.tensorEnrichedFunctor (day d FG H) J m ((a ⊗
    b) ⊗ c, e)
  let gb : W' ⊗ (A' ⊗ Y) ⟶ NB := EnrichedDayKernel.gen d.tensorEnrichedFunctor FG (day d H J) m (a ⊗
    b, c ⊗ e)
  let z : W ⊗ ((A ⊗ B) ⊗ C) ⟶ W ⊗ ((A' ⊗ B) ⊗ C) := 𝟙 W ⊗ₘ ((u ⊗ₘ 𝟙 B) ⊗ₘ 𝟙 C)
  let q : W ⟶ W' := eHomWhiskerRight V (α_ (a ⊗ b) c e).inv m
  let t : (A ⊗ B) ⊗ C ⟶ A ⊗ (B ⊗ C) := (α_ A B C).hom
  let z' : W' ⊗ (A ⊗ (B ⊗ C)) ⟶ W' ⊗ (A' ⊗ (B ⊗ C)) := 𝟙 W' ⊗ₘ (u ⊗ₘ 𝟙 (B ⊗ C))
  let z'' : W' ⊗ (A' ⊗ (B ⊗ C)) ⟶ W' ⊗ (A' ⊗ Y) := 𝟙 W' ⊗ₘ (𝟙 A' ⊗ₘ w)
  let n : W' ⊗ (A ⊗ (B ⊗ C)) ⟶ NB := genB d F G H J m X
  have hgl : gl ≫ l = (𝟙 W ⊗ₘ (v ⊗ₘ 𝟙 C)) ≫ ga := AssociatorFlattening.leftGenerator_flatToNested d
    FG H J m ((a ⊗ b, c), e)
  have hgr : gr ≫ r = z'' ≫ gb := AssociatorRightFlattening.rightGenerator_flatToNested d FG H J m
    ((a ⊗ b, c), e)
  have hsource : genA d F G H J m X = z ≫ gl ≫ l := by
    rw [hgl]
    change (𝟙 W ⊗ₘ (((u ⊗ₘ 𝟙 B) ≫ v) ⊗ₘ 𝟙 C)) ≫ ga =
      (𝟙 W ⊗ₘ ((u ⊗ₘ 𝟙 B) ⊗ₘ 𝟙 C)) ≫ (𝟙 W ⊗ₘ (v ⊗ₘ 𝟙 C)) ≫ ga
    simp only [tensorHom_comp_tensorHom_assoc, tensorHom_comp_tensorHom, Category.comp_id]
  have h := tripleGenerator_coefficients d m FG H J ((a ⊗ b, c), e) u (𝟙 B) (𝟙 C)
  simp only [id_tensorHom_id] at h
  change z ≫ gl ≫ l ≫ f = (q ⊗ₘ t) ≫ z' ≫ gr ≫ r at h
  have hh : z' ≫ z'' = 𝟙 W' ⊗ₘ (u ⊗ₘ w) := by
    simp only [z', z'', tensorHom_comp_tensorHom, Category.id_comp, Category.comp_id]
  have hb : (𝟙 W' ⊗ₘ (u ⊗ₘ w)) ≫ gb = n := rfl
  have htarget : z ≫ gl ≫ l ≫ f = (q ⊗ₘ t) ≫ n := by
    rw [h, hgr, ← Category.assoc z', hh, hb]
  rw [hsource]
  change (z ≫ gl ≫ l) ≫ f =
    ((AssociatorQuadFlat.weightIsoAB d m X).hom ⊗ₘ (AssociatorQuadCoefficient.edgeAB F G H J X).hom)
      ≫ n
  simp only [AssociatorQuadFlat.weightIsoAB, AssociatorQuadMaps.weightIso,
    Iso.eHomCongr, Iso.refl_hom, eHomWhiskerLeft_id, Category.comp_id,
    AssociatorQuadCoefficient.edgeAB]
  change (z ≫ gl ≫ l) ≫ f = (q ⊗ₘ t) ≫ n
  simpa only [Category.assoc] using htarget

end CategoryTheory.EnrichedDayKernel.AssociatorQuadFirstRoute
