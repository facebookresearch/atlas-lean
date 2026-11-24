/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua
module

public import MathlibExt.CategoryTheory.Enriched.Monoidal.DayConvolution.AssociatorQuadNested
public import
  MathlibExt.CategoryTheory.Enriched.Monoidal.DayConvolution.AssociatorPentagonFirstCoefficients
public import MathlibExt.CategoryTheory.Enriched.Monoidal.DayConvolution.AssociatorComparisonUnit
public import MathlibExt.CategoryTheory.Enriched.Monoidal.DayConvolution.Triangle

/-!
# Associator Pentagon Second

Original enriched Day objects, full Hom maps and chosen coend presentations.
-/

@[expose] public section

set_option autoImplicit false
noncomputable section
universe uV vV uI vI
open CategoryTheory CategoryTheory.Limits MonoidalCategory Opposite
open scoped MonoidalClosed

namespace CategoryTheory.EnrichedDayKernel.AssociatorQuadSecondRoute
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

/-- The actual middle associator sends the original D generator to the original E word. -/
@[reassoc]
theorem genD_associator (X : ((I × I) × I) × I) :
    genD d F G H J m X ≫
        (AssociatorConstruction.componentIso d F (day d G H) J m).hom =
      ((AssociatorQuadFlat.weightIsoDE d m X).hom ⊗ₘ
        (AssociatorQuadCoefficient.edgeDE F G H J X).hom) ≫ genE d F G H J m X := by
  let a : I := X.1.1.1
  let b : I := X.1.1.2
  let c : I := X.1.2
  let e : I := X.2
  let A := F.obj a
  let B := G.obj b ⊗ H.obj c
  let C := J.obj e
  let GH := day d G H
  let B' := GH.obj (b ⊗ c)
  let U := (day d F GH).obj (a ⊗ (b ⊗ c))
  let Y := (day d GH J).obj ((b ⊗ c) ⊗ e)
  let W : V := ((a ⊗ (b ⊗ c)) ⊗ e) ⟶[V] m
  let W' : V := (a ⊗ ((b ⊗ c) ⊗ e)) ⟶[V] m
  let u : B ⟶ B' := AssociatorUnit.unitGenerator d.tensorEnrichedFunctor G H (b, c)
  let v : A ⊗ B' ⟶ U := AssociatorUnit.unitGenerator d.tensorEnrichedFunctor F GH (a, b ⊗ c)
  let w : B' ⊗ C ⟶ Y := AssociatorUnit.unitGenerator d.tensorEnrichedFunctor GH J (b ⊗ c, e)
  let PL := AssociatorFlat.leftPoint d F GH J m
  let PR := AssociatorFlat.rightPoint d F GH J m
  let ND := valueD d F G H J m
  let NE := valueE d F G H J m
  let gl : W ⊗ ((A ⊗ B') ⊗ C) ⟶ PL := AssociatorFlat.leftGenerator d F GH J m ((a, b ⊗ c), e)
  let gr : W' ⊗ (A ⊗ (B' ⊗ C)) ⟶ PR := AssociatorFlat.rightGenerator d F GH J m ((a, b ⊗ c), e)
  let l : PL ⟶ ND := AssociatorFlattening.flatToNested d F GH J m
  let r : PR ⟶ NE := AssociatorRightFlattening.flatToNested d F GH J m
  let f : ND ⟶ NE := (AssociatorConstruction.componentIso d F GH J m).hom
  let gd : W ⊗ (U ⊗ C) ⟶ ND :=
    EnrichedDayKernel.gen d.tensorEnrichedFunctor (day d F GH) J m (a ⊗ (b ⊗ c), e)
  let ge : W' ⊗ (A ⊗ Y) ⟶ NE :=
    EnrichedDayKernel.gen d.tensorEnrichedFunctor F (day d GH J) m (a, (b ⊗ c) ⊗ e)
  let z : W ⊗ ((A ⊗ B) ⊗ C) ⟶ W ⊗ ((A ⊗ B') ⊗ C) :=
    𝟙 W ⊗ₘ ((𝟙 A ⊗ₘ u) ⊗ₘ 𝟙 C)
  let q : W ⟶ W' := eHomWhiskerRight V (α_ a (b ⊗ c) e).inv m
  let t : (A ⊗ B) ⊗ C ⟶ A ⊗ (B ⊗ C) := (α_ A B C).hom
  let z' : W' ⊗ (A ⊗ (B ⊗ C)) ⟶ W' ⊗ (A ⊗ (B' ⊗ C)) :=
    𝟙 W' ⊗ₘ (𝟙 A ⊗ₘ (u ⊗ₘ 𝟙 C))
  let z'' : W' ⊗ (A ⊗ (B' ⊗ C)) ⟶ W' ⊗ (A ⊗ Y) := 𝟙 W' ⊗ₘ (𝟙 A ⊗ₘ w)
  let n : W' ⊗ (A ⊗ (B ⊗ C)) ⟶ NE := genE d F G H J m X
  have hgl : gl ≫ l = (𝟙 W ⊗ₘ (v ⊗ₘ 𝟙 C)) ≫ gd :=
    AssociatorFlattening.leftGenerator_flatToNested d F GH J m ((a, b ⊗ c), e)
  have hgr : gr ≫ r = z'' ≫ ge :=
    AssociatorRightFlattening.rightGenerator_flatToNested d F GH J m ((a, b ⊗ c), e)
  have hsource : genD d F G H J m X = z ≫ gl ≫ l := by
    rw [hgl]
    change (𝟙 W ⊗ₘ (((𝟙 A ⊗ₘ u) ≫ v) ⊗ₘ 𝟙 C)) ≫ gd =
      (𝟙 W ⊗ₘ ((𝟙 A ⊗ₘ u) ⊗ₘ 𝟙 C)) ≫ (𝟙 W ⊗ₘ (v ⊗ₘ 𝟙 C)) ≫ gd
    simp only [tensorHom_comp_tensorHom_assoc, tensorHom_comp_tensorHom, Category.comp_id]
  have h := AssociatorQuadFirstRoute.tripleGenerator_coefficients d m
    F GH J ((a, b ⊗ c), e) (𝟙 A) u (𝟙 C)
  change z ≫ gl ≫ l ≫ f = (q ⊗ₘ t) ≫ z' ≫ gr ≫ r at h
  have hh : z' ≫ z'' = 𝟙 W' ⊗ₘ (𝟙 A ⊗ₘ ((u ⊗ₘ 𝟙 C) ≫ w)) := by
    simp only [z', z'', tensorHom_comp_tensorHom, Category.comp_id]
  have hb : (𝟙 W' ⊗ₘ (𝟙 A ⊗ₘ ((u ⊗ₘ 𝟙 C) ≫ w))) ≫ ge = n := rfl
  have htarget : z ≫ gl ≫ l ≫ f = (q ⊗ₘ t) ≫ n := by
    rw [h, hgr, ← Category.assoc z', hh, hb]
  rw [hsource]
  change (z ≫ gl ≫ l) ≫ f =
    ((AssociatorQuadFlat.weightIsoDE d m X).hom ⊗ₘ (AssociatorQuadCoefficient.edgeDE F G H J X).hom)
      ≫ n
  simp only [AssociatorQuadFlat.weightIsoDE, AssociatorQuadMaps.weightIso,
    Iso.eHomCongr, Iso.refl_hom, eHomWhiskerLeft_id, Category.comp_id,
    AssociatorQuadCoefficient.edgeDE]
  change (z ≫ gl ≫ l) ≫ f = (q ⊗ₘ t) ≫ n
  simpa only [Category.assoc] using htarget


/-- The original primitive left triple unit is carried to the exact original right index point. -/
@[reassoc]
theorem primitive_associator_point (F G H : EnrichedFunctor V I V) (X : (I × I) × I) :
    AssociatorQuadLeft.tripleUnitGenerator d F G H X ≫
        (AssociatorConstruction.componentIso d F G H ((AssociatorIndex.leftIndex d).obj X)).hom =
      (α_ (F.obj X.1.1) (G.obj X.1.2) (H.obj X.2)).hom ≫
        AssociatorTriangle.pointInsert (eHomEquiv V (α_ X.1.1 X.1.2 X.2).inv)
          (F.obj X.1.1 ⊗ (G.obj X.1.2 ⊗ H.obj X.2)) ≫
        AssociatorFlat.rightGenerator d F G H ((AssociatorIndex.leftIndex d).obj X) X ≫
          AssociatorRightFlattening.flatToNested d F G H ((AssociatorIndex.leftIndex d).obj X) := by
  let k := (AssociatorIndex.leftIndex d).obj X
  let L := (F.obj X.1.1 ⊗ G.obj X.1.2) ⊗ H.obj X.2
  let R := F.obj X.1.1 ⊗ (G.obj X.1.2 ⊗ H.obj X.2)
  let i : L ⟶ AssociatorFlat.leftObjects d F G H k X := AssociatorUnit.identityInsert k L
  let gl := AssociatorFlat.leftGenerator d F G H k X
  let gr := AssociatorFlat.rightGenerator d F G H k X
  let l := AssociatorFlattening.flatToNested d F G H k
  let r := AssociatorRightFlattening.flatToNested d F G H k
  let a := (AssociatorConstruction.componentIso d F G H k).hom
  let f : X.1.1 ⊗ (X.1.2 ⊗ X.2) ⟶ k := (α_ X.1.1 X.1.2 X.2).inv
  let w := eHomWhiskerRight V f k
  let c : L ⟶ R := (α_ (F.obj X.1.1) (G.obj X.1.2) (H.obj X.2)).hom
  let j : R ⟶ AssociatorFlat.rightObjects d F G H k X :=
    AssociatorTriangle.pointInsert (eHomEquiv V f) R
  have hs : AssociatorQuadLeft.tripleUnitGenerator d F G H X = (i ≫ gl) ≫ l :=
    (AssociatorComparisonUnit.day_left_unitGenerator_flatToNested d F G H X).symm
  have hg : gl ≫ l ≫ a = (w ⊗ₘ c) ≫ gr ≫ r :=
    AssociatorConstruction.tripleGenerator_hom d F G H k X
  have hp : eId V k ≫ w = eHomEquiv V f := eId_comp_eHomWhiskerRight V I f
  have hraw : AssociatorUnit.identityInsert k L ≫ (w ⊗ₘ c) =
      c ≫ AssociatorTriangle.pointInsert (eHomEquiv V f) R := by
    dsimp only [AssociatorUnit.identityInsert, AssociatorTriangle.pointInsert]
    simp only [Category.assoc]
    rw [tensorHom_comp_tensorHom, Category.id_comp, hp]
    have h := congrArg (fun z => z ≫ (eHomEquiv V f ⊗ₘ 𝟙 R)) (leftUnitor_inv_naturality c)
    simpa only [← id_tensorHom, tensorHom_comp_tensorHom, Category.id_comp, Category.comp_id,
      Category.assoc] using h.symm
  have hi : i ≫ (w ⊗ₘ c) = c ≫ j := hraw
  change AssociatorQuadLeft.tripleUnitGenerator d F G H X ≫ a = c ≫ j ≫ gr ≫ r
  calc
    _ = ((i ≫ gl) ≫ l) ≫ a := congrArg (fun z => z ≫ a) hs
    _ = i ≫ (gl ≫ l ≫ a) := by simp only [Category.assoc]
    _ = i ≫ ((w ⊗ₘ c) ≫ gr ≫ r) := congrArg (fun z => i ≫ z) hg
    _ = (i ≫ (w ⊗ₘ c)) ≫ gr ≫ r := by simp only [Category.assoc]
    _ = (c ≫ j) ≫ gr ≫ r := congrArg (fun z => z ≫ gr ≫ r) hi
    _ = _ := by simp only [Category.assoc]


/-- The primitive associator uses the exact original binary generator at its genuine inverse index
  point. -/
@[reassoc]
theorem primitive_associator_generator (F G H : EnrichedFunctor V I V) (X : (I × I) × I) :
    AssociatorQuadLeft.tripleUnitGenerator d F G H X ≫
        (AssociatorConstruction.componentIso d F G H ((AssociatorIndex.leftIndex d).obj X)).hom =
      (α_ (F.obj X.1.1) (G.obj X.1.2) (H.obj X.2)).hom ≫
        (𝟙 (F.obj X.1.1) ⊗ₘ AssociatorUnit.unitGenerator d.tensorEnrichedFunctor G H (X.1.2, X.2)) ≫
        AssociatorTriangle.pointInsert (eHomEquiv V (α_ X.1.1 X.1.2 X.2).inv)
          (F.obj X.1.1 ⊗ (day d G H).obj (X.1.2 ⊗ X.2)) ≫
        EnrichedDayKernel.gen d.tensorEnrichedFunctor F (day d G H)
          ((AssociatorIndex.leftIndex d).obj X) (X.1.1, X.1.2 ⊗ X.2) := by
  let k := (AssociatorIndex.leftIndex d).obj X
  let A := F.obj X.1.1 ⊗ (G.obj X.1.2 ⊗ H.obj X.2)
  let A' := F.obj X.1.1 ⊗ (day d G H).obj (X.1.2 ⊗ X.2)
  let c := (α_ (F.obj X.1.1) (G.obj X.1.2) (H.obj X.2)).hom
  let f := (α_ X.1.1 X.1.2 X.2).inv
  let t : A ⟶ A' := 𝟙 (F.obj X.1.1) ⊗ₘ AssociatorUnit.unitGenerator d.tensorEnrichedFunctor G H
    (X.1.2, X.2)
  let gr := AssociatorFlat.rightGenerator d F G H k X
  let r := AssociatorRightFlattening.flatToNested d F G H k
  let g := EnrichedDayKernel.gen d.tensorEnrichedFunctor F (day d G H) k (X.1.1, X.1.2 ⊗ X.2)
  have hp := primitive_associator_point d F G H X
  have hr : gr ≫ r = (𝟙 ((X.1.1 ⊗ (X.1.2 ⊗ X.2)) ⟶[V] k) ⊗ₘ t) ≫ g :=
    AssociatorRightFlattening.rightGenerator_flatToNested d F G H k X
  have hn : AssociatorTriangle.pointInsert (eHomEquiv V f) A ≫
      (𝟙 ((X.1.1 ⊗ (X.1.2 ⊗ X.2)) ⟶[V] k) ⊗ₘ t) =
      t ≫ AssociatorTriangle.pointInsert (eHomEquiv V f) A' := by
    have h := congrArg (fun z => AssociatorTriangle.pointInsert (eHomEquiv V f) A ≫ z)
      (id_tensorHom ((X.1.1 ⊗ (X.1.2 ⊗ X.2)) ⟶[V] k) t)
    exact h.trans (AssociatorTriangle.pointInsert_natural (eHomEquiv V f) t)
  let i : A ⟶ AssociatorFlat.rightObjects d F G H k X := AssociatorTriangle.pointInsert (eHomEquiv V
    f) A
  let j : A' ⟶ EnrichedDayKernel.objects d.tensorEnrichedFunctor F (day d G H) k
      (X.1.1, X.1.2 ⊗ X.2) := AssociatorTriangle.pointInsert (eHomEquiv V f) A'
  let w : AssociatorFlat.rightObjects d F G H k X ⟶
      EnrichedDayKernel.objects d.tensorEnrichedFunctor F (day d G H) k (X.1.1, X.1.2 ⊗ X.2) :=
    𝟙 ((X.1.1 ⊗ (X.1.2 ⊗ X.2)) ⟶[V] k) ⊗ₘ t
  have hi : i ≫ w = t ≫ j := hn
  have hg : gr ≫ r = w ≫ g := hr
  have hraw : (i ≫ gr) ≫ r = t ≫ (j ≫ g) := by
    calc
      _ = i ≫ (gr ≫ r) := Category.assoc i gr r
      _ = i ≫ (w ≫ g) := congrArg (fun z => i ≫ z) hg
      _ = (i ≫ w) ≫ g := (Category.assoc i w g).symm
      _ = (t ≫ j) ≫ g := congrArg (fun z => z ≫ g) hi
      _ = _ := Category.assoc t j g
  have hp' : AssociatorQuadLeft.tripleUnitGenerator d F G H X ≫
      (AssociatorConstruction.componentIso d F G H k).hom = c ≫ ((i ≫ gr) ≫ r) :=
    hp.trans (congrArg (fun z => c ≫ z) (Category.assoc i gr r).symm)
  exact hp'.trans (congrArg (fun z => c ≫ z) hraw)


/-- Tensoring the actual first-three associator retains the original AD weight and coefficient
  factors. -/
@[reassoc]
theorem genA_tensor_associator (X : ((I × I) × I) × I) :
    genA d F G H J m X ≫ Input.mapAt d.tensorEnrichedFunctor
        (AssociatorConstruction.functorIso d F G H).hom (GradedNatTrans.unitId J) m =
      ((AssociatorQuadFlat.weightIsoAD d m X).hom ⊗ₘ
        (AssociatorQuadCoefficient.edgeAD F G H J X).hom) ≫ genD d F G H J m X := by
  let a : I := X.1.1.1
  let b : I := X.1.1.2
  let c : I := X.1.2
  let e : I := X.2
  let xL := (a ⊗ b) ⊗ c
  let xR := a ⊗ (b ⊗ c)
  let p : I × I := (xL, e)
  let z : I × I := (a, b ⊗ c)
  let L := (F.obj a ⊗ G.obj b) ⊗ H.obj c
  let R := F.obj a ⊗ (G.obj b ⊗ H.obj c)
  let B := J.obj e
  let GH := day d G H
  let LF := day d (day d F G) H
  let RF := day d F GH
  let A := F.obj a ⊗ GH.obj (b ⊗ c)
  let W : V := (xL ⊗ e) ⟶[V] m
  let W' : V := (xR ⊗ e) ⟶[V] m
  let Hm : V := xR ⟶[V] xL
  let f : xR ⟶ xL := (α_ a b c).inv
  let u : L ⟶ LF.obj xL := AssociatorQuadLeft.tripleUnitGenerator d F G H X.1
  let cv : L ⟶ R := (α_ (F.obj a) (G.obj b) (H.obj c)).hom
  let t : R ⟶ A := 𝟙 (F.obj a) ⊗ₘ AssociatorUnit.unitGenerator d.tensorEnrichedFunctor G H (b, c)
  let pt : A ⟶ Hm ⊗ A := AssociatorTriangle.pointInsert (eHomEquiv V f) A
  let gi : Hm ⊗ A ⟶ RF.obj xL := EnrichedDayKernel.gen d.tensorEnrichedFunctor F GH xL z
  let v : A ⟶ RF.obj xR := AssociatorUnit.unitGenerator d.tensorEnrichedFunctor F GH z
  let gs : W ⊗ (LF.obj xL ⊗ B) ⟶ valueA d F G H J m :=
    EnrichedDayKernel.gen d.tensorEnrichedFunctor LF J m p
  let gt : W ⊗ (RF.obj xL ⊗ B) ⟶ valueD d F G H J m :=
    EnrichedDayKernel.gen d.tensorEnrichedFunctor RF J m p
  let gd : W' ⊗ (RF.obj xR ⊗ B) ⟶ valueD d F G H J m :=
    EnrichedDayKernel.gen d.tensorEnrichedFunctor RF J m (xR, e)
  let a3 : LF.obj xL ⟶ RF.obj xL :=
    EnrichedFunctorCat.component (AssociatorConstruction.functorIso d F G H).hom xL
  let fm : valueA d F G H J m ⟶ valueD d F G H J m :=
    Input.mapAt d.tensorEnrichedFunctor (AssociatorConstruction.functorIso d F G H).hom
      (GradedNatTrans.unitId J) m
  let pre : W ⊗ (A ⊗ B) ⟶ W ⊗ ((Hm ⊗ A) ⊗ B) := W ◁ (pt ▷ B)
  let ng : W ⊗ ((Hm ⊗ A) ⊗ B) ⟶ valueD d F G H J m :=
    AssociatorFaces.Left.nestedGenerator d.tensorEnrichedFunctor d.tensorEnrichedFunctor F GH J m p
      z
  let ct : W ⊗ ((Hm ⊗ A) ⊗ B) ⟶ W' ⊗ (A ⊗ B) :=
    AssociatorFlattening.contractWord d F GH J m p z
  let gl : W' ⊗ (A ⊗ B) ⟶ AssociatorFlat.leftPoint d F GH J m :=
    AssociatorFlat.leftGenerator d F GH J m (z, e)
  let l := AssociatorFlattening.flatToNested d F GH J m
  let w : W ⟶ W' := eHomWhiskerRight V (f ▷ e) m
  let q0 : W ⊗ (L ⊗ B) ⟶ W ⊗ (R ⊗ B) := 𝟙 W ⊗ₘ (cv ⊗ₘ 𝟙 B)
  let q1 : W ⊗ (R ⊗ B) ⟶ W ⊗ (A ⊗ B) := 𝟙 W ⊗ₘ (t ⊗ₘ 𝟙 B)
  have hu : u ≫ a3 = cv ≫ t ≫ pt ≫ gi := by
    have ha : a3 = (AssociatorConstruction.componentIso d F G H xL).hom :=
      AssociatorConstruction.functorIso_hom_component d F G H xL
    exact (congrArg (fun y => u ≫ y) ha).trans (primitive_associator_generator d F G H X.1)
  have hinput : gs ≫ fm = (𝟙 W ⊗ₘ (a3 ⊗ₘ 𝟙 B)) ≫ gt := by
    have h := Input.gen_mapAt d.tensorEnrichedFunctor
      (AssociatorConstruction.functorIso d F G H).hom (GradedNatTrans.unitId J) m p
    simp only [GradedNatTrans.unitId_component] at h
    exact h
  have hng : ng = W ◁ (gi ▷ B) ≫ gt := rfl
  have hsource : genA d F G H J m X ≫ fm = q0 ≫ q1 ≫ pre ≫ ng := by
    change ((𝟙 W ⊗ₘ (u ⊗ₘ 𝟙 B)) ≫ gs) ≫ fm = q0 ≫ q1 ≫ pre ≫ ng
    rw [Category.assoc, hinput]
    have hcombine : (𝟙 W ⊗ₘ (u ⊗ₘ 𝟙 B)) ≫ (𝟙 W ⊗ₘ (a3 ⊗ₘ 𝟙 B)) =
        𝟙 W ⊗ₘ ((u ≫ a3) ⊗ₘ 𝟙 B) := by
      simp only [tensorHom_comp_tensorHom, Category.id_comp]
    rw [← Category.assoc, hcombine, hu]
    rw [hng]
    simp only [q0, q1, pre, ← id_tensorHom, ← tensorHom_id,
      tensorHom_comp_tensorHom_assoc, tensorHom_comp_tensorHom,
      Category.comp_id]
  have hct : pre ≫ ct = w ⊗ₘ 𝟙 (A ⊗ B) :=
    AssociatorTriangle.left_contractWord_point d F GH J m p z f
  have hfactor : ct ≫ gl ≫ l = ng :=
    AssociatorFlattening.contractWord_generator_factorization d F GH J m p z
  have hgl : gl ≫ l = (𝟙 W' ⊗ₘ (v ⊗ₘ 𝟙 B)) ≫ gd :=
    AssociatorFlattening.leftGenerator_flatToNested d F GH J m (z, e)
  have hnorm : pre ≫ ng = (w ⊗ₘ (v ⊗ₘ 𝟙 B)) ≫ gd := by
    calc
      _ = pre ≫ (ct ≫ gl ≫ l) := congrArg (fun y => pre ≫ y) hfactor.symm
      _ = (pre ≫ ct) ≫ gl ≫ l := by simp only [Category.assoc]
      _ = (w ⊗ₘ 𝟙 (A ⊗ B)) ≫ gl ≫ l := congrArg (fun y => y ≫ gl ≫ l) hct
      _ = (w ⊗ₘ 𝟙 (A ⊗ B)) ≫ ((𝟙 W' ⊗ₘ (v ⊗ₘ 𝟙 B)) ≫ gd) :=
        congrArg (fun y => (w ⊗ₘ 𝟙 (A ⊗ B)) ≫ y) hgl
      _ = _ := by simp only [tensorHom_comp_tensorHom_assoc, Category.comp_id, Category.id_comp]
  let nd : W' ⊗ (R ⊗ B) ⟶ valueD d F G H J m := genD d F G H J m X
  have hraw : q0 ≫ q1 ≫ pre ≫ ng = (w ⊗ₘ (cv ⊗ₘ 𝟙 B)) ≫ nd := by
    have hn := congrArg (fun y => q0 ≫ q1 ≫ y) hnorm
    have hright : q0 ≫ q1 ≫ ((w ⊗ₘ (v ⊗ₘ 𝟙 B)) ≫ gd) =
        (w ⊗ₘ (cv ⊗ₘ 𝟙 B)) ≫ nd := by
      change q0 ≫ q1 ≫ (w ⊗ₘ (v ⊗ₘ 𝟙 B)) ≫ gd =
        (w ⊗ₘ (cv ⊗ₘ 𝟙 B)) ≫ (𝟙 W' ⊗ₘ ((t ≫ v) ⊗ₘ 𝟙 B)) ≫ gd
      simp only [q0, q1, tensorHom_comp_tensorHom_assoc, tensorHom_comp_tensorHom,
        Category.id_comp, Category.comp_id]
    exact hn.trans hright
  have hw : (AssociatorQuadFlat.weightIsoAD d m X).hom = w := by
    dsimp only [AssociatorQuadFlat.weightIsoAD, AssociatorQuadMaps.weightIso, Iso.eHomCongr,
      AssociatorQuadIndex.edgeAD, MonoidalCategory.tensorIso]
    simp only [Iso.refl_hom, Iso.refl_inv, eHomWhiskerLeft_id, Category.comp_id]
    exact congrArg (fun y => eHomWhiskerRight V y m) (tensorHom_id f e)
  have hc : (AssociatorQuadCoefficient.edgeAD F G H J X).hom = cv ⊗ₘ 𝟙 B := rfl
  have hword : (AssociatorQuadFlat.weightIsoAD d m X).hom ⊗ₘ
      (AssociatorQuadCoefficient.edgeAD F G H J X).hom = w ⊗ₘ (cv ⊗ₘ 𝟙 B) :=
    congrArg₂ (fun f g => f ⊗ₘ g) hw hc
  have ht : genA d F G H J m X ≫ fm = (w ⊗ₘ (cv ⊗ₘ 𝟙 B)) ≫ nd := hsource.trans hraw
  exact ht.trans (congrArg (fun y => y ≫ nd) hword.symm)


/-- Tensoring the actual final-three associator retains the original EC weight and coefficient
  factors. -/
@[reassoc]
theorem genE_tensor_associator (X : ((I × I) × I) × I) :
    genE d F G H J m X ≫ Input.mapAt d.tensorEnrichedFunctor
        (GradedNatTrans.unitId F) (AssociatorConstruction.functorIso d G H J).hom m =
      ((AssociatorQuadFlat.weightIsoEC d m X).hom ⊗ₘ
        (AssociatorQuadCoefficient.edgeEC F G H J X).hom) ≫ genC d F G H J m X := by
  let a : I := X.1.1.1
  let b : I := X.1.1.2
  let c : I := X.1.2
  let e : I := X.2
  let xL := (b ⊗ c) ⊗ e
  let xR := b ⊗ (c ⊗ e)
  let p : I × I := (a, xL)
  let z : I × I := (b, c ⊗ e)
  let L := (G.obj b ⊗ H.obj c) ⊗ J.obj e
  let R := G.obj b ⊗ (H.obj c ⊗ J.obj e)
  let B := F.obj a
  let HJ := day d H J
  let LF := day d (day d G H) J
  let RF := day d G HJ
  let A := G.obj b ⊗ HJ.obj (c ⊗ e)
  let W : V := (a ⊗ xL) ⟶[V] m
  let W' : V := (a ⊗ xR) ⟶[V] m
  let Hm : V := xR ⟶[V] xL
  let f : xR ⟶ xL := (α_ b c e).inv
  let u : L ⟶ LF.obj xL := AssociatorQuadLeft.tripleUnitGenerator d G H J ((b, c), e)
  let cv : L ⟶ R := (α_ (G.obj b) (H.obj c) (J.obj e)).hom
  let t : R ⟶ A := 𝟙 (G.obj b) ⊗ₘ AssociatorUnit.unitGenerator d.tensorEnrichedFunctor H J (c, e)
  let pt : A ⟶ Hm ⊗ A := AssociatorTriangle.pointInsert (eHomEquiv V f) A
  let gi : Hm ⊗ A ⟶ RF.obj xL := EnrichedDayKernel.gen d.tensorEnrichedFunctor G HJ xL z
  let v : A ⟶ RF.obj xR := AssociatorUnit.unitGenerator d.tensorEnrichedFunctor G HJ z
  let gs : W ⊗ (B ⊗ LF.obj xL) ⟶ valueE d F G H J m :=
    EnrichedDayKernel.gen d.tensorEnrichedFunctor F LF m p
  let gt : W ⊗ (B ⊗ RF.obj xL) ⟶ valueC d F G H J m :=
    EnrichedDayKernel.gen d.tensorEnrichedFunctor F RF m p
  let gc : W' ⊗ (B ⊗ RF.obj xR) ⟶ valueC d F G H J m :=
    EnrichedDayKernel.gen d.tensorEnrichedFunctor F RF m (a, xR)
  let a3 : LF.obj xL ⟶ RF.obj xL :=
    EnrichedFunctorCat.component (AssociatorConstruction.functorIso d G H J).hom xL
  let fm : valueE d F G H J m ⟶ valueC d F G H J m :=
    Input.mapAt d.tensorEnrichedFunctor (GradedNatTrans.unitId F)
      (AssociatorConstruction.functorIso d G H J).hom m
  let pre : W ⊗ (B ⊗ A) ⟶ W ⊗ (B ⊗ (Hm ⊗ A)) := W ◁ (B ◁ pt)
  let ng : W ⊗ (B ⊗ (Hm ⊗ A)) ⟶ valueC d F G H J m :=
    AssociatorFaces.Right.nestedGenerator d.tensorEnrichedFunctor d.tensorEnrichedFunctor G HJ F m p
      z
  let ct : W ⊗ (B ⊗ (Hm ⊗ A)) ⟶ W' ⊗ (B ⊗ A) :=
    AssociatorRightFlattening.contractWord d F G HJ m p z
  let gr : W' ⊗ (B ⊗ A) ⟶ AssociatorFlat.rightPoint d F G HJ m :=
    AssociatorFlat.rightGenerator d F G HJ m ((a, b), c ⊗ e)
  let r := AssociatorRightFlattening.flatToNested d F G HJ m
  let w : W ⟶ W' := eHomWhiskerRight V (a ◁ f) m
  let q0 : W ⊗ (B ⊗ L) ⟶ W ⊗ (B ⊗ R) := 𝟙 W ⊗ₘ (𝟙 B ⊗ₘ cv)
  let q1 : W ⊗ (B ⊗ R) ⟶ W ⊗ (B ⊗ A) := 𝟙 W ⊗ₘ (𝟙 B ⊗ₘ t)
  have hu : u ≫ a3 = cv ≫ t ≫ pt ≫ gi := by
    have ha : a3 = (AssociatorConstruction.componentIso d G H J xL).hom :=
      AssociatorConstruction.functorIso_hom_component d G H J xL
    exact (congrArg (fun y => u ≫ y) ha).trans (primitive_associator_generator d G H J ((b, c), e))
  have hinput : gs ≫ fm = (𝟙 W ⊗ₘ (𝟙 B ⊗ₘ a3)) ≫ gt := by
    have h := Input.gen_mapAt d.tensorEnrichedFunctor
      (GradedNatTrans.unitId F) (AssociatorConstruction.functorIso d G H J).hom m p
    simp only [GradedNatTrans.unitId_component] at h
    exact h
  have hng : ng = W ◁ (B ◁ gi) ≫ gt := rfl
  have hsource : genE d F G H J m X ≫ fm = q0 ≫ q1 ≫ pre ≫ ng := by
    change ((𝟙 W ⊗ₘ (𝟙 B ⊗ₘ u)) ≫ gs) ≫ fm = q0 ≫ q1 ≫ pre ≫ ng
    rw [Category.assoc, hinput]
    have hcombine : (𝟙 W ⊗ₘ (𝟙 B ⊗ₘ u)) ≫ (𝟙 W ⊗ₘ (𝟙 B ⊗ₘ a3)) =
        𝟙 W ⊗ₘ (𝟙 B ⊗ₘ (u ≫ a3)) := by
      simp only [tensorHom_comp_tensorHom, Category.id_comp]
    rw [← Category.assoc, hcombine, hu]
    rw [hng]
    simp only [q0, q1, pre, ← id_tensorHom,
      tensorHom_comp_tensorHom_assoc, tensorHom_comp_tensorHom, Category.comp_id]
  have hct : pre ≫ ct = w ⊗ₘ 𝟙 (B ⊗ A) :=
    AssociatorTriangle.right_contractWord_point d F G HJ m p z f
  have hfactor : ct ≫ gr ≫ r = ng :=
    AssociatorRightFlattening.contractWord_generator_factorization d F G HJ m p z
  have hgr : gr ≫ r = (𝟙 W' ⊗ₘ (𝟙 B ⊗ₘ v)) ≫ gc :=
    AssociatorRightFlattening.rightGenerator_flatToNested d F G HJ m ((a, b), c ⊗ e)
  have hnorm : pre ≫ ng = (w ⊗ₘ (𝟙 B ⊗ₘ v)) ≫ gc := by
    calc
      _ = pre ≫ (ct ≫ gr ≫ r) := congrArg (fun y => pre ≫ y) hfactor.symm
      _ = (pre ≫ ct) ≫ gr ≫ r := by simp only [Category.assoc]
      _ = (w ⊗ₘ 𝟙 (B ⊗ A)) ≫ gr ≫ r := congrArg (fun y => y ≫ gr ≫ r) hct
      _ = (w ⊗ₘ 𝟙 (B ⊗ A)) ≫ ((𝟙 W' ⊗ₘ (𝟙 B ⊗ₘ v)) ≫ gc) :=
        congrArg (fun y => (w ⊗ₘ 𝟙 (B ⊗ A)) ≫ y) hgr
      _ = _ := by simp only [tensorHom_comp_tensorHom_assoc, Category.comp_id, Category.id_comp]
  let nc : W' ⊗ (B ⊗ R) ⟶ valueC d F G H J m := genC d F G H J m X
  have hraw : q0 ≫ q1 ≫ pre ≫ ng = (w ⊗ₘ (𝟙 B ⊗ₘ cv)) ≫ nc := by
    have hn := congrArg (fun y => q0 ≫ q1 ≫ y) hnorm
    have hright : q0 ≫ q1 ≫ ((w ⊗ₘ (𝟙 B ⊗ₘ v)) ≫ gc) =
        (w ⊗ₘ (𝟙 B ⊗ₘ cv)) ≫ nc := by
      change q0 ≫ q1 ≫ (w ⊗ₘ (𝟙 B ⊗ₘ v)) ≫ gc =
        (w ⊗ₘ (𝟙 B ⊗ₘ cv)) ≫ (𝟙 W' ⊗ₘ (𝟙 B ⊗ₘ (t ≫ v))) ≫ gc
      simp only [q0, q1, tensorHom_comp_tensorHom_assoc, tensorHom_comp_tensorHom,
        Category.id_comp, Category.comp_id]
    exact hn.trans hright
  have hw : (AssociatorQuadFlat.weightIsoEC d m X).hom = w := by
    dsimp only [AssociatorQuadFlat.weightIsoEC, AssociatorQuadMaps.weightIso, Iso.eHomCongr,
      AssociatorQuadIndex.edgeEC, MonoidalCategory.tensorIso]
    simp only [Iso.refl_hom, Iso.refl_inv, eHomWhiskerLeft_id, Category.comp_id]
    exact congrArg (fun y => eHomWhiskerRight V y m) (id_tensorHom a f)
  have hc : (AssociatorQuadCoefficient.edgeEC F G H J X).hom = 𝟙 B ⊗ₘ cv := rfl
  have hword : (AssociatorQuadFlat.weightIsoEC d m X).hom ⊗ₘ
      (AssociatorQuadCoefficient.edgeEC F G H J X).hom = w ⊗ₘ (𝟙 B ⊗ₘ cv) :=
    congrArg₂ (fun f g => f ⊗ₘ g) hw hc
  have ht : genE d F G H J m X ≫ fm = (w ⊗ₘ (𝟙 B ⊗ₘ cv)) ≫ nc := hsource.trans hraw
  exact ht.trans (congrArg (fun y => y ≫ nc) hword.symm)

/-- The complete second nested Day pentagon route keeps all three original index and coefficient
  words. -/
theorem second_route (X : ((I × I) × I) × I) :
    genA d F G H J m X ≫ Input.mapAt d.tensorEnrichedFunctor
        (AssociatorConstruction.functorIso d F G H).hom (GradedNatTrans.unitId J) m ≫
      (AssociatorConstruction.componentIso d F (day d G H) J m).hom ≫
      Input.mapAt d.tensorEnrichedFunctor (GradedNatTrans.unitId F)
        (AssociatorConstruction.functorIso d G H J).hom m =
    ((AssociatorQuadFlat.weightIsoAD d m X).hom ⊗ₘ (AssociatorQuadCoefficient.edgeAD F G H J X).hom)
      ≫
      ((AssociatorQuadFlat.weightIsoDE d m X).hom ⊗ₘ (AssociatorQuadCoefficient.edgeDE F G H J
        X).hom) ≫
      ((AssociatorQuadFlat.weightIsoEC d m X).hom ⊗ₘ (AssociatorQuadCoefficient.edgeEC F G H J
        X).hom) ≫
        genC d F G H J m X := by
  let A := valueA d F G H J m
  let D := valueD d F G H J m
  let E := valueE d F G H J m
  let C := valueC d F G H J m
  let gA : AssociatorQuadFlat.objects d F G H J m .a X ⟶ A := genA d F G H J m X
  let gD : AssociatorQuadFlat.objects d F G H J m .d X ⟶ D := genD d F G H J m X
  let gE : AssociatorQuadFlat.objects d F G H J m .e X ⟶ E := genE d F G H J m X
  let gC : AssociatorQuadFlat.objects d F G H J m .c X ⟶ C := genC d F G H J m X
  let a : A ⟶ D := Input.mapAt d.tensorEnrichedFunctor
    (AssociatorConstruction.functorIso d F G H).hom (GradedNatTrans.unitId J) m
  let b : D ⟶ E := (AssociatorConstruction.componentIso d F (day d G H) J m).hom
  let c : E ⟶ C := Input.mapAt d.tensorEnrichedFunctor (GradedNatTrans.unitId F)
    (AssociatorConstruction.functorIso d G H J).hom m
  let wAD : AssociatorQuadFlat.objects d F G H J m .a X ⟶ AssociatorQuadFlat.objects d F G H J m .d
    X :=
    (AssociatorQuadFlat.weightIsoAD d m X).hom ⊗ₘ (AssociatorQuadCoefficient.edgeAD F G H J X).hom
  let wDE : AssociatorQuadFlat.objects d F G H J m .d X ⟶ AssociatorQuadFlat.objects d F G H J m .e
    X :=
    (AssociatorQuadFlat.weightIsoDE d m X).hom ⊗ₘ (AssociatorQuadCoefficient.edgeDE F G H J X).hom
  let wEC : AssociatorQuadFlat.objects d F G H J m .e X ⟶ AssociatorQuadFlat.objects d F G H J m .c
    X :=
    (AssociatorQuadFlat.weightIsoEC d m X).hom ⊗ₘ (AssociatorQuadCoefficient.edgeEC F G H J X).hom
  have hAD : gA ≫ a = wAD ≫ gD := genA_tensor_associator d F G H J m X
  have hDE : gD ≫ b = wDE ≫ gE := genD_associator d F G H J m X
  have hEC : gE ≫ c = wEC ≫ gC := genE_tensor_associator d F G H J m X
  change gA ≫ a ≫ b ≫ c = wAD ≫ wDE ≫ wEC ≫ gC
  rw [← Category.assoc gA a, hAD, Category.assoc, ← Category.assoc gD b,
    hDE, Category.assoc, hEC]

end CategoryTheory.EnrichedDayKernel.AssociatorQuadSecondRoute
