/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua
module

public import MathlibExt.CategoryTheory.Enriched.Monoidal.DayConvolution.AssociatorComparison

/-!
# Associator Components

Original enriched Day objects, full Hom maps and chosen coend presentations.
-/

@[expose] public section

set_option autoImplicit false
noncomputable section
universe uV vV uI vI
open CategoryTheory CategoryTheory.Limits MonoidalCategory Opposite
open scoped MonoidalClosed

namespace CategoryTheory.EnrichedDayKernel.AssociatorConstruction
variable {V : Type uV} [Category.{vV} V] [MonoidalCategory V]
  [SymmetricCategory V] [MonoidalClosed V]
  {I : Type uI} [Category.{vI} I] [MonoidalCategory I] [EnrichedOrdinaryCategory V I]
  (d : EnrichedMonoidalCategoryData V I) (F G H : EnrichedFunctor V I V) (m : I)
attribute [local instance] Enriched.prodCategory
variable [HasCoproduct (AssociatorFlat.leftObjects d F G H m)]
  [HasCoproduct (AssociatorFlat.leftRelations d F G H m)]
  [HasCoequalizer (AssociatorFlat.leftMap0 d F G H m) (AssociatorFlat.leftMap1 d F G H m)]
  [HasCoproduct (AssociatorPresentation.Left.simultaneousObjects d.tensorEnrichedFunctor
    d.tensorEnrichedFunctor F G H m)]
  [HasCoproduct (AssociatorPresentation.Left.simultaneousRelations d.tensorEnrichedFunctor
    d.tensorEnrichedFunctor F G H m)]
  [HasCoequalizer
    (AssociatorPresentation.Left.simultaneousLeftMap d.tensorEnrichedFunctor d.tensorEnrichedFunctor
      F G H m)
    (AssociatorPresentation.Left.simultaneousRightMap d.tensorEnrichedFunctor
      d.tensorEnrichedFunctor F G H m)]

variable
  [∀ k : I, HasCoproduct (EnrichedDayKernel.objects d.tensorEnrichedFunctor F G k)]
  [∀ k : I, HasCoproduct (EnrichedDayKernel.relations d.tensorEnrichedFunctor F G k)]
  [∀ k : I, HasCoequalizer (EnrichedDayKernel.leftMap d.tensorEnrichedFunctor F G k)
    (EnrichedDayKernel.rightMap d.tensorEnrichedFunctor F G k)]
  [∀ p : I × I, HasCoproduct (AssociatorFaces.Left.objects d.tensorEnrichedFunctor
    d.tensorEnrichedFunctor F G H m p)]
  [∀ p : I × I, HasCoproduct (AssociatorFaces.Left.innerRelations d.tensorEnrichedFunctor
    d.tensorEnrichedFunctor F G H m p)]
  [∀ p : I × I, HasCoequalizer
    (AssociatorFaces.Left.innerLeftMap d.tensorEnrichedFunctor d.tensorEnrichedFunctor F G H m p)
    (AssociatorFaces.Left.innerRightMap d.tensorEnrichedFunctor d.tensorEnrichedFunctor F G H m p)]
  [∀ pq : (I × I) × (I × I), HasCoproduct
    (AssociatorPresentation.Left.relationObjects d.tensorEnrichedFunctor d.tensorEnrichedFunctor F G
      H m pq)]
  [∀ pq : (I × I) × (I × I), HasCoproduct
    (AssociatorPresentation.Left.relationRelations d.tensorEnrichedFunctor d.tensorEnrichedFunctor F
      G H m pq)]
  [∀ pq : (I × I) × (I × I), HasCoequalizer
    (AssociatorPresentation.Left.relationLeftMap d.tensorEnrichedFunctor d.tensorEnrichedFunctor F G
      H m pq)
    (AssociatorPresentation.Left.relationRightMap d.tensorEnrichedFunctor d.tensorEnrichedFunctor F
      G H m pq)]
  [HasCoproduct (AssociatorPresentation.Left.innerObjects d.tensorEnrichedFunctor
    d.tensorEnrichedFunctor F G H m)]
  [HasCoproduct (AssociatorPresentation.Left.outerRelations d.tensorEnrichedFunctor
    d.tensorEnrichedFunctor F G H m)]
  [HasCoequalizer
    (AssociatorPresentation.Left.outerLeftMap d.tensorEnrichedFunctor d.tensorEnrichedFunctor F G H
      m)
    (AssociatorPresentation.Left.outerRightMap d.tensorEnrichedFunctor d.tensorEnrichedFunctor F G H
      m)]
  [HasCoproduct (EnrichedDayKernel.objects d.tensorEnrichedFunctor (Output.functor
    d.tensorEnrichedFunctor F G) H m)]
  [HasCoproduct (EnrichedDayKernel.relations d.tensorEnrichedFunctor (Output.functor
    d.tensorEnrichedFunctor F G) H m)]
  [HasCoequalizer
    (EnrichedDayKernel.leftMap d.tensorEnrichedFunctor (Output.functor d.tensorEnrichedFunctor F G)
      H m)
    (EnrichedDayKernel.rightMap d.tensorEnrichedFunctor (Output.functor d.tensorEnrichedFunctor F G)
      H m)]

variable [HasCoproduct (AssociatorFlat.rightObjects d F G H m)]
  [HasCoproduct (AssociatorFlat.rightRelations d F G H m)]
  [HasCoequalizer (AssociatorFlat.rightMap0 d F G H m) (AssociatorFlat.rightMap1 d F G H m)]
  [HasCoproduct (AssociatorPresentation.Right.simultaneousObjects d.tensorEnrichedFunctor
    d.tensorEnrichedFunctor G H F m)]
  [HasCoproduct (AssociatorPresentation.Right.simultaneousRelations d.tensorEnrichedFunctor
    d.tensorEnrichedFunctor G H F m)]
  [HasCoequalizer
    (AssociatorPresentation.Right.simultaneousLeftMap d.tensorEnrichedFunctor
      d.tensorEnrichedFunctor G H F m)
    (AssociatorPresentation.Right.simultaneousRightMap d.tensorEnrichedFunctor
      d.tensorEnrichedFunctor G H F m)]

variable
  [∀ k : I, HasCoproduct (EnrichedDayKernel.objects d.tensorEnrichedFunctor G H k)]
  [∀ k : I, HasCoproduct (EnrichedDayKernel.relations d.tensorEnrichedFunctor G H k)]
  [∀ k : I, HasCoequalizer (EnrichedDayKernel.leftMap d.tensorEnrichedFunctor G H k)
    (EnrichedDayKernel.rightMap d.tensorEnrichedFunctor G H k)]
  [∀ p : I × I, HasCoproduct (AssociatorFaces.Right.objects d.tensorEnrichedFunctor
    d.tensorEnrichedFunctor G H F m p)]
  [∀ p : I × I, HasCoproduct (AssociatorFaces.Right.innerRelations d.tensorEnrichedFunctor
    d.tensorEnrichedFunctor G H F m p)]
  [∀ p : I × I, HasCoequalizer
    (AssociatorFaces.Right.innerLeftMap d.tensorEnrichedFunctor d.tensorEnrichedFunctor G H F m p)
    (AssociatorFaces.Right.innerRightMap d.tensorEnrichedFunctor d.tensorEnrichedFunctor G H F m p)]
  [∀ pq : (I × I) × (I × I), HasCoproduct
    (AssociatorPresentation.Right.relationObjects d.tensorEnrichedFunctor d.tensorEnrichedFunctor G
      H F m pq)]
  [∀ pq : (I × I) × (I × I), HasCoproduct
    (AssociatorPresentation.Right.relationRelations d.tensorEnrichedFunctor d.tensorEnrichedFunctor
      G H F m pq)]
  [∀ pq : (I × I) × (I × I), HasCoequalizer
    (AssociatorPresentation.Right.relationLeftMap d.tensorEnrichedFunctor d.tensorEnrichedFunctor G
      H F m pq)
    (AssociatorPresentation.Right.relationRightMap d.tensorEnrichedFunctor d.tensorEnrichedFunctor G
      H F m pq)]
  [HasCoproduct (AssociatorPresentation.Right.innerObjects d.tensorEnrichedFunctor
    d.tensorEnrichedFunctor G H F m)]
  [HasCoproduct (AssociatorPresentation.Right.outerRelations d.tensorEnrichedFunctor
    d.tensorEnrichedFunctor G H F m)]
  [HasCoequalizer
    (AssociatorPresentation.Right.outerLeftMap d.tensorEnrichedFunctor d.tensorEnrichedFunctor G H F
      m)
    (AssociatorPresentation.Right.outerRightMap d.tensorEnrichedFunctor d.tensorEnrichedFunctor G H
      F m)]
  [HasCoproduct (EnrichedDayKernel.objects d.tensorEnrichedFunctor F (Output.functor
    d.tensorEnrichedFunctor G H) m)]
  [HasCoproduct (EnrichedDayKernel.relations d.tensorEnrichedFunctor F (Output.functor
    d.tensorEnrichedFunctor G H) m)]
  [HasCoequalizer
    (EnrichedDayKernel.leftMap d.tensorEnrichedFunctor F (Output.functor d.tensorEnrichedFunctor G
      H) m)
    (EnrichedDayKernel.rightMap d.tensorEnrichedFunctor F (Output.functor d.tensorEnrichedFunctor G
      H) m)]

/-- The actual Day associator on the unchanged original nested values and chosen presentations. -/
def componentIso :
    EnrichedDayKernel.obj d.tensorEnrichedFunctor (Output.functor d.tensorEnrichedFunctor F G) H m ≅
      EnrichedDayKernel.obj d.tensorEnrichedFunctor F (Output.functor d.tensorEnrichedFunctor G H) m
        :=
  (AssociatorFlattening.iso d F G H m).symm ≪≫ AssociatorFlat.iso d F G H m ≪≫
    AssociatorRightFlattening.iso d F G H m

/-- The forward path uses actual left descent, original flat associator and original right
  insertion. -/
@[reassoc]
theorem componentIso_hom :
    (componentIso d F G H m).hom =
      AssociatorFlattening.nestedToFlat d F G H m ≫ (AssociatorFlat.iso d F G H m).hom ≫
        AssociatorRightFlattening.flatToNested d F G H m := by
  simp only [componentIso, Iso.trans_hom, Iso.symm_hom, AssociatorFlattening.iso,
    AssociatorRightFlattening.iso]

/-- The inverse uses the opposite actual descent, index/coefficient factors and insertion. -/
@[reassoc]
theorem componentIso_inv :
    (componentIso d F G H m).inv =
      AssociatorRightFlattening.nestedToFlat d F G H m ≫ (AssociatorFlat.iso d F G H m).inv ≫
        AssociatorFlattening.flatToNested d F G H m := by
  simp only [componentIso, Iso.trans_inv, Iso.symm_inv, AssociatorFlattening.iso,
    AssociatorRightFlattening.iso, Category.assoc]

/-- Every original left nested generator keeps its full contraction and actual associator factors.
-/
@[reassoc]
theorem nestedGenerator_hom (p a : I × I) :
    AssociatorFaces.Left.nestedGenerator d.tensorEnrichedFunctor d.tensorEnrichedFunctor F G H m p a
      ≫
        (componentIso d F G H m).hom =
    AssociatorFlattening.contractWord d F G H m p a ≫
      (eHomWhiskerRight V (α_ a.1 a.2 p.2).inv m ⊗ₘ
        (α_ (F.obj a.1) (G.obj a.2) (H.obj p.2)).hom) ≫
      AssociatorFlat.rightGenerator d F G H m (a, p.2) ≫
        AssociatorRightFlattening.flatToNested d F G H m := by
  let X : (I × I) × I := (a, p.2)
  let DL := AssociatorFlat.leftObjects d F G H m X
  let DR := AssociatorFlat.rightObjects d F G H m X
  let NL := EnrichedDayKernel.obj d.tensorEnrichedFunctor (Output.functor d.tensorEnrichedFunctor F
    G) H m
  let NR := EnrichedDayKernel.obj d.tensorEnrichedFunctor F (Output.functor d.tensorEnrichedFunctor
    G H) m
  let P := AssociatorFlat.leftPoint d F G H m
  let Q := AssociatorFlat.rightPoint d F G H m
  let D := AssociatorFaces.Left.objects d.tensorEnrichedFunctor d.tensorEnrichedFunctor F G H m p a
  let g : D ⟶ NL := AssociatorFaces.Left.nestedGenerator d.tensorEnrichedFunctor
    d.tensorEnrichedFunctor F G H m p a
  let c : D ⟶ DL := AssociatorFlattening.contractWord d F G H m p a
  let l : NL ⟶ P := AssociatorFlattening.nestedToFlat d F G H m
  let f : P ⟶ Q := (AssociatorFlat.iso d F G H m).hom
  let r : Q ⟶ NR := AssociatorRightFlattening.flatToNested d F G H m
  let g0 : DL ⟶ P := AssociatorFlat.leftGenerator d F G H m X
  let g1 : DR ⟶ Q := AssociatorFlat.rightGenerator d F G H m X
  let w : DL ⟶ DR := eHomWhiskerRight V (α_ a.1 a.2 p.2).inv m ⊗ₘ
    (α_ (F.obj a.1) (G.obj a.2) (H.obj p.2)).hom
  have hg : g ≫ l = c ≫ g0 := AssociatorFlattening.nestedGenerator_nestedToFlat d F G H m p a
  have hf : g0 ≫ f = w ≫ g1 := AssociatorFlat.leftGenerator_iso_hom d F G H m X
  have ht : (componentIso d F G H m).hom = l ≫ f ≫ r := componentIso_hom d F G H m
  change g ≫ (componentIso d F G H m).hom = c ≫ w ≫ g1 ≫ r
  rw [ht]
  have h0 := congrArg (fun z => z ≫ f ≫ r) hg
  have h1 := congrArg (fun z => c ≫ z ≫ r) hf
  simp only [Category.assoc] at h0 h1
  exact h0.trans h1

/-- Every original right nested generator retains the exact opposite index/coefficient factors. -/
@[reassoc]
theorem nestedGenerator_inv (p a : I × I) :
    AssociatorFaces.Right.nestedGenerator d.tensorEnrichedFunctor d.tensorEnrichedFunctor G H F m p
      a ≫
        (componentIso d F G H m).inv =
    AssociatorRightFlattening.contractWord d F G H m p a ≫
      (eHomWhiskerRight V (α_ p.1 a.1 a.2).hom m ⊗ₘ
        (α_ (F.obj p.1) (G.obj a.1) (H.obj a.2)).inv) ≫
      AssociatorFlat.leftGenerator d F G H m ((p.1, a.1), a.2) ≫
        AssociatorFlattening.flatToNested d F G H m := by
  let X : (I × I) × I := ((p.1, a.1), a.2)
  let DL := AssociatorFlat.leftObjects d F G H m X
  let DR := AssociatorFlat.rightObjects d F G H m X
  let NL := EnrichedDayKernel.obj d.tensorEnrichedFunctor (Output.functor d.tensorEnrichedFunctor F
    G) H m
  let NR := EnrichedDayKernel.obj d.tensorEnrichedFunctor F (Output.functor d.tensorEnrichedFunctor
    G H) m
  let P := AssociatorFlat.leftPoint d F G H m
  let Q := AssociatorFlat.rightPoint d F G H m
  let D := AssociatorFaces.Right.objects d.tensorEnrichedFunctor d.tensorEnrichedFunctor G H F m p a
  let g : D ⟶ NR := AssociatorFaces.Right.nestedGenerator d.tensorEnrichedFunctor
    d.tensorEnrichedFunctor G H F m p a
  let c : D ⟶ DR := AssociatorRightFlattening.contractWord d F G H m p a
  let r : NR ⟶ Q := AssociatorRightFlattening.nestedToFlat d F G H m
  let f : Q ⟶ P := (AssociatorFlat.iso d F G H m).inv
  let l : P ⟶ NL := AssociatorFlattening.flatToNested d F G H m
  let g0 : DR ⟶ Q := AssociatorFlat.rightGenerator d F G H m X
  let g1 : DL ⟶ P := AssociatorFlat.leftGenerator d F G H m X
  let w : DR ⟶ DL := eHomWhiskerRight V (α_ p.1 a.1 a.2).hom m ⊗ₘ
    (α_ (F.obj p.1) (G.obj a.1) (H.obj a.2)).inv
  have hg : g ≫ r = c ≫ g0 := AssociatorRightFlattening.nestedGenerator_nestedToFlat d F G H m p a
  have hf : g0 ≫ f = w ≫ g1 := AssociatorFlat.rightGenerator_iso_inv d F G H m X
  have ht : (componentIso d F G H m).inv = r ≫ f ≫ l := componentIso_inv d F G H m
  change g ≫ (componentIso d F G H m).inv = c ≫ w ≫ g1 ≫ l
  rw [ht]
  have h0 := congrArg (fun z => z ≫ f ≫ l) hg
  have h1 := congrArg (fun z => c ≫ z ≫ l) hf
  simp only [Category.assoc] at h0 h1
  exact h0.trans h1

/-- The forward triple-generator path uses inverse INDEX associator and forward COEFFICIENT
  associator. -/
@[reassoc]
theorem tripleGenerator_hom (X : (I × I) × I) :
    AssociatorFlat.leftGenerator d F G H m X ≫ AssociatorFlattening.flatToNested d F G H m ≫
        (componentIso d F G H m).hom =
      (eHomWhiskerRight V (α_ X.1.1 X.1.2 X.2).inv m ⊗ₘ
        (α_ (F.obj X.1.1) (G.obj X.1.2) (H.obj X.2)).hom) ≫
      AssociatorFlat.rightGenerator d F G H m X ≫
        AssociatorRightFlattening.flatToNested d F G H m := by
  let DL := AssociatorFlat.leftObjects d F G H m X
  let DR := AssociatorFlat.rightObjects d F G H m X
  let NL := EnrichedDayKernel.obj d.tensorEnrichedFunctor (Output.functor d.tensorEnrichedFunctor F
    G) H m
  let NR := EnrichedDayKernel.obj d.tensorEnrichedFunctor F (Output.functor d.tensorEnrichedFunctor
    G H) m
  let P := AssociatorFlat.leftPoint d F G H m
  let Q := AssociatorFlat.rightPoint d F G H m
  let l : P ⟶ NL := AssociatorFlattening.flatToNested d F G H m
  let li : NL ⟶ P := AssociatorFlattening.nestedToFlat d F G H m
  let f : P ⟶ Q := (AssociatorFlat.iso d F G H m).hom
  let r : Q ⟶ NR := AssociatorRightFlattening.flatToNested d F G H m
  let g0 : DL ⟶ P := AssociatorFlat.leftGenerator d F G H m X
  let g1 : DR ⟶ Q := AssociatorFlat.rightGenerator d F G H m X
  let w : DL ⟶ DR := eHomWhiskerRight V (α_ X.1.1 X.1.2 X.2).inv m ⊗ₘ
    (α_ (F.obj X.1.1) (G.obj X.1.2) (H.obj X.2)).hom
  have hi : l ≫ li = 𝟙 P := AssociatorFlattening.flatToNested_nestedToFlat d F G H m
  have hf : g0 ≫ f = w ≫ g1 := AssociatorFlat.leftGenerator_iso_hom d F G H m X
  have ht : (componentIso d F G H m).hom = li ≫ f ≫ r := componentIso_hom d F G H m
  change g0 ≫ l ≫ (componentIso d F G H m).hom = w ≫ g1 ≫ r
  rw [ht]
  have h0 := congrArg (fun z => g0 ≫ z ≫ f ≫ r) hi
  have h1 := congrArg (fun z => z ≫ r) hf
  simp only [Category.assoc, Category.id_comp] at h0 h1
  exact h0.trans h1

/-- The inverse triple-generator path uses the actual opposite factors on the same inputs. -/
@[reassoc]
theorem tripleGenerator_inv (X : (I × I) × I) :
    AssociatorFlat.rightGenerator d F G H m X ≫ AssociatorRightFlattening.flatToNested d F G H m ≫
        (componentIso d F G H m).inv =
      (eHomWhiskerRight V (α_ X.1.1 X.1.2 X.2).hom m ⊗ₘ
        (α_ (F.obj X.1.1) (G.obj X.1.2) (H.obj X.2)).inv) ≫
      AssociatorFlat.leftGenerator d F G H m X ≫ AssociatorFlattening.flatToNested d F G H m := by
  let DL := AssociatorFlat.leftObjects d F G H m X
  let DR := AssociatorFlat.rightObjects d F G H m X
  let NL := EnrichedDayKernel.obj d.tensorEnrichedFunctor (Output.functor d.tensorEnrichedFunctor F
    G) H m
  let NR := EnrichedDayKernel.obj d.tensorEnrichedFunctor F (Output.functor d.tensorEnrichedFunctor
    G H) m
  let P := AssociatorFlat.leftPoint d F G H m
  let Q := AssociatorFlat.rightPoint d F G H m
  let r : Q ⟶ NR := AssociatorRightFlattening.flatToNested d F G H m
  let ri : NR ⟶ Q := AssociatorRightFlattening.nestedToFlat d F G H m
  let f : Q ⟶ P := (AssociatorFlat.iso d F G H m).inv
  let l : P ⟶ NL := AssociatorFlattening.flatToNested d F G H m
  let g0 : DR ⟶ Q := AssociatorFlat.rightGenerator d F G H m X
  let g1 : DL ⟶ P := AssociatorFlat.leftGenerator d F G H m X
  let w : DR ⟶ DL := eHomWhiskerRight V (α_ X.1.1 X.1.2 X.2).hom m ⊗ₘ
    (α_ (F.obj X.1.1) (G.obj X.1.2) (H.obj X.2)).inv
  have hi : r ≫ ri = 𝟙 Q := AssociatorRightFlattening.flatToNested_nestedToFlat d F G H m
  have hf : g0 ≫ f = w ≫ g1 := AssociatorFlat.rightGenerator_iso_inv d F G H m X
  have ht : (componentIso d F G H m).inv = ri ≫ f ≫ l := componentIso_inv d F G H m
  change g0 ≫ r ≫ (componentIso d F G H m).inv = w ≫ g1 ≫ l
  rw [ht]
  have h0 := congrArg (fun z => g0 ≫ z ≫ f ≫ l) hi
  have h1 := congrArg (fun z => z ≫ l) hf
  simp only [Category.assoc, Category.id_comp] at h0 h1
  exact h0.trans h1

end CategoryTheory.EnrichedDayKernel.AssociatorConstruction
