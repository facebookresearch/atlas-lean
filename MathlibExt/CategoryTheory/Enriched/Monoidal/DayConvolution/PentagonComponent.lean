/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua
module

public import MathlibExt.CategoryTheory.Enriched.Monoidal.DayConvolution.AssociatorPentagonFirst
public import MathlibExt.CategoryTheory.Enriched.Monoidal.DayConvolution.AssociatorPentagonSecond

/-!
# Pentagon Component

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


variable (F G H J : EnrichedFunctor V I V) (m : I)
  [HasCoproduct (AssociatorQuadLeft.objects d F G H J m)]
  [HasCoproduct (AssociatorQuadLeft.relations d F G H J m)]
  [HasCoequalizer (AssociatorQuadLeft.map0 d F G H J m) (AssociatorQuadLeft.map1 d F G H J m)]
  [HasCoproduct (AssociatorPresentation.Left.simultaneousObjects
    (AssociatorIndex.leftIndex d) d.tensorEnrichedFunctor (F.externalTensor G) H J m)]
  [HasCoproduct (AssociatorPresentation.Left.simultaneousRelations
    (AssociatorIndex.leftIndex d) d.tensorEnrichedFunctor (F.externalTensor G) H J m)]
  [HasCoequalizer
    (AssociatorPresentation.Left.simultaneousLeftMap
      (AssociatorIndex.leftIndex d) d.tensorEnrichedFunctor (F.externalTensor G) H J m)
    (AssociatorPresentation.Left.simultaneousRightMap
      (AssociatorIndex.leftIndex d) d.tensorEnrichedFunctor (F.externalTensor G) H J m)]
  [∀ p : I × I, HasCoproduct (AssociatorFaces.Left.objects
    (AssociatorIndex.leftIndex d) d.tensorEnrichedFunctor (F.externalTensor G) H J m p)]
  [∀ p : I × I, HasCoproduct (AssociatorFaces.Left.innerRelations
    (AssociatorIndex.leftIndex d) d.tensorEnrichedFunctor (F.externalTensor G) H J m p)]
  [∀ p : I × I, HasCoequalizer
    (AssociatorFaces.Left.innerLeftMap
      (AssociatorIndex.leftIndex d) d.tensorEnrichedFunctor (F.externalTensor G) H J m p)
    (AssociatorFaces.Left.innerRightMap
      (AssociatorIndex.leftIndex d) d.tensorEnrichedFunctor (F.externalTensor G) H J m p)]
  [∀ pq : (I × I) × (I × I), HasCoproduct (AssociatorPresentation.Left.relationObjects
    (AssociatorIndex.leftIndex d) d.tensorEnrichedFunctor (F.externalTensor G) H J m pq)]
  [∀ pq : (I × I) × (I × I), HasCoproduct (AssociatorPresentation.Left.relationRelations
    (AssociatorIndex.leftIndex d) d.tensorEnrichedFunctor (F.externalTensor G) H J m pq)]
  [∀ pq : (I × I) × (I × I), HasCoequalizer
    (AssociatorPresentation.Left.relationLeftMap
      (AssociatorIndex.leftIndex d) d.tensorEnrichedFunctor (F.externalTensor G) H J m pq)
    (AssociatorPresentation.Left.relationRightMap
      (AssociatorIndex.leftIndex d) d.tensorEnrichedFunctor (F.externalTensor G) H J m pq)]
  [HasCoproduct (AssociatorPresentation.Left.innerObjects
    (AssociatorIndex.leftIndex d) d.tensorEnrichedFunctor (F.externalTensor G) H J m)]
  [HasCoproduct (AssociatorPresentation.Left.outerRelations
    (AssociatorIndex.leftIndex d) d.tensorEnrichedFunctor (F.externalTensor G) H J m)]
  [HasCoequalizer
    (AssociatorPresentation.Left.outerLeftMap
      (AssociatorIndex.leftIndex d) d.tensorEnrichedFunctor (F.externalTensor G) H J m)
    (AssociatorPresentation.Left.outerRightMap
      (AssociatorIndex.leftIndex d) d.tensorEnrichedFunctor (F.externalTensor G) H J m)]

open AssociatorQuadNested

/-- Pentagon coherence for the original chosen nested values on every four genuine inputs. -/
theorem pentagon_component :
    Input.mapAt d.tensorEnrichedFunctor (AssociatorConstruction.functorIso d F G H).hom
        (GradedNatTrans.unitId J) m ≫
      (AssociatorConstruction.componentIso d F (day d G H) J m).hom ≫
      Input.mapAt d.tensorEnrichedFunctor (GradedNatTrans.unitId F)
        (AssociatorConstruction.functorIso d G H J).hom m =
    (AssociatorConstruction.componentIso d (day d F G) H J m).hom ≫
      (AssociatorConstruction.componentIso d F G (day d H J) m).hom := by
  apply AssociatorQuadLeft.hom_ext d F G H J m
  intro X
  let A := valueA d F G H J m
  let B := valueB d F G H J m
  let C := valueC d F G H J m
  let D := valueD d F G H J m
  let E := valueE d F G H J m
  let gA : AssociatorQuadFlat.objects d F G H J m .a X ⟶ A := genA d F G H J m X
  let gC : AssociatorQuadFlat.objects d F G H J m .c X ⟶ C := genC d F G H J m X
  let aAB : A ⟶ B := (AssociatorConstruction.componentIso d (day d F G) H J m).hom
  let aBC : B ⟶ C := (AssociatorConstruction.componentIso d F G (day d H J) m).hom
  let aAD : A ⟶ D := Input.mapAt d.tensorEnrichedFunctor
    (AssociatorConstruction.functorIso d F G H).hom (GradedNatTrans.unitId J) m
  let aDE : D ⟶ E := (AssociatorConstruction.componentIso d F (day d G H) J m).hom
  let aEC : E ⟶ C := Input.mapAt d.tensorEnrichedFunctor (GradedNatTrans.unitId F)
    (AssociatorConstruction.functorIso d G H J).hom m
  let WA := (AssociatorQuadFlat.weight d m .a).obj (op X)
  let CA := (AssociatorQuadFlat.coefficient F G H J .a).obj X
  let WB := (AssociatorQuadFlat.weight d m .b).obj (op X)
  let CB := (AssociatorQuadFlat.coefficient F G H J .b).obj X
  let WC := (AssociatorQuadFlat.weight d m .c).obj (op X)
  let CC := (AssociatorQuadFlat.coefficient F G H J .c).obj X
  let WD := (AssociatorQuadFlat.weight d m .d).obj (op X)
  let CD := (AssociatorQuadFlat.coefficient F G H J .d).obj X
  let WE := (AssociatorQuadFlat.weight d m .e).obj (op X)
  let CE := (AssociatorQuadFlat.coefficient F G H J .e).obj X
  let wAB : WA ⟶ WB := (AssociatorQuadFlat.weightIsoAB d m X).hom
  let cAB : CA ⟶ CB := (AssociatorQuadCoefficient.edgeAB F G H J X).hom
  let wBC : WB ⟶ WC := (AssociatorQuadFlat.weightIsoBC d m X).hom
  let cBC : CB ⟶ CC := (AssociatorQuadCoefficient.edgeBC F G H J X).hom
  let wAD : WA ⟶ WD := (AssociatorQuadFlat.weightIsoAD d m X).hom
  let cAD : CA ⟶ CD := (AssociatorQuadCoefficient.edgeAD F G H J X).hom
  let wDE : WD ⟶ WE := (AssociatorQuadFlat.weightIsoDE d m X).hom
  let cDE : CD ⟶ CE := (AssociatorQuadCoefficient.edgeDE F G H J X).hom
  let wEC : WE ⟶ WC := (AssociatorQuadFlat.weightIsoEC d m X).hom
  let cEC : CE ⟶ CC := (AssociatorQuadCoefficient.edgeEC F G H J X).hom
  have hfirst : gA ≫ aAB ≫ aBC = (wAB ⊗ₘ cAB) ≫ (wBC ⊗ₘ cBC) ≫ gC :=
    AssociatorQuadFirstRoute.first_route d F G H J m X
  have hsecond : gA ≫ aAD ≫ aDE ≫ aEC =
      (wAD ⊗ₘ cAD) ≫ (wDE ⊗ₘ cDE) ≫ (wEC ⊗ₘ cEC) ≫ gC :=
    AssociatorQuadSecondRoute.second_route d F G H J m X
  have hw : wAB ≫ wBC = wAD ≫ wDE ≫ wEC := AssociatorQuadFlat.weight_pentagon d m X
  have hc : cAB ≫ cBC = cAD ≫ cDE ≫ cEC :=
    AssociatorQuadCoefficient.edge_pentagon F G H J X
  have ht : (wAB ⊗ₘ cAB) ≫ (wBC ⊗ₘ cBC) =
      (wAD ⊗ₘ cAD) ≫ (wDE ⊗ₘ cDE) ≫ (wEC ⊗ₘ cEC) := by
    simpa only [tensorHom_comp_tensorHom, Category.assoc] using
      congrArg₂ (fun w c => w ⊗ₘ c) hw hc
  have ht' : (wAB ⊗ₘ cAB) ≫ (wBC ⊗ₘ cBC) ≫ gC =
      (wAD ⊗ₘ cAD) ≫ (wDE ⊗ₘ cDE) ≫ (wEC ⊗ₘ cEC) ≫ gC := by
    simpa only [Category.assoc] using congrArg (fun z => z ≫ gC) ht
  change gA ≫ aAD ≫ aDE ≫ aEC = gA ≫ aAB ≫ aBC
  exact hsecond.trans (ht'.symm.trans hfirst.symm)

end CategoryTheory.EnrichedDayKernel.AssociatorPentagon
