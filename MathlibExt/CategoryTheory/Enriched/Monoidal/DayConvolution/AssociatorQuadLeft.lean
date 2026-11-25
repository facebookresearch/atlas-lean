/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua
module

public import MathlibExt.CategoryTheory.Enriched.Monoidal.DayConvolution.Associator
public import MathlibExt.CategoryTheory.Enriched.Monoidal.DayConvolution.Tensor
public import MathlibExt.CategoryTheory.Enriched.Monoidal.DayConvolution.AssociatorComparison
public import MathlibExt.CategoryTheory.Enriched.FunctorCategoryIso
public import MathlibExt.CategoryTheory.Enriched.Monoidal.DayConvolution.AssociatorLeftGeneral
public import Mathlib.CategoryTheory.Products.Basic

/-!
# Associator Quad Left

Original enriched Day objects, full Hom maps and chosen coend presentations.
-/

@[expose] public section

set_option autoImplicit false
noncomputable section
universe uV vV uI vI
open CategoryTheory CategoryTheory.Limits MonoidalCategory Opposite
open scoped MonoidalClosed

namespace CategoryTheory.EnrichedDayKernel.AssociatorQuadLeft

variable {V : Type uV} [Category.{vV} V] [MonoidalCategory V]
  [SymmetricCategory V] [MonoidalClosed V]
  {I : Type uI} [Category.{vI} I] [MonoidalCategory I]
  [EnrichedOrdinaryCategory V I]
  (d : EnrichedMonoidalCategoryData V I)

attribute [local instance] Enriched.prodCategory

/-- The literal fully left-associated four-input enriched index. -/
abbrev flatIndex : EnrichedFunctor V (((I × I) × I) × I) I :=
  (prodEnrichedFunctor (AssociatorIndex.leftIndex d) (EnrichedFunctor.id V I)).comp V
    d.tensorEnrichedFunctor

omit [MonoidalClosed V] in
/-- Every original index remains in its original position. -/
theorem flatIndex_obj (X : ((I × I) × I) × I) :
    (flatIndex d).obj X = ((X.1.1.1 ⊗ X.1.1.2) ⊗ X.1.2) ⊗ X.2 := rfl

omit [MonoidalClosed V] in
/-- The entire four-input Hom action retains the original triple and fourth factors. -/
theorem flatIndex_map (X Y : ((I × I) × I) × I) :
    (flatIndex d).map X Y =
      ((AssociatorIndex.leftIndex d).map X.1 Y.1 ⊗ₘ 𝟙 (X.2 ⟶[V] Y.2)) ≫
        d.tensorEnrichedFunctor.map
          (((X.1.1.1 ⊗ X.1.1.2) ⊗ X.1.2), X.2)
          (((Y.1.1.1 ⊗ Y.1.1.2) ⊗ Y.1.2), Y.2) := rfl

/-- The original representable weight at the unchanged output. -/
abbrev flatWeight (m : I) : EnrichedFunctor V (((I × I) × I) × I)ᵒᵖ V :=
  weight (flatIndex d) m

variable (F G H J : EnrichedFunctor V I V)

/-- All four original coefficient functors, in their original tensor word. -/
abbrev coefficients : EnrichedFunctor V (((I × I) × I) × I) V :=
  ((F.externalTensor G).externalTensor H).externalTensor J

/-- The actual flat object family. -/
abbrev objects (m : I) : ((I × I) × I) × I → V :=
  Enriched.weightedCoend.objects (flatWeight d m) (coefficients F G H J)

/-- The actual full-Hom flat relation family. -/
abbrev relations (m : I) :
    (((I × I) × I) × I) × (((I × I) × I) × I) → V :=
  Enriched.weightedCoend.relations (flatWeight d m) (coefficients F G H J)

/-- Each summand retains the full original weight and all four coefficients. -/
theorem objects_original (m : I) (X : ((I × I) × I) × I) :
    objects d F G H J m X =
      ((((X.1.1.1 ⊗ X.1.1.2) ⊗ X.1.2) ⊗ X.2) ⟶[V] m) ⊗
        (((F.obj X.1.1.1 ⊗ G.obj X.1.1.2) ⊗ H.obj X.1.2) ⊗ J.obj X.2) := rfl

section Flat

variable (m : I)
  [HasCoproduct (objects d F G H J m)]
  [HasCoproduct (relations d F G H J m)]

/-- The relation map induced by the weight action in the flattened left four-input
  presentation. -/
abbrev map0 := Enriched.weightedCoend.leftMap (flatWeight d m) (coefficients F G H J)
/-- The relation map induced by the coefficient action in the flattened left four-input
  presentation. -/
abbrev map1 := Enriched.weightedCoend.rightMap (flatWeight d m) (coefficients F G H J)

variable [HasCoequalizer (map0 d F G H J m) (map1 d F G H J m)]

/-- The actual selected fully-left four-input flat coend. -/
abbrev point : V := Enriched.weightedCoend (flatWeight d m) (coefficients F G H J)

/-- The actual original four-input flat generator. -/
abbrev generator (X : ((I × I) × I) × I) :
    objects d F G H J m X ⟶ point d F G H J m :=
  Enriched.weightedCoend.ι (flatWeight d m) (coefficients F G H J) X

/-- The chosen flat coend's original generators determine every outgoing arrow. -/
theorem flat_hom_ext {Z : V} {f g : point d F G H J m ⟶ Z}
    (h : ∀ X, generator d F G H J m X ≫ f = generator d F G H J m X ≫ g) :
    f = g :=
  Enriched.weightedCoend.hom_ext (flatWeight d m) (coefficients F G H J) h

end Flat

section ChosenDayPairs

variable
  [∀ (A B : EnrichedFunctor V I V) (k : I),
    HasCoproduct (EnrichedDayKernel.objects d.tensorEnrichedFunctor A B k)]
  [∀ (A B : EnrichedFunctor V I V) (k : I),
    HasCoproduct (EnrichedDayKernel.relations d.tensorEnrichedFunctor A B k)]
  [∀ (A B : EnrichedFunctor V I V) (k : I),
    HasCoequalizer (EnrichedDayKernel.leftMap d.tensorEnrichedFunctor A B k)
      (EnrichedDayKernel.rightMap d.tensorEnrichedFunctor A B k)]

/-- The original left-nested three-input output functor. -/
abbrev leftTripleFunctor : EnrichedFunctor V I V :=
  Output.functor d.tensorEnrichedFunctor (Output.functor d.tensorEnrichedFunctor F G) H

/-- Insert the actual first-pair and third-input identity generators. -/
abbrev tripleUnitGenerator (X : (I × I) × I) :
    (F.obj X.1.1 ⊗ G.obj X.1.2) ⊗ H.obj X.2 ⟶
      (leftTripleFunctor d F G H).obj ((X.1.1 ⊗ X.1.2) ⊗ X.2) :=
  (AssociatorUnit.unitGenerator d.tensorEnrichedFunctor F G X.1 ⊗ₘ 𝟙 (H.obj X.2)) ≫
    AssociatorUnit.unitGenerator d.tensorEnrichedFunctor
      (Output.functor d.tensorEnrichedFunctor F G) H (X.1.1 ⊗ X.1.2, X.2)

/-- The original four-input generator of the actual fully left-nested Day value. -/
abbrev nestedGenerator (m : I) (X : ((I × I) × I) × I) :
    objects d F G H J m X ⟶
      EnrichedDayKernel.obj d.tensorEnrichedFunctor (leftTripleFunctor d F G H) J m :=
  (𝟙 ((flatIndex d).obj X ⟶[V] m) ⊗ₘ
    (tripleUnitGenerator d F G H X.1 ⊗ₘ 𝟙 (J.obj X.2))) ≫
      EnrichedDayKernel.gen d.tensorEnrichedFunctor (leftTripleFunctor d F G H) J m
        ((X.1.1.1 ⊗ X.1.1.2) ⊗ X.1.2, X.2)

section FixedTriple

variable
  [∀ k : I, HasCoproduct (AssociatorFlat.leftObjects d F G H k)]
  [∀ k : I, HasCoproduct (AssociatorFlat.leftRelations d F G H k)]
  [∀ k : I, HasCoequalizer (AssociatorFlat.leftMap0 d F G H k)
    (AssociatorFlat.leftMap1 d F G H k)]

/-- The actual selected flat triple output functor, with its full enriched Hom maps. -/
abbrev tripleFlatFunctor : EnrichedFunctor V I V :=
  Output.functor (AssociatorIndex.leftIndex d) (F.externalTensor G) H


section GroupedComparison

variable (m : I)
  [HasCoproduct (objects d F G H J m)]
  [HasCoproduct (relations d F G H J m)]
  [HasCoequalizer (map0 d F G H J m) (map1 d F G H J m)]
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

/-- The original heterogeneous LEFT Iso for the first three raw indices and fourth input. -/
def groupedIso : point d F G H J m ≅
    EnrichedDayKernel.obj d.tensorEnrichedFunctor (tripleFlatFunctor d F G H) J m :=
  AssociatorLeftGeneral.iso (AssociatorIndex.leftIndex d) d.tensorEnrichedFunctor
    (F.externalTensor G) H J m

/-- Its original forward map inserts the actual triple-flat identity generator. -/
@[reassoc]
theorem generator_groupedIso_hom (X : ((I × I) × I) × I) :
    generator d F G H J m X ≫ (groupedIso d F G H J m).hom =
      (𝟙 ((flatIndex d).obj X ⟶[V] m) ⊗ₘ
        (AssociatorUnit.unitGenerator (AssociatorIndex.leftIndex d) (F.externalTensor G) H X.1 ⊗ₘ
          𝟙 (J.obj X.2))) ≫
        EnrichedDayKernel.gen d.tensorEnrichedFunctor (tripleFlatFunctor d F G H) J m
          ((X.1.1.1 ⊗ X.1.1.2) ⊗ X.1.2, X.2) :=
  AssociatorLeftGeneral.generator_iso_hom (AssociatorIndex.leftIndex d) d.tensorEnrichedFunctor
    (F.externalTensor G) H J m X

/-- Its actual inverse retains every original raw nested Hom and contraction leg. -/
@[reassoc]
theorem nestedGenerator_groupedIso_inv (p : I × I) (a : (I × I) × I) :
    AssociatorFaces.Left.nestedGenerator (AssociatorIndex.leftIndex d) d.tensorEnrichedFunctor
        (F.externalTensor G) H J m p a ≫ (groupedIso d F G H J m).inv =
      AssociatorLeftGeneral.contractWord (AssociatorIndex.leftIndex d) d.tensorEnrichedFunctor
          (F.externalTensor G) H J m p a ≫ generator d F G H J m (a, p.2) :=
  AssociatorLeftGeneral.nestedGenerator_iso_inv (AssociatorIndex.leftIndex d)
    d.tensorEnrichedFunctor (F.externalTensor G) H J m p a

end GroupedComparison

variable
  [∀ k : I, HasCoproduct (AssociatorPresentation.Left.simultaneousObjects
    d.tensorEnrichedFunctor d.tensorEnrichedFunctor F G H k)]
  [∀ k : I, HasCoproduct (AssociatorPresentation.Left.simultaneousRelations
    d.tensorEnrichedFunctor d.tensorEnrichedFunctor F G H k)]
  [∀ k : I, HasCoequalizer
    (AssociatorPresentation.Left.simultaneousLeftMap
      d.tensorEnrichedFunctor d.tensorEnrichedFunctor F G H k)
    (AssociatorPresentation.Left.simultaneousRightMap
      d.tensorEnrichedFunctor d.tensorEnrichedFunctor F G H k)]
  [∀ (k : I) (p : I × I), HasCoproduct
    (AssociatorFaces.Left.objects d.tensorEnrichedFunctor d.tensorEnrichedFunctor F G H k p)]
  [∀ (k : I) (p : I × I), HasCoproduct
    (AssociatorFaces.Left.innerRelations d.tensorEnrichedFunctor d.tensorEnrichedFunctor F G H k p)]
  [∀ (k : I) (p : I × I), HasCoequalizer
    (AssociatorFaces.Left.innerLeftMap d.tensorEnrichedFunctor d.tensorEnrichedFunctor F G H k p)
    (AssociatorFaces.Left.innerRightMap d.tensorEnrichedFunctor d.tensorEnrichedFunctor F G H k p)]
  [∀ (k : I) (pq : (I × I) × (I × I)), HasCoproduct
    (AssociatorPresentation.Left.relationObjects
      d.tensorEnrichedFunctor d.tensorEnrichedFunctor F G H k pq)]
  [∀ (k : I) (pq : (I × I) × (I × I)), HasCoproduct
    (AssociatorPresentation.Left.relationRelations
      d.tensorEnrichedFunctor d.tensorEnrichedFunctor F G H k pq)]
  [∀ (k : I) (pq : (I × I) × (I × I)), HasCoequalizer
    (AssociatorPresentation.Left.relationLeftMap
      d.tensorEnrichedFunctor d.tensorEnrichedFunctor F G H k pq)
    (AssociatorPresentation.Left.relationRightMap
      d.tensorEnrichedFunctor d.tensorEnrichedFunctor F G H k pq)]
  [∀ k : I, HasCoproduct (AssociatorPresentation.Left.innerObjects
    d.tensorEnrichedFunctor d.tensorEnrichedFunctor F G H k)]
  [∀ k : I, HasCoproduct (AssociatorPresentation.Left.outerRelations
    d.tensorEnrichedFunctor d.tensorEnrichedFunctor F G H k)]
  [∀ k : I, HasCoequalizer
    (AssociatorPresentation.Left.outerLeftMap
      d.tensorEnrichedFunctor d.tensorEnrichedFunctor F G H k)
    (AssociatorPresentation.Left.outerRightMap
      d.tensorEnrichedFunctor d.tensorEnrichedFunctor F G H k)]

/-- The actual fixed F/G/H left comparison and its proved full output-Hom naturality. -/
def tripleFunctorIso :
    (⟨tripleFlatFunctor d F G H⟩ : EnrichedFunctorCat V I) ≅
      ⟨leftTripleFunctor d F G H⟩ :=
  EnrichedFunctorCat.isoOfComponents _ _ (fun k => AssociatorFlattening.iso d F G H k)
    (AssociatorNaturality.left_output_natural d F G H)

/-- Its forward component is the original actual flat-to-nested map. -/
@[simp]
theorem tripleFunctorIso_hom_component (k : I) :
    EnrichedFunctorCat.component (tripleFunctorIso d F G H).hom k =
      AssociatorFlattening.flatToNested d F G H k := by
  exact EnrichedFunctorCat.isoOfComponents_hom_component
    (⟨tripleFlatFunctor d F G H⟩ : EnrichedFunctorCat V I)
    (⟨leftTripleFunctor d F G H⟩ : EnrichedFunctorCat V I)
    (fun k => AssociatorFlattening.iso d F G H k)
    (AssociatorNaturality.left_output_natural d F G H) k

/-- Its inverse component is the original actual nested-to-flat map. -/
@[simp]
theorem tripleFunctorIso_inv_component (k : I) :
    EnrichedFunctorCat.component (tripleFunctorIso d F G H).inv k =
      AssociatorFlattening.nestedToFlat d F G H k := by
  exact EnrichedFunctorCat.isoOfComponents_inv_component
    (⟨tripleFlatFunctor d F G H⟩ : EnrichedFunctorCat V I)
    (⟨leftTripleFunctor d F G H⟩ : EnrichedFunctorCat V I)
    (fun k => AssociatorFlattening.iso d F G H k)
    (AssociatorNaturality.left_output_natural d F G H) k

/-- The triple comparison keeps the two original nested identity-generator legs. -/
@[reassoc]
theorem unitGenerator_tripleFunctorIso_hom (X : (I × I) × I) :
    AssociatorUnit.unitGenerator (AssociatorIndex.leftIndex d) (F.externalTensor G) H X ≫
        EnrichedFunctorCat.component (tripleFunctorIso d F G H).hom
          ((X.1.1 ⊗ X.1.2) ⊗ X.2) =
      tripleUnitGenerator d F G H X := by
  rw [tripleFunctorIso_hom_component]
  let x := (X.1.1 ⊗ X.1.2) ⊗ X.2
  let Q := (F.obj X.1.1 ⊗ G.obj X.1.2) ⊗ H.obj X.2
  let Q' := (Output.functor d.tensorEnrichedFunctor F G).obj (X.1.1 ⊗ X.1.2) ⊗ H.obj X.2
  let u : Q ⟶ Q' :=
    AssociatorUnit.unitGenerator d.tensorEnrichedFunctor F G X.1 ⊗ₘ 𝟙 (H.obj X.2)
  let g : (x ⟶[V] x) ⊗ Q' ⟶ (leftTripleFunctor d F G H).obj x :=
    EnrichedDayKernel.gen d.tensorEnrichedFunctor
      (Output.functor d.tensorEnrichedFunctor F G) H x (X.1.1 ⊗ X.1.2, X.2)
  let i : Q ⟶ AssociatorFlat.leftObjects d F G H x X := AssociatorUnit.identityInsert x Q
  let g₀ := AssociatorFlat.leftGenerator d F G H x X
  let f := AssociatorFlattening.flatToNested d F G H x
  let w : AssociatorFlat.leftObjects d F G H x X ⟶ (x ⟶[V] x) ⊗ Q' :=
    𝟙 (x ⟶[V] x) ⊗ₘ u
  have hf : g₀ ≫ f = w ≫ g := AssociatorFlattening.leftGenerator_flatToNested d F G H x X
  have hi : i ≫ w = u ≫ AssociatorUnit.identityInsert x Q' := by
    have ht := congrArg (fun f => AssociatorUnit.identityInsert x Q ≫ f)
      (id_tensorHom (x ⟶[V] x) u)
    exact ht.trans (AssociatorUnit.identityInsert_naturality x u)
  change (i ≫ g₀) ≫ f = u ≫ (AssociatorUnit.identityInsert x Q' ≫ g)
  calc
    _ = i ≫ (g₀ ≫ f) := Category.assoc i g₀ f
    _ = i ≫ (w ≫ g) := congrArg (fun z => i ≫ z) hf
    _ = (i ≫ w) ≫ g := (Category.assoc i w g).symm
    _ = (u ≫ AssociatorUnit.identityInsert x Q') ≫ g := congrArg (fun z => z ≫ g) hi
    _ = _ := Category.assoc u (AssociatorUnit.identityInsert x Q') g

/-- Apply the unchanged chosen Day bifunctor to the actual triple Iso and fourth identity. -/
def outerFunctorIso :
    (Input.bifunctor d.tensorEnrichedFunctor).obj
      ((⟨tripleFlatFunctor d F G H⟩ : EnrichedFunctorCat V I),
        (⟨J⟩ : EnrichedFunctorCat V I)) ≅
    (Input.bifunctor d.tensorEnrichedFunctor).obj
      ((⟨leftTripleFunctor d F G H⟩ : EnrichedFunctorCat V I),
        (⟨J⟩ : EnrichedFunctorCat V I)) :=
  (Input.bifunctor d.tensorEnrichedFunctor).mapIso
    ((tripleFunctorIso d F G H).prod (Iso.refl (⟨J⟩ : EnrichedFunctorCat V I)))

/-- The forward outer component is the actual original chosen coend input map. -/
theorem outerFunctorIso_hom_component (m : I) :
    EnrichedFunctorCat.component (outerFunctorIso d F G H J).hom m =
      Input.mapAt d.tensorEnrichedFunctor (tripleFunctorIso d F G H).hom
        (GradedNatTrans.unitId J) m := by
  exact Input.bifunctor_map_component d.tensorEnrichedFunctor
    (tripleFunctorIso d F G H).hom (𝟙 (⟨J⟩ : EnrichedFunctorCat V I)) m

/-- The inverse outer component uses the original inverse triple map. -/
theorem outerFunctorIso_inv_component (m : I) :
    EnrichedFunctorCat.component (outerFunctorIso d F G H J).inv m =
      Input.mapAt d.tensorEnrichedFunctor (tripleFunctorIso d F G H).inv
        (GradedNatTrans.unitId J) m := by
  exact Input.bifunctor_map_component d.tensorEnrichedFunctor
    (tripleFunctorIso d F G H).inv (𝟙 (⟨J⟩ : EnrichedFunctorCat V I)) m

/-- The two actual outer maps give the corresponding Iso of selected output values. -/
def outerIso (m : I) :
    EnrichedDayKernel.obj d.tensorEnrichedFunctor (tripleFlatFunctor d F G H) J m ≅
      EnrichedDayKernel.obj d.tensorEnrichedFunctor (leftTripleFunctor d F G H) J m where
  hom := EnrichedFunctorCat.component (outerFunctorIso d F G H J).hom m
  inv := EnrichedFunctorCat.component (outerFunctorIso d F G H J).inv m
  hom_inv_id := by
    have h := congrArg (fun f => EnrichedFunctorCat.component f m)
      (outerFunctorIso d F G H J).hom_inv_id
    simpa only [EnrichedFunctorCat.component_comp, EnrichedFunctorCat.component_id] using h
  inv_hom_id := by
    have h := congrArg (fun f => EnrichedFunctorCat.component f m)
      (outerFunctorIso d F G H J).inv_hom_id
    simpa only [EnrichedFunctorCat.component_comp, EnrichedFunctorCat.component_id] using h


/-- The actual forward value map is the same chosen Day input map. -/
@[simp]
theorem outerIso_hom (m : I) :
    (outerIso d F G H J m).hom =
      Input.mapAt d.tensorEnrichedFunctor (tripleFunctorIso d F G H).hom
        (GradedNatTrans.unitId J) m :=
  outerFunctorIso_hom_component d F G H J m

/-- The actual inverse value map is the original inverse Day input map. -/
@[simp]
theorem outerIso_inv (m : I) :
    (outerIso d F G H J m).inv =
      Input.mapAt d.tensorEnrichedFunctor (tripleFunctorIso d F G H).inv
        (GradedNatTrans.unitId J) m :=
  outerFunctorIso_inv_component d F G H J m


/-- The actual outer input map retains its original weight and coefficient components. -/
@[reassoc]
theorem outer_generator_hom (m : I) (p : I × I) :
    EnrichedDayKernel.gen d.tensorEnrichedFunctor (tripleFlatFunctor d F G H) J m p ≫
        (outerIso d F G H J m).hom =
      (𝟙 ((weight d.tensorEnrichedFunctor m).obj (op p)) ⊗ₘ
        (EnrichedFunctorCat.component (tripleFunctorIso d F G H).hom p.1 ⊗ₘ
          𝟙 (J.obj p.2))) ≫
        EnrichedDayKernel.gen d.tensorEnrichedFunctor (leftTripleFunctor d F G H) J m p := by
  have h := Input.gen_mapAt d.tensorEnrichedFunctor
    (tripleFunctorIso d F G H).hom (GradedNatTrans.unitId J) m p
  rw [outerIso_hom]
  simpa only [EnrichedFunctorCat.component, EnrichedDayKernel.weight_obj,
    GradedNatTrans.unitId_component] using h

section Comparison

variable (m : I)
  [HasCoproduct (objects d F G H J m)]
  [HasCoproduct (relations d F G H J m)]
  [HasCoequalizer (map0 d F G H J m) (map1 d F G H J m)]
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

/-- The actual flat-four to fully left-nested-four Iso, with both genuine inverse maps. -/
def iso : point d F G H J m ≅
    EnrichedDayKernel.obj d.tensorEnrichedFunctor (leftTripleFunctor d F G H) J m :=
  groupedIso d F G H J m ≪≫ outerIso d F G H J m

/-- The complete forward map is original grouped descent followed by the actual Day input map. -/
theorem iso_hom : (iso d F G H J m).hom =
    AssociatorLeftGeneral.flatToNested (AssociatorIndex.leftIndex d) d.tensorEnrichedFunctor
        (F.externalTensor G) H J m ≫
      Input.mapAt d.tensorEnrichedFunctor (tripleFunctorIso d F G H).hom
        (GradedNatTrans.unitId J) m := by
  change AssociatorLeftGeneral.flatToNested (AssociatorIndex.leftIndex d) d.tensorEnrichedFunctor
      (F.externalTensor G) H J m ≫ (outerIso d F G H J m).hom = _
  exact congrArg (fun f => AssociatorLeftGeneral.flatToNested
    (AssociatorIndex.leftIndex d) d.tensorEnrichedFunctor (F.externalTensor G) H J m ≫ f)
      (outerIso_hom d F G H J m)

/-- The inverse uses the original inverse triple input map and actual grouped contraction. -/
theorem iso_inv : (iso d F G H J m).inv =
    Input.mapAt d.tensorEnrichedFunctor (tripleFunctorIso d F G H).inv
        (GradedNatTrans.unitId J) m ≫
      AssociatorLeftGeneral.nestedToFlat (AssociatorIndex.leftIndex d) d.tensorEnrichedFunctor
        (F.externalTensor G) H J m := by
  change (outerIso d F G H J m).inv ≫ AssociatorLeftGeneral.nestedToFlat
      (AssociatorIndex.leftIndex d) d.tensorEnrichedFunctor (F.externalTensor G) H J m = _
  exact congrArg (fun f => f ≫ AssociatorLeftGeneral.nestedToFlat
    (AssociatorIndex.leftIndex d) d.tensorEnrichedFunctor (F.externalTensor G) H J m)
      (outerIso_inv d F G H J m)

/-- Every original four-input flat generator keeps the full weight and all original nested legs. -/
@[reassoc]
theorem generator_iso_hom (X : ((I × I) × I) × I) :
    generator d F G H J m X ≫ (iso d F G H J m).hom =
      nestedGenerator d F G H J m X := by
  let p : I × I := ((X.1.1.1 ⊗ X.1.1.2) ⊗ X.1.2, X.2)
  let W := (flatIndex d).obj X ⟶[V] m
  let A := (F.obj X.1.1.1 ⊗ G.obj X.1.1.2) ⊗ H.obj X.1.2
  let u : A ⟶ (tripleFlatFunctor d F G H).obj p.1 :=
    AssociatorUnit.unitGenerator (AssociatorIndex.leftIndex d) (F.externalTensor G) H X.1
  let s : (tripleFlatFunctor d F G H).obj p.1 ⟶ (leftTripleFunctor d F G H).obj p.1 :=
    EnrichedFunctorCat.component (tripleFunctorIso d F G H).hom p.1
  let v : A ⟶ (leftTripleFunctor d F G H).obj p.1 := tripleUnitGenerator d F G H X.1
  let g₀ := EnrichedDayKernel.gen d.tensorEnrichedFunctor (tripleFlatFunctor d F G H) J m p
  let g₁ := EnrichedDayKernel.gen d.tensorEnrichedFunctor (leftTripleFunctor d F G H) J m p
  let w₀ : objects d F G H J m X ⟶
      EnrichedDayKernel.objects d.tensorEnrichedFunctor (tripleFlatFunctor d F G H) J m p :=
    𝟙 W ⊗ₘ (u ⊗ₘ 𝟙 (J.obj p.2))
  let w₁ : EnrichedDayKernel.objects d.tensorEnrichedFunctor (tripleFlatFunctor d F G H) J m p ⟶
      EnrichedDayKernel.objects d.tensorEnrichedFunctor (leftTripleFunctor d F G H) J m p :=
    𝟙 W ⊗ₘ (s ⊗ₘ 𝟙 (J.obj p.2))
  let w₂ : objects d F G H J m X ⟶
      EnrichedDayKernel.objects d.tensorEnrichedFunctor (leftTripleFunctor d F G H) J m p :=
    𝟙 W ⊗ₘ (v ⊗ₘ 𝟙 (J.obj p.2))
  have h₀ : generator d F G H J m X ≫ (groupedIso d F G H J m).hom = w₀ ≫ g₀ :=
    generator_groupedIso_hom d F G H J m X
  have h₁ : g₀ ≫ (outerIso d F G H J m).hom = w₁ ≫ g₁ :=
    outer_generator_hom d F G H J m p
  have hu : u ≫ s = v := unitGenerator_tripleFunctorIso_hom d F G H X.1
  have hw : w₀ ≫ w₁ = w₂ := by
    change (𝟙 W ⊗ₘ (u ⊗ₘ 𝟙 (J.obj p.2))) ≫
      (𝟙 W ⊗ₘ (s ⊗ₘ 𝟙 (J.obj p.2))) = 𝟙 W ⊗ₘ (v ⊗ₘ 𝟙 (J.obj p.2))
    simp only [tensorHom_comp_tensorHom, Category.id_comp, hu]
  change generator d F G H J m X ≫
    ((groupedIso d F G H J m).hom ≫ (outerIso d F G H J m).hom) = w₂ ≫ g₁
  calc
    _ = (generator d F G H J m X ≫ (groupedIso d F G H J m).hom) ≫
        (outerIso d F G H J m).hom := (Category.assoc _ _ _).symm
    _ = (w₀ ≫ g₀) ≫ (outerIso d F G H J m).hom :=
      congrArg (fun f => f ≫ (outerIso d F G H J m).hom) h₀
    _ = w₀ ≫ (g₀ ≫ (outerIso d F G H J m).hom) := Category.assoc _ _ _
    _ = w₀ ≫ (w₁ ≫ g₁) := congrArg (fun f => w₀ ≫ f) h₁
    _ = (w₀ ≫ w₁) ≫ g₁ := (Category.assoc _ _ _).symm
    _ = _ := congrArg (fun f => f ≫ g₁) hw

/-- The genuine inverse returns every original fully-left four-input generator. -/
@[reassoc]
theorem nestedGenerator_iso_inv (X : ((I × I) × I) × I) :
    nestedGenerator d F G H J m X ≫ (iso d F G H J m).inv =
      generator d F G H J m X := by
  have h := congrArg (fun f => f ≫ (iso d F G H J m).inv)
    (generator_iso_hom d F G H J m X)
  simpa only [Category.assoc, Iso.hom_inv_id, Category.comp_id] using h.symm

/-- The original four-input generator family is dense in the actual fully left-nested value. -/
theorem hom_ext {Z : V}
    {f g : EnrichedDayKernel.obj d.tensorEnrichedFunctor (leftTripleFunctor d F G H) J m ⟶ Z}
    (h : ∀ X, nestedGenerator d F G H J m X ≫ f = nestedGenerator d F G H J m X ≫ g) :
    f = g := by
  apply (cancel_epi (iso d F G H J m).hom).1
  apply flat_hom_ext d F G H J m
  intro X
  simpa only [← Category.assoc, generator_iso_hom] using h X

/-- Equality is precisely equality on all original four-input nested generators. -/
theorem hom_ext_iff {Z : V}
    (f g : EnrichedDayKernel.obj d.tensorEnrichedFunctor (leftTripleFunctor d F G H) J m ⟶ Z) :
    f = g ↔ ∀ X, nestedGenerator d F G H J m X ≫ f = nestedGenerator d F G H J m X ≫ g := by
  constructor
  · intro h X
    rw [h]
  · exact hom_ext d F G H J m

end Comparison

end FixedTriple
end ChosenDayPairs
end CategoryTheory.EnrichedDayKernel.AssociatorQuadLeft
