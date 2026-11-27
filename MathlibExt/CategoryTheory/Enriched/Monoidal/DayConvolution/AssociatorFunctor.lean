/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua
module

public import MathlibExt.CategoryTheory.Enriched.Monoidal.DayConvolution.AssociatorComparison
public import MathlibExt.CategoryTheory.Enriched.Monoidal.DayConvolution.AssociatorComponents
public import MathlibExt.CategoryTheory.Enriched.FunctorCategoryIso
public import Mathlib.CategoryTheory.Products.Associator

/-!
# Associator Functor

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

/-- The unchanged genuine left-nested output functor. -/
abbrev leftFunctor (F G H : EnrichedFunctor V I V) : EnrichedFunctor V I V :=
  Output.functor d.tensorEnrichedFunctor (Output.functor d.tensorEnrichedFunctor F G) H
/-- The unchanged genuine right-nested output functor. -/
abbrev rightFunctor (F G H : EnrichedFunctor V I V) : EnrichedFunctor V I V :=
  Output.functor d.tensorEnrichedFunctor F (Output.functor d.tensorEnrichedFunctor G H)
/-- The original selected left flat output functor. -/
abbrev leftFlatFunctor (F G H : EnrichedFunctor V I V) : EnrichedFunctor V I V :=
  Output.functor (AssociatorIndex.leftIndex d) (F.externalTensor G) H

omit
  [∀ (F G : EnrichedFunctor V I V) (k : I), HasCoproduct (EnrichedDayKernel.objects
    d.tensorEnrichedFunctor F G k)]
  [∀ (F G : EnrichedFunctor V I V) (k : I), HasCoproduct (EnrichedDayKernel.relations
    d.tensorEnrichedFunctor F G k)]
  [∀ (F G : EnrichedFunctor V I V) (k : I), HasCoequalizer (EnrichedDayKernel.leftMap
    d.tensorEnrichedFunctor F G k)
    (EnrichedDayKernel.rightMap d.tensorEnrichedFunctor F G k)]
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
      F m)] in
/-- The full original flat associator is natural on the entire output Hom. -/
theorem flat_output_natural (F G H : EnrichedFunctor V I V) (m n : I) :
    MonoidalClosed.uncurry ((leftFlatFunctor d F G H).map m n) ≫ (AssociatorFlat.iso d F G H n).hom
      =
    ((AssociatorFlat.iso d F G H m).hom ⊗ₘ 𝟙 (m ⟶[V] n)) ≫
      MonoidalClosed.uncurry ((AssociatorNaturality.rightOutputFunctor d F G H).map m n) := by
  let P := AssociatorFlat.leftPoint d F G H m
  let Q := AssociatorFlat.rightPoint d F G H m
  let P' := AssociatorFlat.leftPoint d F G H n
  let Q' := AssociatorFlat.rightPoint d F G H n
  let R : V := m ⟶[V] n
  let l : P ⊗ R ⟶ P' := MonoidalClosed.uncurry ((leftFlatFunctor d F G H).map m n)
  let r : Q ⊗ R ⟶ Q' := MonoidalClosed.uncurry ((AssociatorNaturality.rightOutputFunctor d F G
    H).map m n)
  let a : P ⟶ Q := (AssociatorFlat.iso d F G H m).hom
  let ai : Q ⟶ P := (AssociatorFlat.iso d F G H m).inv
  let b : P' ⟶ Q' := (AssociatorFlat.iso d F G H n).hom
  have h := AssociatorNaturality.uncurry_ofIsoComponents (leftFlatFunctor d F G H)
    (fun m => AssociatorFlat.rightPoint d F G H m) (fun m => AssociatorFlat.iso d F G H m) m n
  change r = (ai ⊗ₘ 𝟙 R) ≫ l ≫ b at h
  have hi : a ≫ ai = 𝟙 P := (AssociatorFlat.iso d F G H m).hom_inv_id
  have ht : (a ⊗ₘ 𝟙 R) ≫ (ai ⊗ₘ 𝟙 R) = 𝟙 (P ⊗ R) := by
    rw [tensorHom_comp_tensorHom, hi, Category.comp_id, id_tensorHom_id]
  have h0 := congrArg (fun z => (a ⊗ₘ 𝟙 R) ≫ z) h
  have h1 := congrArg (fun z => z ≫ l ≫ b) ht
  simp only [Category.assoc, Category.id_comp] at h0 h1
  change l ≫ b = (a ⊗ₘ 𝟙 R) ≫ r
  exact (h0.trans h1).symm

/-- The actual left flat/nested comparison is an isomorphism of genuine enriched functors. -/
def leftFunctorIso (F G H : EnrichedFunctor V I V) :
    (⟨leftFlatFunctor d F G H⟩ : EnrichedFunctorCat V I) ≅ ⟨leftFunctor d F G H⟩ :=
  EnrichedFunctorCat.isoOfComponents _ _ (fun m => AssociatorFlattening.iso d F G H m)
    (AssociatorNaturality.left_output_natural d F G H)

/-- The original flat associator, including its actual right output action, is a genuine functor
  isomorphism. -/
def flatFunctorIso (F G H : EnrichedFunctor V I V) :
    (⟨leftFlatFunctor d F G H⟩ : EnrichedFunctorCat V I) ≅ ⟨AssociatorNaturality.rightOutputFunctor
      d F G H⟩ :=
  EnrichedFunctorCat.isoOfComponents _ _ (fun m => AssociatorFlat.iso d F G H m)
    (flat_output_natural d F G H)

/-- The original right comparison is an isomorphism of genuine enriched output functors. -/
def rightFunctorIso (F G H : EnrichedFunctor V I V) :
    (⟨AssociatorNaturality.rightOutputFunctor d F G H⟩ : EnrichedFunctorCat V I) ≅ ⟨rightFunctor d F
      G H⟩ :=
  EnrichedFunctorCat.isoOfComponents _ _ (fun m => AssociatorRightFlattening.iso d F G H m)
    (AssociatorNaturality.right_output_natural d F G H)

omit
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
      F m)] in
/-- The hom keeps the original leftFunctorIso component. -/
@[simp]
theorem leftFunctorIso_hom_component (F G H : EnrichedFunctor V I V) (m : I) :
    EnrichedFunctorCat.component (leftFunctorIso d F G H).hom m = (AssociatorFlattening.iso d F G H
      m).hom :=
  EnrichedFunctorCat.isoOfComponents_hom_component
    (⟨leftFlatFunctor d F G H⟩ : EnrichedFunctorCat V I) ⟨leftFunctor d F G H⟩ (fun m =>
      AssociatorFlattening.iso d F G H m)
    (AssociatorNaturality.left_output_natural d F G H) m

omit
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
      F m)] in
/-- The inv keeps the original leftFunctorIso component. -/
@[simp]
theorem leftFunctorIso_inv_component (F G H : EnrichedFunctor V I V) (m : I) :
    EnrichedFunctorCat.component (leftFunctorIso d F G H).inv m = (AssociatorFlattening.iso d F G H
      m).inv :=
  EnrichedFunctorCat.isoOfComponents_inv_component
    (⟨leftFlatFunctor d F G H⟩ : EnrichedFunctorCat V I) ⟨leftFunctor d F G H⟩ (fun m =>
      AssociatorFlattening.iso d F G H m)
    (AssociatorNaturality.left_output_natural d F G H) m

omit
  [∀ (F G : EnrichedFunctor V I V) (k : I), HasCoproduct (EnrichedDayKernel.objects
    d.tensorEnrichedFunctor F G k)]
  [∀ (F G : EnrichedFunctor V I V) (k : I), HasCoproduct (EnrichedDayKernel.relations
    d.tensorEnrichedFunctor F G k)]
  [∀ (F G : EnrichedFunctor V I V) (k : I), HasCoequalizer (EnrichedDayKernel.leftMap
    d.tensorEnrichedFunctor F G k)
    (EnrichedDayKernel.rightMap d.tensorEnrichedFunctor F G k)]
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
      F m)] in
/-- The hom keeps the original flatFunctorIso component. -/
@[simp]
theorem flatFunctorIso_hom_component (F G H : EnrichedFunctor V I V) (m : I) :
    EnrichedFunctorCat.component (flatFunctorIso d F G H).hom m = (AssociatorFlat.iso d F G H m).hom
      :=
  EnrichedFunctorCat.isoOfComponents_hom_component
    (⟨leftFlatFunctor d F G H⟩ : EnrichedFunctorCat V I) ⟨AssociatorNaturality.rightOutputFunctor d
      F G H⟩ (fun m => AssociatorFlat.iso d F G H m)
    (flat_output_natural d F G H) m

omit
  [∀ (F G : EnrichedFunctor V I V) (k : I), HasCoproduct (EnrichedDayKernel.objects
    d.tensorEnrichedFunctor F G k)]
  [∀ (F G : EnrichedFunctor V I V) (k : I), HasCoproduct (EnrichedDayKernel.relations
    d.tensorEnrichedFunctor F G k)]
  [∀ (F G : EnrichedFunctor V I V) (k : I), HasCoequalizer (EnrichedDayKernel.leftMap
    d.tensorEnrichedFunctor F G k)
    (EnrichedDayKernel.rightMap d.tensorEnrichedFunctor F G k)]
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
      F m)] in
/-- The inv keeps the original flatFunctorIso component. -/
@[simp]
theorem flatFunctorIso_inv_component (F G H : EnrichedFunctor V I V) (m : I) :
    EnrichedFunctorCat.component (flatFunctorIso d F G H).inv m = (AssociatorFlat.iso d F G H m).inv
      :=
  EnrichedFunctorCat.isoOfComponents_inv_component
    (⟨leftFlatFunctor d F G H⟩ : EnrichedFunctorCat V I) ⟨AssociatorNaturality.rightOutputFunctor d
      F G H⟩ (fun m => AssociatorFlat.iso d F G H m)
    (flat_output_natural d F G H) m

omit
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
      m)] in
/-- The hom keeps the original rightFunctorIso component. -/
@[simp]
theorem rightFunctorIso_hom_component (F G H : EnrichedFunctor V I V) (m : I) :
    EnrichedFunctorCat.component (rightFunctorIso d F G H).hom m = (AssociatorRightFlattening.iso d
      F G H m).hom :=
  EnrichedFunctorCat.isoOfComponents_hom_component
    (⟨AssociatorNaturality.rightOutputFunctor d F G H⟩ : EnrichedFunctorCat V I) ⟨rightFunctor d F G
      H⟩ (fun m => AssociatorRightFlattening.iso d F G H m)
    (AssociatorNaturality.right_output_natural d F G H) m

omit
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
      m)] in
/-- The inv keeps the original rightFunctorIso component. -/
@[simp]
theorem rightFunctorIso_inv_component (F G H : EnrichedFunctor V I V) (m : I) :
    EnrichedFunctorCat.component (rightFunctorIso d F G H).inv m = (AssociatorRightFlattening.iso d
      F G H m).inv :=
  EnrichedFunctorCat.isoOfComponents_inv_component
    (⟨AssociatorNaturality.rightOutputFunctor d F G H⟩ : EnrichedFunctorCat V I) ⟨rightFunctor d F G
      H⟩ (fun m => AssociatorRightFlattening.iso d F G H m)
    (AssociatorNaturality.right_output_natural d F G H) m

/-- The genuine Day associator on the ORIGINAL chosen nested functors. -/
def functorIso (F G H : EnrichedFunctor V I V) :
    (⟨leftFunctor d F G H⟩ : EnrichedFunctorCat V I) ≅ ⟨rightFunctor d F G H⟩ :=
  (leftFunctorIso d F G H).symm ≪≫ flatFunctorIso d F G H ≪≫ rightFunctorIso d F G H

/-- The associator component is exactly the already constructed original nested-value isomorphism.
-/
@[simp]
theorem functorIso_hom_component (F G H : EnrichedFunctor V I V) (m : I) :
    EnrichedFunctorCat.component (functorIso d F G H).hom m = (componentIso d F G H m).hom := by
  simp only [functorIso, Iso.trans_hom, Iso.symm_hom, EnrichedFunctorCat.component_comp,
    leftFunctorIso_inv_component, flatFunctorIso_hom_component, rightFunctorIso_hom_component,
    componentIso_hom, AssociatorFlattening.iso, AssociatorRightFlattening.iso] ; rfl

/-- The genuine inverse retains exactly the opposite original nested-value maps. -/
@[simp]
theorem functorIso_inv_component (F G H : EnrichedFunctor V I V) (m : I) :
    EnrichedFunctorCat.component (functorIso d F G H).inv m = (componentIso d F G H m).inv := by
  simp only [functorIso, Iso.trans_inv, Iso.symm_inv, EnrichedFunctorCat.component_comp,
    rightFunctorIso_inv_component, flatFunctorIso_inv_component, leftFunctorIso_hom_component,
    componentIso_inv, AssociatorFlattening.iso, AssociatorRightFlattening.iso, Category.assoc]
  rfl

/-- Full output-index Hom naturality of the actual Day associator, without a separator. -/
theorem output_natural (F G H : EnrichedFunctor V I V) (m n : I) :
    MonoidalClosed.uncurry ((leftFunctor d F G H).map m n) ≫ (componentIso d F G H n).hom =
      ((componentIso d F G H m).hom ⊗ₘ 𝟙 (m ⟶[V] n)) ≫
        MonoidalClosed.uncurry ((rightFunctor d F G H).map m n) := by
  have h := GradedNatTrans.uncurriedNaturality (functorIso d F G H).hom m n
  simpa only [← functorIso_hom_component, EnrichedFunctorCat.component] using h

/-- The exact inverse is natural on the same complete output Hom. -/
theorem output_inverse_natural (F G H : EnrichedFunctor V I V) (m n : I) :
    MonoidalClosed.uncurry ((rightFunctor d F G H).map m n) ≫ (componentIso d F G H n).inv =
      ((componentIso d F G H m).inv ⊗ₘ 𝟙 (m ⟶[V] n)) ≫
        MonoidalClosed.uncurry ((leftFunctor d F G H).map m n) := by
  have h := GradedNatTrans.uncurriedNaturality (functorIso d F G H).inv m n
  simpa only [← functorIso_inv_component, EnrichedFunctorCat.component] using h


section Inputs
variable {F F' G G' H H' : EnrichedFunctor V I V}
  (a : GradedNatTrans ((Center.ofBraided V).obj (𝟙_ V)) F F')
  (b : GradedNatTrans ((Center.ofBraided V).obj (𝟙_ V)) G G')
  (c : GradedNatTrans ((Center.ofBraided V).obj (𝟙_ V)) H H') (m : I)

omit
  [∀ (F G : EnrichedFunctor V I V) (k : I), HasCoproduct (EnrichedDayKernel.objects
    d.tensorEnrichedFunctor F G k)]
  [∀ (F G : EnrichedFunctor V I V) (k : I), HasCoproduct (EnrichedDayKernel.relations
    d.tensorEnrichedFunctor F G k)]
  [∀ (F G : EnrichedFunctor V I V) (k : I), HasCoequalizer (EnrichedDayKernel.leftMap
    d.tensorEnrichedFunctor F G k)
    (EnrichedDayKernel.rightMap d.tensorEnrichedFunctor F G k)]
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
      F m)] in
/-- The actual flat associator is jointly natural in all three original input transformations. -/
theorem flat_input_natural :
    AssociatorNaturality.leftInputMap d a b c m ≫ (AssociatorFlat.iso d F' G' H' m).hom =
      (AssociatorFlat.iso d F G H m).hom ≫ AssociatorNaturality.rightInputMap d a b c m := by
  apply Enriched.weightedCoend.hom_ext (AssociatorIndex.leftWeight d m) (Associator.leftCoefficients
    F G H)
  intro X
  let DL := AssociatorFlat.leftObjects d F G H m X
  let DL' := AssociatorFlat.leftObjects d F' G' H' m X
  let DR := AssociatorFlat.rightObjects d F G H m X
  let DR' := AssociatorFlat.rightObjects d F' G' H' m X
  let WL := (AssociatorIndex.leftWeight d m).obj (op X)
  let WR := (AssociatorIndex.rightWeight d m).obj (op X)
  let x : F.obj X.1.1 ⟶ F'.obj X.1.1 := (eHomEquiv V).symm (a.app X.1.1)
  let y : G.obj X.1.2 ⟶ G'.obj X.1.2 := (eHomEquiv V).symm (b.app X.1.2)
  let z : H.obj X.2 ⟶ H'.obj X.2 := (eHomEquiv V).symm (c.app X.2)
  let w : WL ⟶ WR := eHomWhiskerRight V (α_ X.1.1 X.1.2 X.2).inv m
  let kl : DL ⟶ DL' := 𝟙 WL ⊗ₘ ((x ⊗ₘ y) ⊗ₘ z)
  let kr : DR ⟶ DR' := 𝟙 WR ⊗ₘ (x ⊗ₘ (y ⊗ₘ z))
  let v : DL ⟶ DR := w ⊗ₘ (α_ (F.obj X.1.1) (G.obj X.1.2) (H.obj X.2)).hom
  let v' : DL' ⟶ DR' := w ⊗ₘ (α_ (F'.obj X.1.1) (G'.obj X.1.2) (H'.obj X.2)).hom
  let P := AssociatorFlat.leftPoint d F G H m
  let P' := AssociatorFlat.leftPoint d F' G' H' m
  let Q := AssociatorFlat.rightPoint d F G H m
  let Q' := AssociatorFlat.rightPoint d F' G' H' m
  let li : P ⟶ P' := AssociatorNaturality.leftInputMap d a b c m
  let ri : Q ⟶ Q' := AssociatorNaturality.rightInputMap d a b c m
  let f : P ⟶ Q := (AssociatorFlat.iso d F G H m).hom
  let f' : P' ⟶ Q' := (AssociatorFlat.iso d F' G' H' m).hom
  let g0 : DL ⟶ P := AssociatorFlat.leftGenerator d F G H m X
  let g1 : DL' ⟶ P' := AssociatorFlat.leftGenerator d F' G' H' m X
  let h0 : DR ⟶ Q := AssociatorFlat.rightGenerator d F G H m X
  let h1 : DR' ⟶ Q' := AssociatorFlat.rightGenerator d F' G' H' m X
  have hl : g0 ≫ li = kl ≫ g1 := AssociatorNaturality.leftInputMap_generator d a b c m X
  have hr : h0 ≫ ri = kr ≫ h1 := AssociatorNaturality.rightInputMap_generator d a b c m X
  have hf : g0 ≫ f = v ≫ h0 := AssociatorFlat.leftGenerator_iso_hom d F G H m X
  have hf' : g1 ≫ f' = v' ≫ h1 := AssociatorFlat.leftGenerator_iso_hom d F' G' H' m X
  have hs : kl ≫ v' = v ≫ kr := by
    change (𝟙 WL ⊗ₘ ((x ⊗ₘ y) ⊗ₘ z)) ≫
        (w ⊗ₘ (α_ (F'.obj X.1.1) (G'.obj X.1.2) (H'.obj X.2)).hom) =
      (w ⊗ₘ (α_ (F.obj X.1.1) (G.obj X.1.2) (H.obj X.2)).hom) ≫
        (𝟙 WR ⊗ₘ (x ⊗ₘ (y ⊗ₘ z)))
    rw [tensorHom_comp_tensorHom, tensorHom_comp_tensorHom]
    simp only [Category.id_comp, Category.comp_id]
    exact congrArg (fun t => w ⊗ₘ t) (associator_naturality x y z)
  have hL := congrArg (fun t => t ≫ f') hl
  have hL' := congrArg (fun t => kl ≫ t) hf'
  have hS := congrArg (fun t => t ≫ h1) hs
  have hR := congrArg (fun t => t ≫ ri) hf
  have hR' := congrArg (fun t => v ≫ t) hr
  simp only [Category.assoc] at hL hL' hS hR hR'
  change g0 ≫ li ≫ f' = g0 ≫ f ≫ ri
  exact hL.trans (hL'.trans (hS.trans (hR'.symm.trans hR.symm)))

omit
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
      F m)] in
/-- The actual inverse left comparison is natural in the same three genuine input maps. -/
theorem left_inverse_input_natural :
    Input.mapAt d.tensorEnrichedFunctor (Input.natTrans d.tensorEnrichedFunctor a b) c m ≫
      AssociatorFlattening.nestedToFlat d F' G' H' m =
    AssociatorFlattening.nestedToFlat d F G H m ≫ AssociatorNaturality.leftInputMap d a b c m := by
  let P := AssociatorFlat.leftPoint d F G H m
  let P' := AssociatorFlat.leftPoint d F' G' H' m
  let N := EnrichedDayKernel.obj d.tensorEnrichedFunctor (Output.functor d.tensorEnrichedFunctor F
    G) H m
  let N' := EnrichedDayKernel.obj d.tensorEnrichedFunctor (Output.functor d.tensorEnrichedFunctor F'
    G') H' m
  let l : P ⟶ N := AssociatorFlattening.flatToNested d F G H m
  let li : N ⟶ P := AssociatorFlattening.nestedToFlat d F G H m
  let r : P' ⟶ N' := AssociatorFlattening.flatToNested d F' G' H' m
  let ri : N' ⟶ P' := AssociatorFlattening.nestedToFlat d F' G' H' m
  let x : P ⟶ P' := AssociatorNaturality.leftInputMap d a b c m
  let y : N ⟶ N' := Input.mapAt d.tensorEnrichedFunctor (Input.natTrans d.tensorEnrichedFunctor a b)
    c m
  have h : x ≫ r = l ≫ y := AssociatorNaturality.left_input_natural d a b c m
  have h0 : l ≫ li = 𝟙 P := AssociatorFlattening.flatToNested_nestedToFlat d F G H m
  have h1 : r ≫ ri = 𝟙 P' := AssociatorFlattening.flatToNested_nestedToFlat d F' G' H' m
  apply (cancel_epi (AssociatorFlattening.iso d F G H m).hom).1
  change l ≫ y ≫ ri = l ≫ li ≫ x
  have ht := congrArg (fun t => t ≫ ri) h
  simp only [Category.assoc] at ht
  rw [← ht]
  have h0' := congrArg (fun t => t ≫ x) h0
  have h1' := congrArg (fun t => x ≫ t) h1
  simp only [Category.assoc, Category.id_comp, Category.comp_id] at h0' h1'
  exact h1'.trans h0'.symm

/-- Joint naturality of the actual Day associator on the unchanged chosen nested values. -/
theorem input_natural :
    Input.mapAt d.tensorEnrichedFunctor (Input.natTrans d.tensorEnrichedFunctor a b) c m ≫
      (componentIso d F' G' H' m).hom =
    (componentIso d F G H m).hom ≫
      Input.mapAt d.tensorEnrichedFunctor a (Input.natTrans d.tensorEnrichedFunctor b c) m := by
  let P := AssociatorFlat.leftPoint d F G H m
  let P' := AssociatorFlat.leftPoint d F' G' H' m
  let Q := AssociatorFlat.rightPoint d F G H m
  let Q' := AssociatorFlat.rightPoint d F' G' H' m
  let NL := EnrichedDayKernel.obj d.tensorEnrichedFunctor (Output.functor d.tensorEnrichedFunctor F
    G) H m
  let NL' := EnrichedDayKernel.obj d.tensorEnrichedFunctor (Output.functor d.tensorEnrichedFunctor
    F' G') H' m
  let NR := EnrichedDayKernel.obj d.tensorEnrichedFunctor F (Output.functor d.tensorEnrichedFunctor
    G H) m
  let NR' := EnrichedDayKernel.obj d.tensorEnrichedFunctor F' (Output.functor
    d.tensorEnrichedFunctor G' H') m
  let li : NL ⟶ P := AssociatorFlattening.nestedToFlat d F G H m
  let li' : NL' ⟶ P' := AssociatorFlattening.nestedToFlat d F' G' H' m
  let f : P ⟶ Q := (AssociatorFlat.iso d F G H m).hom
  let f' : P' ⟶ Q' := (AssociatorFlat.iso d F' G' H' m).hom
  let r : Q ⟶ NR := AssociatorRightFlattening.flatToNested d F G H m
  let r' : Q' ⟶ NR' := AssociatorRightFlattening.flatToNested d F' G' H' m
  let xl : NL ⟶ NL' := Input.mapAt d.tensorEnrichedFunctor (Input.natTrans d.tensorEnrichedFunctor a
    b) c m
  let xr : NR ⟶ NR' := Input.mapAt d.tensorEnrichedFunctor a (Input.natTrans d.tensorEnrichedFunctor
    b c) m
  let xf : P ⟶ P' := AssociatorNaturality.leftInputMap d a b c m
  let xg : Q ⟶ Q' := AssociatorNaturality.rightInputMap d a b c m
  have hL : xl ≫ li' = li ≫ xf := left_inverse_input_natural d a b c m
  have hF : xf ≫ f' = f ≫ xg := flat_input_natural d a b c m
  have hR : xg ≫ r' = r ≫ xr := AssociatorNaturality.right_input_natural d a b c m
  have h0 := congrArg (fun t => t ≫ f' ≫ r') hL
  have h1 := congrArg (fun t => li ≫ t ≫ r') hF
  have h2 := congrArg (fun t => li ≫ f ≫ t) hR
  simp only [Category.assoc] at h0 h1 h2
  change xl ≫ (componentIso d F' G' H' m).hom = (componentIso d F G H m).hom ≫ xr
  have hi : (componentIso d F G H m).hom = li ≫ f ≫ r := componentIso_hom d F G H m
  have hi' : (componentIso d F' G' H' m).hom = li' ≫ f' ≫ r' := componentIso_hom d F' G' H' m
  rw [hi, hi']
  simpa only [Category.assoc] using h0.trans (h1.trans h2)

end Inputs


/-- The original selected Day bifunctor nested on the first two genuine inputs. -/
abbrev leftTripleFunctor :
    ((EnrichedFunctorCat V I × EnrichedFunctorCat V I) × EnrichedFunctorCat V I) ⥤
      EnrichedFunctorCat V I :=
  ((Input.bifunctor d.tensorEnrichedFunctor).prod (𝟭 (EnrichedFunctorCat V I))) ⋙
    Input.bifunctor d.tensorEnrichedFunctor

/-- The same original Day bifunctor nested on the final two inputs, with literal product
  reassociation. -/
abbrev rightTripleFunctor :
    ((EnrichedFunctorCat V I × EnrichedFunctorCat V I) × EnrichedFunctorCat V I) ⥤
      EnrichedFunctorCat V I :=
  CategoryTheory.prod.associator (EnrichedFunctorCat V I) (EnrichedFunctorCat V I)
    (EnrichedFunctorCat V I) ⋙
    ((𝟭 (EnrichedFunctorCat V I)).prod (Input.bifunctor d.tensorEnrichedFunctor)) ⋙
      Input.bifunctor d.tensorEnrichedFunctor

/-- The full natural Day associator on the unchanged chosen genuine Day bifunctor. -/
def associator : leftTripleFunctor d ≅ rightTripleFunctor d :=
  NatIso.ofComponents
    (fun X => functorIso d X.1.1.toEnrichedFunctor X.1.2.toEnrichedFunctor X.2.toEnrichedFunctor)
    (by
      intro X Y f
      apply EnrichedFunctorCat.hom_ext
      intro m
      let F := X.1.1.toEnrichedFunctor
      let G := X.1.2.toEnrichedFunctor
      let H := X.2.toEnrichedFunctor
      let F' := Y.1.1.toEnrichedFunctor
      let G' := Y.1.2.toEnrichedFunctor
      let H' := Y.2.toEnrichedFunctor
      let a : GradedNatTrans ((Center.ofBraided V).obj (𝟙_ V)) F F' := f.1.1
      let b : GradedNatTrans ((Center.ofBraided V).obj (𝟙_ V)) G G' := f.1.2
      let c : GradedNatTrans ((Center.ofBraided V).obj (𝟙_ V)) H H' := f.2
      have h := input_natural d a b c m
      change EnrichedFunctorCat.component
          (Input.natTrans d.tensorEnrichedFunctor (Input.natTrans d.tensorEnrichedFunctor a b) c ≫
            (functorIso d F' G' H').hom) m =
        EnrichedFunctorCat.component ((functorIso d F G H).hom ≫
          Input.natTrans d.tensorEnrichedFunctor a (Input.natTrans d.tensorEnrichedFunctor b c)) m
      rw [EnrichedFunctorCat.component_comp, EnrichedFunctorCat.component_comp,
        functorIso_hom_component, functorIso_hom_component]
      change (eHomEquiv V).symm ((Input.natTrans d.tensorEnrichedFunctor
          (Input.natTrans d.tensorEnrichedFunctor a b) c).app m) ≫ (componentIso d F' G' H' m).hom =
        (componentIso d F G H m).hom ≫ (eHomEquiv V).symm
          ((Input.natTrans d.tensorEnrichedFunctor a (Input.natTrans d.tensorEnrichedFunctor b
            c)).app m)
      rw [Input.natTrans_component, Input.natTrans_component]
      exact h)

/-- The natural associator component uses precisely the original nested-value construction. -/
@[simp]
theorem associator_hom_component (F G H : EnrichedFunctorCat V I) (m : I) :
    EnrichedFunctorCat.component
      (F := ⟨Output.functor d.tensorEnrichedFunctor
        (Output.functor d.tensorEnrichedFunctor F.toEnrichedFunctor G.toEnrichedFunctor)
        H.toEnrichedFunctor⟩)
      (G := ⟨Output.functor d.tensorEnrichedFunctor F.toEnrichedFunctor
        (Output.functor d.tensorEnrichedFunctor G.toEnrichedFunctor H.toEnrichedFunctor)⟩)
      ((associator d).hom.app ((F, G), H)) m =
      (componentIso d F.toEnrichedFunctor G.toEnrichedFunctor H.toEnrichedFunctor m).hom :=
  functorIso_hom_component d _ _ _ m

/-- Its inverse uses the same original opposite component, not a separately selected comparison. -/
@[simp]
theorem associator_inv_component (F G H : EnrichedFunctorCat V I) (m : I) :
    EnrichedFunctorCat.component
      (F := ⟨Output.functor d.tensorEnrichedFunctor F.toEnrichedFunctor
        (Output.functor d.tensorEnrichedFunctor G.toEnrichedFunctor H.toEnrichedFunctor)⟩)
      (G := ⟨Output.functor d.tensorEnrichedFunctor
        (Output.functor d.tensorEnrichedFunctor F.toEnrichedFunctor G.toEnrichedFunctor)
        H.toEnrichedFunctor⟩)
      ((associator d).inv.app ((F, G), H)) m =
      (componentIso d F.toEnrichedFunctor G.toEnrichedFunctor H.toEnrichedFunctor m).inv :=
  functorIso_inv_component d _ _ _ m

end CategoryTheory.EnrichedDayKernel.AssociatorConstruction
