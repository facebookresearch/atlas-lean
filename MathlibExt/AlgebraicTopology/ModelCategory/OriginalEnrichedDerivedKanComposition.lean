/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Attribution for this imported development.
Author: @toskua, Codex
-/

module

public import MathlibExt.AlgebraicTopology.ModelCategory.OriginalEnrichedDerivedKanAdjunction
public import MathlibExt.CategoryTheory.Enriched.LeftKanComposition

/-!
# Composition of the actual original derived weighted Kan functors

Original generation supplies the three genuine coend presentations.
Their full native Kan/restriction adjunction comparison is left-derived
using the same source Q. The original Q-compositor gives the comparison
to the iterated derived Kan functors. All original models, index functors,
inverse maps and arbitrary Ho naturality squares are retained.
-/

@[expose] public section
set_option autoImplicit false
set_option backward.defeqAttrib.useBackward true
noncomputable section
universe w uA uB uC uV vV
open CategoryTheory Limits MonoidalCategory
open CategoryTheory.Functor

namespace HomotopicalAlgebra.OriginalEnrichedDerivedKan

variable {V : Type uV} [Category.{vV} V] [MonoidalCategory V]
  [BraidedCategory V] [MonoidalClosed V] [ModelCategory V]
  {A : Type uA} [EnrichedCategory V A]
  {B : Type uB} [EnrichedCategory V B]
  {C : Type uC} [EnrichedCategory V C]
  {κ : Cardinal.{w}} [Fact κ.IsRegular] [OrderBot κ.ord.ToType]
  [Small.{w} A] [Small.{w} B] [Small.{w} C] [LocallySmall.{w} V]
  (g : CofibrantGenerationData V κ)

/-- The whole actual original coend comparison uses its three original generated colimit certificates. -/
def originalKanComposition (j : EnrichedFunctor V A B) (k : EnrichedFunctor V B C) :
    originalKan g (j.comp V k) ≅ originalKan g j ⋙ originalKan g k := by
  letI := objectCoproducts g j
  letI := relationCoproducts g j
  letI := balanceCoequalizers g j
  letI := objectCoproducts g k
  letI := relationCoproducts g k
  letI := balanceCoequalizers g k
  letI := objectCoproducts g (j.comp V k)
  letI := relationCoproducts g (j.comp V k)
  letI := balanceCoequalizers g (j.comp V k)
  exact EnrichedFunctorCat.LeftKanComposition.comparison j k

variable (sA : OriginalEnrichedProjective.SourceConditions (A := A) g)
  (sB : OriginalEnrichedProjective.SourceConditions (A := B) g)
  (sC : OriginalEnrichedProjective.SourceConditions (A := C) g)

/-- The original complete Q maps and actual coend comparison give the full derived Kan compositor. -/
def kanComposition (j : EnrichedFunctor V A B) (k : EnrichedFunctor V B C) :
    derivedKan g sA sC (j.comp V k) ≅ derivedKan g sA sB j ⋙ derivedKan g sB sC k := by
  letI := projectiveModel g sA
  letI := projectiveModel g sB
  letI := projectiveModel g sC
  letI := original_isQuillen g sA sB j
  letI := original_isQuillen g sB sC k
  letI := original_isQuillen g sA sC (j.comp V k)
  exact DerivedFunctorCoherence.leftNatIso (originalAdjunction g (j.comp V k))
      ((originalAdjunction g j).comp (originalAdjunction g k))
      (projectiveReplacements g sA) (originalKanComposition g j k) ≪≫
    (DerivedFunctorCoherence.leftCompositionIso (originalAdjunction g j)
      (originalAdjunction g k) (projectiveReplacements g sA) (projectiveReplacements g sB)).symm

/-- Every actual original source Ho map retains the whole forward coend/compositor square. -/
theorem kanComposition_naturality (j : EnrichedFunctor V A B) (k : EnrichedFunctor V B C)
    {X Y : projectiveHo g sA} (f : X ⟶ Y) :
    (derivedKan g sA sC (j.comp V k)).map f ≫ (kanComposition g sA sB sC j k).hom.app Y =
      (kanComposition g sA sB sC j k).hom.app X ≫
        (derivedKan g sA sB j ⋙ derivedKan g sB sC k).map f :=
  (kanComposition g sA sB sC j k).hom.naturality f

/-- The whole inverse square retains the original source Ho map and both complete derived functors. -/
theorem kanComposition_inverse_naturality (j : EnrichedFunctor V A B) (k : EnrichedFunctor V B C)
    {X Y : projectiveHo g sA} (f : X ⟶ Y) :
    (derivedKan g sA sB j ⋙ derivedKan g sB sC k).map f ≫
        (kanComposition g sA sB sC j k).inv.app Y =
      (kanComposition g sA sB sC j k).inv.app X ≫
        (derivedKan g sA sC (j.comp V k)).map f :=
  (kanComposition g sA sB sC j k).inv.naturality f

end HomotopicalAlgebra.OriginalEnrichedDerivedKan
