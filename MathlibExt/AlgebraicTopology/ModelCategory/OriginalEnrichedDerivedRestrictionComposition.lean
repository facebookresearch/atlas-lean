/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.AlgebraicTopology.ModelCategory.OriginalEnrichedDerivedKanAdjunction
public import MathlibExt.CategoryTheory.Enriched.RestrictionInversePair

/-!
# Composition of the actual original derived restrictions

The original full index restriction identity is derived on the same
target R. The inverse original right compositor retains the intermediate
R-unit. Every coefficient action, map and original projective model is
kept. This comparison supplies the actual right-hand square for the
derived Beck--Chevalley mate construction.
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
  (sA : OriginalEnrichedProjective.SourceConditions (A := A) g)
  (sB : OriginalEnrichedProjective.SourceConditions (A := B) g)
  (sC : OriginalEnrichedProjective.SourceConditions (A := C) g)

/-- The same full native restriction composition identity includes every original enriched action. -/
def originalRestrictionComposition (j : EnrichedFunctor V A B) (k : EnrichedFunctor V B C) :
    EnrichedFunctorCat.restriction k ⋙ EnrichedFunctorCat.restriction j ≅
      EnrichedFunctorCat.restriction (j.comp V k) :=
  eqToIso (EnrichedFunctorCat.RestrictionInversePair.restriction_comp j k)

/-- The complete right-derived composition is built from the original intermediate R-unit and native identity. -/
def restrictionComposition (j : EnrichedFunctor V A B) (k : EnrichedFunctor V B C) :
    derivedRestriction g sB sC k ⋙ derivedRestriction g sA sB j ≅
      derivedRestriction g sA sC (j.comp V k) := by
  letI := projectiveModel g sA
  letI := projectiveModel g sB
  letI := projectiveModel g sC
  letI := original_isQuillen g sA sB j
  letI := original_isQuillen g sB sC k
  letI := original_isQuillen g sA sC (j.comp V k)
  exact (DerivedFunctorCoherence.rightCompositionIso (originalAdjunction g j)
      (originalAdjunction g k) (projectiveReplacements g sB) (projectiveReplacements g sC)).symm ≪≫
    DerivedFunctorCoherence.rightNatIso ((originalAdjunction g j).comp (originalAdjunction g k))
      (originalAdjunction g (j.comp V k)) (projectiveReplacements g sC)
      (originalRestrictionComposition j k)

/-- Every original target Ho morphism retains the entire forward restriction-composition square. -/
theorem restrictionComposition_naturality (j : EnrichedFunctor V A B) (k : EnrichedFunctor V B C)
    {X Y : projectiveHo g sC} (f : X ⟶ Y) :
    (derivedRestriction g sB sC k ⋙ derivedRestriction g sA sB j).map f ≫
        (restrictionComposition g sA sB sC j k).hom.app Y =
      (restrictionComposition g sA sB sC j k).hom.app X ≫
        (derivedRestriction g sA sC (j.comp V k)).map f :=
  (restrictionComposition g sA sB sC j k).hom.naturality f

/-- The full inverse square uses the same original derived functors and all Ho morphisms. -/
theorem restrictionComposition_inverse_naturality (j : EnrichedFunctor V A B) (k : EnrichedFunctor V B C)
    {X Y : projectiveHo g sC} (f : X ⟶ Y) :
    (derivedRestriction g sA sC (j.comp V k)).map f ≫
        (restrictionComposition g sA sB sC j k).inv.app Y =
      (restrictionComposition g sA sB sC j k).inv.app X ≫
        (derivedRestriction g sB sC k ⋙ derivedRestriction g sA sB j).map f :=
  (restrictionComposition g sA sB sC j k).inv.naturality f

end HomotopicalAlgebra.OriginalEnrichedDerivedKan
