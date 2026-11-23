/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.AlgebraicTopology.ModelCategory.OriginalEnrichedDerivedRestrictionComposition
public import Mathlib.CategoryTheory.Adjunction.Mates

/-!
# The derived Beck--Chevalley mate of the same original enriched square

Four independent original index categories and projective source models
are retained. An equality of the original full enriched index composites
gives the actual right-derived restriction square through both original
R-composition comparisons. Its left Kan mate uses those same original
derived pairs and their units/counits. Invertibility of this left mate
requires the separate original homotopy-exact/cofinal source criterion;
it is not inferred from invertibility of the right square.
-/

@[expose] public section
set_option autoImplicit false
set_option backward.defeqAttrib.useBackward true
noncomputable section
universe w uA uB uC uD uV vV
open CategoryTheory Limits MonoidalCategory
open CategoryTheory.Functor

namespace HomotopicalAlgebra.OriginalEnrichedDerivedKan

variable {V : Type uV} [Category.{vV} V] [MonoidalCategory V]
  [BraidedCategory V] [MonoidalClosed V] [ModelCategory V]
  {A : Type uA} [EnrichedCategory V A]
  {B : Type uB} [EnrichedCategory V B]
  {C : Type uC} [EnrichedCategory V C]
  {D : Type uD} [EnrichedCategory V D]
  {κ : Cardinal.{w}} [Fact κ.IsRegular] [OrderBot κ.ord.ToType]
  [Small.{w} A] [Small.{w} B] [Small.{w} C] [Small.{w} D] [LocallySmall.{w} V]
  (g : CofibrantGenerationData V κ)
  (sA : OriginalEnrichedProjective.SourceConditions (A := A) g)
  (sB : OriginalEnrichedProjective.SourceConditions (A := B) g)
  (sC : OriginalEnrichedProjective.SourceConditions (A := C) g)
  (sD : OriginalEnrichedProjective.SourceConditions (A := D) g)

/-- The same entire original index square constructs its actual right-derived restriction Iso. -/
def rightSquare (j : EnrichedFunctor V A B) (k : EnrichedFunctor V C D)
    (p : EnrichedFunctor V A C) (q : EnrichedFunctor V B D)
    (h : p.comp V k = j.comp V q) :
    derivedRestriction g sC sD k ⋙ derivedRestriction g sA sC p ≅
      derivedRestriction g sB sD q ⋙ derivedRestriction g sA sB j :=
  restrictionComposition g sA sC sD p k ≪≫
    eqToIso (congrArg (fun r : EnrichedFunctor V A D => derivedRestriction g sA sD r) h) ≪≫
      (restrictionComposition g sA sB sD j q).symm

/-- The original right square gives the complete actual derived left Kan BC mate. -/
def beckChevalley (j : EnrichedFunctor V A B) (k : EnrichedFunctor V C D)
    (p : EnrichedFunctor V A C) (q : EnrichedFunctor V B D)
    (h : p.comp V k = j.comp V q) :
    derivedRestriction g sA sC p ⋙ derivedKan g sA sB j ⟶
      derivedKan g sC sD k ⋙ derivedRestriction g sB sD q :=
  (mateEquiv (derivedAdjunction g sC sD k) (derivedAdjunction g sA sB j)).symm
    (rightSquare g sA sB sC sD j k p q h).hom

/-- Every full original source Ho morphism retains the actual BC mate naturality square. -/
theorem beckChevalley_naturality (j : EnrichedFunctor V A B) (k : EnrichedFunctor V C D)
    (p : EnrichedFunctor V A C) (q : EnrichedFunctor V B D)
    (h : p.comp V k = j.comp V q) {X Y : projectiveHo g sC} (f : X ⟶ Y) :
    (derivedRestriction g sA sC p ⋙ derivedKan g sA sB j).map f ≫
        (beckChevalley g sA sB sC sD j k p q h).app Y =
      (beckChevalley g sA sB sC sD j k p q h).app X ≫
        (derivedKan g sC sD k ⋙ derivedRestriction g sB sD q).map f :=
  (beckChevalley g sA sB sC sD j k p q h).naturality f

/-- The whole original derived unit equation characterizes the same BC mate. -/
theorem beckChevalley_unit (j : EnrichedFunctor V A B) (k : EnrichedFunctor V C D)
    (p : EnrichedFunctor V A C) (q : EnrichedFunctor V B D)
    (h : p.comp V k = j.comp V q) (X : projectiveHo g sC) :
    (derivedRestriction g sA sC p).map ((derivedAdjunction g sC sD k).unit.app X) ≫
        (rightSquare g sA sB sC sD j k p q h).hom.app ((derivedKan g sC sD k).obj X) =
      (derivedAdjunction g sA sB j).unit.app ((derivedRestriction g sA sC p).obj X) ≫
        (derivedRestriction g sA sB j).map
          ((beckChevalley g sA sB sC sD j k p q h).app X) :=
  unit_mateEquiv_symm (derivedAdjunction g sC sD k) (derivedAdjunction g sA sB j)
    (rightSquare g sA sB sC sD j k p q h).hom X

/-- Both full original counits retain every original right-square and BC-mate component. -/
theorem beckChevalley_counit (j : EnrichedFunctor V A B) (k : EnrichedFunctor V C D)
    (p : EnrichedFunctor V A C) (q : EnrichedFunctor V B D)
    (h : p.comp V k = j.comp V q) (Y : projectiveHo g sD) :
    (derivedKan g sA sB j).map ((rightSquare g sA sB sC sD j k p q h).hom.app Y) ≫
        (derivedAdjunction g sA sB j).counit.app ((derivedRestriction g sB sD q).obj Y) =
      (beckChevalley g sA sB sC sD j k p q h).app ((derivedRestriction g sC sD k).obj Y) ≫
        (derivedRestriction g sB sD q).map ((derivedAdjunction g sC sD k).counit.app Y) :=
  mateEquiv_counit_symm (derivedAdjunction g sC sD k) (derivedAdjunction g sA sB j)
    (rightSquare g sA sB sC sD j k p q h).hom Y

/-- The same forward square is exactly recovered by taking the actual mate back. -/
theorem beckChevalley_right_readback (j : EnrichedFunctor V A B) (k : EnrichedFunctor V C D)
    (p : EnrichedFunctor V A C) (q : EnrichedFunctor V B D)
    (h : p.comp V k = j.comp V q) :
    mateEquiv (derivedAdjunction g sC sD k) (derivedAdjunction g sA sB j)
      (beckChevalley g sA sB sC sD j k p q h) =
        (rightSquare g sA sB sC sD j k p q h).hom :=
  (mateEquiv (derivedAdjunction g sC sD k) (derivedAdjunction g sA sB j)).apply_symm_apply _

end HomotopicalAlgebra.OriginalEnrichedDerivedKan
