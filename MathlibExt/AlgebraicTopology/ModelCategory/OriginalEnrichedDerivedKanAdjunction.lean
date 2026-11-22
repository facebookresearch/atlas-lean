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

public import MathlibExt.AlgebraicTopology.ModelCategory.OriginalEnrichedDerivedKan
public import MathlibExt.AlgebraicTopology.ModelCategory.DerivedAdjunctionCoherence

/-!
# The actual derived Kan and free adjunctions from the original models

Both complete projective models and original factor records are retained.
The source-built Quillen pairs give the full chosen derived adjunctions.
Their units, counits, every Ho Hom function and both replacement comparison
functions are the ones constructed from those original records. Ordinary
Kan/free Quillen constructors supply inputs to these derived results.
-/

@[expose] public section
set_option autoImplicit false
set_option backward.defeqAttrib.useBackward true
noncomputable section
universe w uA uB uV vV
open CategoryTheory Limits MonoidalCategory
open CategoryTheory.Functor

namespace HomotopicalAlgebra.OriginalEnrichedDerivedKan

variable {V : Type uV} [Category.{vV} V] [MonoidalCategory V]
  [BraidedCategory V] [MonoidalClosed V] [ModelCategory V]
  {A : Type uA} [EnrichedCategory V A]
  {B : Type uB} [EnrichedCategory V B]
  {κ : Cardinal.{w}} [Fact κ.IsRegular] [OrderBot κ.ord.ToType]
  [Small.{w} A] [Small.{w} B] [LocallySmall.{w} V]
  (g : CofibrantGenerationData V κ)

section OneIndex

variable (s : OriginalEnrichedProjective.SourceConditions (A := A) g)

/-- The complete right-derived evaluation uses the original projective R and coefficient localization. -/
def derivedEvaluation (a : A) : projectiveHo g s ⥤ (weakEquivalences V).Localization := by
  letI := projectiveModel g s
  letI := free_isQuillen g s a
  exact DerivedFunctorCoherence.right (EnrichedFunctorCat.Free.adjunction a)
    (projectiveReplacements g s)

/-- Both original replacements construct the full actual derived free/evaluation adjunction. -/
def derivedFreeAdjunction (a : A) : derivedFree g s a ⊣ derivedEvaluation g s a := by
  letI := projectiveModel g s
  letI := free_isQuillen g s a
  unfold derivedFree derivedEvaluation
  exact DerivedAdjunctionCoherence.chosenAdjunction (EnrichedFunctorCat.Free.adjunction a)
    (GeneratedFunctorialReplacements.fromGeneration g) (projectiveReplacements g s)

end OneIndex

variable (sA : OriginalEnrichedProjective.SourceConditions (A := A) g)
  (sB : OriginalEnrichedProjective.SourceConditions (A := B) g)

/-- The original Kan pair and both original Q/R records construct the whole derived adjunction. -/
def derivedAdjunction (j : EnrichedFunctor V A B) : derivedKan g sA sB j ⊣ derivedRestriction g sA sB j := by
  letI := projectiveModel g sA
  letI := projectiveModel g sB
  letI := original_isQuillen g sA sB j
  unfold derivedKan derivedRestriction
  exact DerivedAdjunctionCoherence.chosenAdjunction (originalAdjunction g j)
    (projectiveReplacements g sA) (projectiveReplacements g sB)

/-- Every original projective Ho source and target has the complete actual derived Kan Hom equivalence. -/
def derivedHomEquiv (j : EnrichedFunctor V A B) (X : projectiveHo g sA) (Y : projectiveHo g sB) :
    ((derivedKan g sA sB j).obj X ⟶ Y) ≃ (X ⟶ (derivedRestriction g sA sB j).obj Y) :=
  (derivedAdjunction g sA sB j).homEquiv X Y

/-- Every complete source Ho map retains naturality of the whole derived Hom function. -/
theorem derivedHomEquiv_source (j : EnrichedFunctor V A B) {X X' : projectiveHo g sA}
    (a : X' ⟶ X) (Y : projectiveHo g sB) (f : (derivedKan g sA sB j).obj X ⟶ Y) :
    derivedHomEquiv g sA sB j X' Y ((derivedKan g sA sB j).map a ≫ f) =
      a ≫ derivedHomEquiv g sA sB j X Y f :=
  (derivedAdjunction g sA sB j).homEquiv_naturality_left a f

/-- Every original target Ho map retains the actual complete right-derived restriction map. -/
theorem derivedHomEquiv_target (j : EnrichedFunctor V A B) (X : projectiveHo g sA)
    {Y Y' : projectiveHo g sB} (a : Y ⟶ Y') (f : (derivedKan g sA sB j).obj X ⟶ Y) :
    derivedHomEquiv g sA sB j X Y' (f ≫ a) =
      derivedHomEquiv g sA sB j X Y f ≫ (derivedRestriction g sA sB j).map a :=
  (derivedAdjunction g sA sB j).homEquiv_naturality_right f a

/-- The entire derived unit retains the original native Kan unit and both actual replacement comparisons. -/
theorem derivedUnit_fac (j : EnrichedFunctor V A B) (F : EnrichedFunctorCat V A) :
    letI := projectiveModel g sA
    letI := projectiveModel g sB
    letI := original_isQuillen g sA sB j
    (derivedAdjunction g sA sB j).unit.app
        ((DerivedFunctorCoherence.projection (EnrichedFunctorCat V A)).obj F) ≫
      (derivedRestriction g sA sB j).map
        ((DerivedFunctorCoherence.leftComparison (originalAdjunction g j)
          (projectiveReplacements g sA)).app F) =
    (DerivedFunctorCoherence.projection (EnrichedFunctorCat V A)).map
        ((originalAdjunction g j).unit.app F) ≫
      (DerivedFunctorCoherence.rightComparison (originalAdjunction g j)
        (projectiveReplacements g sB)).app ((originalKan g j).obj F) := by
  let := projectiveModel g sA
  let := projectiveModel g sB
  let := original_isQuillen g sA sB j
  exact DerivedAdjunctionCoherence.unit_fac (originalAdjunction g j)
    (projectiveReplacements g sA) (projectiveReplacements g sB) F

/-- The original counit and whole source/target comparisons remain in the full derived counit equation. -/
theorem derivedCounit_fac (j : EnrichedFunctor V A B) (G : EnrichedFunctorCat V B) :
    letI := projectiveModel g sA
    letI := projectiveModel g sB
    letI := original_isQuillen g sA sB j
    (derivedKan g sA sB j).map
        ((DerivedFunctorCoherence.rightComparison (originalAdjunction g j)
          (projectiveReplacements g sB)).app G) ≫
      (derivedAdjunction g sA sB j).counit.app
        ((DerivedFunctorCoherence.projection (EnrichedFunctorCat V B)).obj G) =
    (DerivedFunctorCoherence.leftComparison (originalAdjunction g j)
        (projectiveReplacements g sA)).app ((EnrichedFunctorCat.restriction j).obj G) ≫
      (DerivedFunctorCoherence.projection (EnrichedFunctorCat V B)).map
        ((originalAdjunction g j).counit.app G) := by
  let := projectiveModel g sA
  let := projectiveModel g sB
  let := original_isQuillen g sA sB j
  exact DerivedAdjunctionCoherence.counit_fac (originalAdjunction g j)
    (projectiveReplacements g sA) (projectiveReplacements g sB) G

/-- The full represented derived Hom function is the original Kan adjunct followed by the original R comparison. -/
theorem derivedHomEquiv_original_map (j : EnrichedFunctor V A B)
    (F : EnrichedFunctorCat V A) (G : EnrichedFunctorCat V B) (f : (originalKan g j).obj F ⟶ G) :
    letI := projectiveModel g sA
    letI := projectiveModel g sB
    letI := original_isQuillen g sA sB j
    derivedHomEquiv g sA sB j
        ((DerivedFunctorCoherence.projection (EnrichedFunctorCat V A)).obj F)
        ((DerivedFunctorCoherence.projection (EnrichedFunctorCat V B)).obj G)
      ((DerivedFunctorCoherence.leftComparison (originalAdjunction g j)
          (projectiveReplacements g sA)).app F ≫
        (DerivedFunctorCoherence.projection (EnrichedFunctorCat V B)).map f) =
      (DerivedFunctorCoherence.projection (EnrichedFunctorCat V A)).map
          ((originalAdjunction g j).homEquiv F G f) ≫
        (DerivedFunctorCoherence.rightComparison (originalAdjunction g j)
          (projectiveReplacements g sB)).app G := by
  let := projectiveModel g sA
  let := projectiveModel g sB
  let := original_isQuillen g sA sB j
  exact DerivedAdjunctionCoherence.homEquiv_source_map (originalAdjunction g j)
    (projectiveReplacements g sA) (projectiveReplacements g sB) F G f

/-- The entire inverse Hom function retains the original inverse Kan adjunct and left comparison. -/
theorem derivedHomEquiv_original_map_symm (j : EnrichedFunctor V A B)
    (F : EnrichedFunctorCat V A) (G : EnrichedFunctorCat V B)
    (f : F ⟶ (EnrichedFunctorCat.restriction j).obj G) :
    letI := projectiveModel g sA
    letI := projectiveModel g sB
    letI := original_isQuillen g sA sB j
    (derivedHomEquiv g sA sB j
        ((DerivedFunctorCoherence.projection (EnrichedFunctorCat V A)).obj F)
        ((DerivedFunctorCoherence.projection (EnrichedFunctorCat V B)).obj G)).symm
      ((DerivedFunctorCoherence.projection (EnrichedFunctorCat V A)).map f ≫
        (DerivedFunctorCoherence.rightComparison (originalAdjunction g j)
          (projectiveReplacements g sB)).app G) =
      (DerivedFunctorCoherence.leftComparison (originalAdjunction g j)
          (projectiveReplacements g sA)).app F ≫
        (DerivedFunctorCoherence.projection (EnrichedFunctorCat V B)).map
          (((originalAdjunction g j).homEquiv F G).symm f) := by
  let := projectiveModel g sA
  let := projectiveModel g sB
  let := original_isQuillen g sA sB j
  exact DerivedAdjunctionCoherence.homEquiv_source_map_symm (originalAdjunction g j)
    (projectiveReplacements g sA) (projectiveReplacements g sB) F G f

/-- Both actual diagram Q/R maps retain the full ordinary-Ho Kan transpose at the original source and target. -/
theorem derivedHomEquiv_replacements (j : EnrichedFunctor V A B)
    (F : EnrichedFunctorCat V A) (G : EnrichedFunctorCat V B) :
    letI := projectiveModel g sA
    letI := projectiveModel g sB
    letI := original_isQuillen g sA sB j
    ∀ f : (derivedKan g sA sB j).obj
        ((DerivedFunctorCoherence.projection (EnrichedFunctorCat V A)).obj F) ⟶
        (DerivedFunctorCoherence.projection (EnrichedFunctorCat V B)).obj G,
      (DerivedFunctorCoherence.projection (EnrichedFunctorCat V A)).map
          ((projectiveReplacements g sA).q.app F) ≫
        derivedHomEquiv g sA sB j
          ((DerivedFunctorCoherence.projection (EnrichedFunctorCat V A)).obj F)
          ((DerivedFunctorCoherence.projection (EnrichedFunctorCat V B)).obj G) f =
      DerivedAdjunctionCoherence.originalHomEquiv (originalAdjunction g j)
        (projectiveReplacements g sA) (projectiveReplacements g sB) F G
        (f ≫ (DerivedFunctorCoherence.projection (EnrichedFunctorCat V B)).map
          ((projectiveReplacements g sB).r.app G)) := by
  let := projectiveModel g sA
  let := projectiveModel g sB
  let := original_isQuillen g sA sB j
  intro f
  exact DerivedAdjunctionCoherence.homEquiv_original (originalAdjunction g j)
    (projectiveReplacements g sA) (projectiveReplacements g sB) F G f

end HomotopicalAlgebra.OriginalEnrichedDerivedKan
