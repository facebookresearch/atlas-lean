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

public import MathlibExt.AlgebraicTopology.ModelCategory.OriginalEnrichedDiagramQuillen
public import MathlibExt.AlgebraicTopology.ModelCategory.CofibrantlyGenerated.Colimits
public import MathlibExt.AlgebraicTopology.ModelCategory.DerivedFunctorNaturalIso
public import MathlibExt.CategoryTheory.Enriched.LeftKanFreeComparison

/-!
# Derived Kan/free comparison from the original projective source

The original coefficient generation supplies working-size colimits and
both original diagram models and factor records. Only the actual A and
A × A coproduct shapes are used for the Kan coend. The derived comparison
keeps the original Q, the intermediate q and the native coend contraction
on all coefficient objects and all homotopy-category morphisms.
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

include g in
omit [Small.{w} B] [LocallySmall.{w} V] in
/-- Generation supplies the original actual object-coproduct shape. -/
theorem objectCoproducts (j : EnrichedFunctor V A B) :
    ∀ (F : EnrichedFunctorCat V A) (b : B),
      HasCoproduct (Enriched.weightedCoend.objects (EnrichedFunctorCat.leftKanWeight j b)
        F.toEnrichedFunctor) := by
  intro F b
  let : HasColimitsOfShape (Discrete A) V := g.hasColimitsOfShape
  infer_instance

include g in
omit [Small.{w} B] [LocallySmall.{w} V] in
/-- The relation coproduct uses exactly the original A × A shape. -/
theorem relationCoproducts (j : EnrichedFunctor V A B) :
    ∀ (F : EnrichedFunctorCat V A) (b : B),
      HasCoproduct (Enriched.weightedCoend.relations (EnrichedFunctorCat.leftKanWeight j b)
        F.toEnrichedFunctor) := by
  intro F b
  let : HasColimitsOfShape (Discrete (A × A)) V := g.hasColimitsOfShape
  infer_instance

omit [Small.{w} B] [LocallySmall.{w} V] in
/-- Original model coequalizers balance those same complete coproducts. -/
theorem balanceCoequalizers (j : EnrichedFunctor V A B) :
    letI := objectCoproducts g j
    letI := relationCoproducts g j
    ∀ (F : EnrichedFunctorCat V A) (b : B),
      HasCoequalizer
        (Enriched.weightedCoend.leftMap (EnrichedFunctorCat.leftKanWeight j b) F.toEnrichedFunctor)
        (Enriched.weightedCoend.rightMap (EnrichedFunctorCat.leftKanWeight j b) F.toEnrichedFunctor) := by
  let := objectCoproducts g j
  let := relationCoproducts g j
  intro F b
  infer_instance

/-- The original weighted Kan functor with these actual coend certificates. -/
def originalKan (j : EnrichedFunctor V A B) :
    EnrichedFunctorCat V A ⥤ EnrichedFunctorCat V B := by
  letI := objectCoproducts g j
  letI := relationCoproducts g j
  letI := balanceCoequalizers g j
  exact EnrichedFunctorCat.leftKan j

/-- Both full Hom functions, units and counits are the original Kan pair. -/
def originalAdjunction (j : EnrichedFunctor V A B) :
    originalKan g j ⊣ EnrichedFunctorCat.restriction j := by
  letI := objectCoproducts g j
  letI := relationCoproducts g j
  letI := balanceCoequalizers g j
  exact EnrichedFunctorCat.leftKanRestrictionAdjunction j

/-- The actual free/coend comparison is supplied by its original two adjunctions. -/
def pointsetFreeIso (j : EnrichedFunctor V A B) (a : A) :
    EnrichedFunctorCat.Free.functor a ⋙ originalKan g j ≅
      EnrichedFunctorCat.Free.functor (j.obj a) := by
  letI := objectCoproducts g j
  letI := relationCoproducts g j
  letI := balanceCoequalizers g j
  exact EnrichedFunctorCat.LeftKanFreeComparison.functorIso j a

section OneIndex

variable (s : OriginalEnrichedProjective.SourceConditions (A := A) g)

/-- Reuse the original projective model, deriving working colimits from g. -/
@[instance_reducible]
def projectiveModel : ModelCategory (EnrichedFunctorCat V A) := by
  letI : HasColimitsOfSize.{w, w} V := g.hasColimitsOfSize
  exact EnrichedProjective.modelCategory g s.I_tensor s.J_tensor s.I_source s.J_source

/-- The homotopy category is the same original weak localization. -/
abbrev projectiveHo :=
  letI := projectiveModel g s
  (weakEquivalences (EnrichedFunctorCat V A)).Localization

/-- Complete original Q/R data from the same projective generation and both factors. -/
def projectiveReplacements :
    letI := projectiveModel g s
    GeneratedFunctorialReplacements.Data (C := EnrichedFunctorCat V A) := by
  letI : HasColimitsOfSize.{w, w} V := g.hasColimitsOfSize
  letI := projectiveModel g s
  exact GeneratedFunctorialReplacements.fromGeneration
    (OriginalEnrichedProjective.generationData g s)

/-- Both full replacement factors are the entire original fixed-cardinal factors. -/
theorem projectiveReplacements_factors :
    letI : HasColimitsOfSize.{w, w} V := g.hasColimitsOfSize
    letI := projectiveModel g s
    (projectiveReplacements g s).cofibrantFactor =
        OriginalEnrichedProjective.cofibrantFactorizationData g s ∧
      (projectiveReplacements g s).fibrantFactor =
        OriginalEnrichedProjective.fibrantFactorizationData g s := by
  let : HasColimitsOfSize.{w, w} V := g.hasColimitsOfSize
  let := projectiveModel g s
  exact OriginalEnrichedProjective.generationData_factorizations g s

/-- The original free/evaluation pair is Quillen on the same source-built model. -/
theorem free_isQuillen (a : A) :
    letI := projectiveModel g s
    (EnrichedFunctorCat.Free.adjunction (V := V) a).IsQuillenAdjunction := by
  let : HasColimitsOfSize.{w, w} V := g.hasColimitsOfSize
  let := projectiveModel g s
  exact EnrichedProjective.freeAtEvaluation_isQuillenAdjunction g
    s.I_tensor s.J_tensor s.I_source s.J_source a

/-- The free functor on every coefficient Ho object uses the original coefficient Q. -/
def derivedFree (a : A) : (weakEquivalences V).Localization ⥤ projectiveHo g s := by
  letI := projectiveModel g s
  letI := free_isQuillen g s a
  exact DerivedFunctorCoherence.left (EnrichedFunctorCat.Free.adjunction a)
    (GeneratedFunctorialReplacements.fromGeneration g)

end OneIndex

variable (sA : OriginalEnrichedProjective.SourceConditions (A := A) g)
  (sB : OriginalEnrichedProjective.SourceConditions (A := B) g)

/-- Original restriction right classes prove the genuine Kan pair Quillen. -/
theorem original_isQuillen (j : EnrichedFunctor V A B) :
    letI := projectiveModel g sA
    letI := projectiveModel g sB
    (originalAdjunction g j).IsQuillenAdjunction := by
  let : HasColimitsOfSize.{w, w} V := g.hasColimitsOfSize
  let := projectiveModel g sA
  let := projectiveModel g sB
  have h := OriginalEnrichedDiagramQuillen.restriction_right_classes g sA sB j
  exact Adjunction.IsQuillenAdjunction.mkOfPreservesFibrations
    (adj := originalAdjunction g j) h.1 h.2

/-- The complete derived Kan functor uses the entire original source Q. -/
def derivedKan (j : EnrichedFunctor V A B) : projectiveHo g sA ⥤ projectiveHo g sB := by
  letI := projectiveModel g sA
  letI := projectiveModel g sB
  letI := original_isQuillen g sA sB j
  exact DerivedFunctorCoherence.left (originalAdjunction g j) (projectiveReplacements g sA)

/-- The complete derived restriction retains the original target R. -/
def derivedRestriction (j : EnrichedFunctor V A B) : projectiveHo g sB ⥤ projectiveHo g sA := by
  letI := projectiveModel g sA
  letI := projectiveModel g sB
  letI := original_isQuillen g sA sB j
  exact DerivedFunctorCoherence.right (originalAdjunction g j) (projectiveReplacements g sB)

/-- The actual full derived Kan/free comparison on all coefficient Ho objects and maps. -/
def freeComparison (j : EnrichedFunctor V A B) (a : A) :
    derivedFree g sA a ⋙ derivedKan g sA sB j ≅ derivedFree g sB (j.obj a) := by
  letI := projectiveModel g sA
  letI := projectiveModel g sB
  letI := free_isQuillen g sA a
  letI := free_isQuillen g sB (j.obj a)
  letI := original_isQuillen g sA sB j
  exact DerivedFunctorCoherence.leftCompositionIso (EnrichedFunctorCat.Free.adjunction a)
      (originalAdjunction g j) (GeneratedFunctorialReplacements.fromGeneration g)
      (projectiveReplacements g sA) ≪≫
    DerivedFunctorCoherence.leftNatIso
      ((EnrichedFunctorCat.Free.adjunction a).comp (originalAdjunction g j))
      (EnrichedFunctorCat.Free.adjunction (j.obj a))
      (GeneratedFunctorialReplacements.fromGeneration g) (pointsetFreeIso g j a)

/-- Every original coefficient-Ho map has the complete forward naturality square. -/
theorem freeComparison_naturality (j : EnrichedFunctor V A B) (a : A)
    {X Y : (weakEquivalences V).Localization} (f : X ⟶ Y) :
    (derivedFree g sA a ⋙ derivedKan g sA sB j).map f ≫
        (freeComparison g sA sB j a).hom.app Y =
      (freeComparison g sA sB j a).hom.app X ≫ (derivedFree g sB (j.obj a)).map f :=
  (freeComparison g sA sB j a).hom.naturality f

/-- The inverse comparison retains all arbitrary original coefficient-Ho morphisms. -/
theorem freeComparison_inverse_naturality (j : EnrichedFunctor V A B) (a : A)
    {X Y : (weakEquivalences V).Localization} (f : X ⟶ Y) :
    (derivedFree g sB (j.obj a)).map f ≫ (freeComparison g sA sB j a).inv.app Y =
      (freeComparison g sA sB j a).inv.app X ≫
        (derivedFree g sA a ⋙ derivedKan g sA sB j).map f :=
  (freeComparison g sA sB j a).inv.naturality f

/-- The forward map is the original intermediate q followed by the same actual coend/free map. -/
theorem freeComparison_hom_app (j : EnrichedFunctor V A B) (a : A) (X : V) :
    letI := projectiveModel g sA
    letI := projectiveModel g sB
    (freeComparison g sA sB j a).hom.app ((DerivedFunctorCoherence.projection V).obj X) =
      (DerivedFunctorCoherence.projection (EnrichedFunctorCat V B)).map
        ((originalKan g j).map ((projectiveReplacements g sA).q.app
            (EnrichedFunctorCat.Free.object a
              ((GeneratedFunctorialReplacements.fromGeneration g).Q.obj X))) ≫
          (pointsetFreeIso g j a).hom.app
            ((GeneratedFunctorialReplacements.fromGeneration g).Q.obj X)) := by
  let := projectiveModel g sA
  let := projectiveModel g sB
  let := free_isQuillen g sA a
  let := free_isQuillen g sB (j.obj a)
  let := original_isQuillen g sA sB j
  change (DerivedFunctorCoherence.leftCompositionIso (EnrichedFunctorCat.Free.adjunction a)
      (originalAdjunction g j) (GeneratedFunctorialReplacements.fromGeneration g)
      (projectiveReplacements g sA)).hom.app ((DerivedFunctorCoherence.projection V).obj X) ≫
    (DerivedFunctorCoherence.leftNatIso
      ((EnrichedFunctorCat.Free.adjunction a).comp (originalAdjunction g j))
      (EnrichedFunctorCat.Free.adjunction (j.obj a))
      (GeneratedFunctorialReplacements.fromGeneration g) (pointsetFreeIso g j a)).hom.app
        ((DerivedFunctorCoherence.projection V).obj X) = _
  rw [DerivedFunctorCoherence.leftCompositionIso_app,
    DerivedFunctorCoherence.leftNatIso_hom_app]
  exact (DerivedFunctorCoherence.projection (EnrichedFunctorCat V B)).map_comp _ _ |>.symm

end HomotopicalAlgebra.OriginalEnrichedDerivedKan
