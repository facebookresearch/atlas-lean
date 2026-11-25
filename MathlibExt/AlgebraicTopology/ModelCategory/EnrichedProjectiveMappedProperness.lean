/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua, Codex
import MathlibExt.AlgebraicTopology.ModelCategory.EnrichedProjectiveMappedTransport
import MathlibExt.AlgebraicTopology.ModelCategory.EnrichedProjective.Proper

/-!
# Properness of the actual mapped-source projective models

The source generation data and generator tensor bounds prove evaluated
cofibration membership and left properness for the same constructed model.
The original carrier transport retains every pushout map and both classes.
-/

set_option autoImplicit false

noncomputable section

universe w uA uV vV uC vC

open CategoryTheory Limits MorphismProperty MonoidalCategory

namespace HomotopicalAlgebra.EnrichedProjective.MappedSources

variable {V : Type uV} [Category.{vV} V] [MonoidalCategory V]
  [BraidedCategory V] [MonoidalClosed V] [ModelCategory V]
  {A : Type uA} [EnrichedCategory V A]
  {κ : Cardinal.{w}} [Fact κ.IsRegular] [OrderBot κ.ord.ToType]
  [Small.{w} A] [LocallySmall.{w} V] [HasColimitsOfSize.{w, w} V]
  (d : CofibrantGenerationData V κ)
  (hJ : ∀ a b : A, ∀ {X Y : V} (f : X ⟶ Y), d.J f → trivialCofibrations V (f ▷ (a ⟶[V] b)))
  (hSourceI : SourceCondition (A := A) (κ := κ) d.I)
  (hSourceJ : SourceCondition (A := A) (κ := κ) d.J)
  (hI : ∀ a b : A, ∀ {X Y : V} (f : X ⟶ Y), d.I f → cofibrations V (f ▷ (a ⟶[V] b)))

include hI

/-- The actual source-generated model's entire cofibration class evaluates into base cofibrations.
-/
theorem modelCategory_cofibrations_le_evaluationProperty :
    letI : ModelCategory (EnrichedFunctorCat V A) := modelCategory d hJ hSourceI hSourceJ
    cofibrations (EnrichedFunctorCat V A) ≤
      EvaluationTransfer.evaluationProperty (fun a : A => EnrichedFunctorCat.evaluation a)
          (cofibrations V) := by
  let _ : ModelCategory (EnrichedFunctorCat V A) := modelCategory d hJ hSourceI hSourceJ
  let _ : (cofibrations V).IsStableUnderCoproducts.{w} :=
    IsStableUnderCoproducts.of_llp_eq (cofibrations V) (trivialFibrations V)
        (trivialFibrations_llp V)
  let _ : (cofibrations V).IsStableUnderTransfiniteCompositionOfShape κ.ord.ToType := by
    rw [← trivialFibrations_llp V]
    infer_instance
  exact EnrichedProjective.cofibrations_le_evaluationProperty
    (generationData d hJ hSourceI hSourceJ) d.I (cofibrations V)
    (generationData_I d hJ hSourceI hSourceJ) hI

variable [hBaseProper : IsLeftProper V]

include hBaseProper

/-- Source left properness and generator tensor membership prove the actual projective model left
proper. -/
theorem modelCategory_isLeftProper :
    letI : ModelCategory (EnrichedFunctorCat V A) := modelCategory d hJ hSourceI hSourceJ
    IsLeftProper (EnrichedFunctorCat V A) := by
  let _ : ModelCategory (EnrichedFunctorCat V A) := modelCategory d hJ hSourceI hSourceJ
  let _ : (cofibrations V).IsStableUnderCoproducts.{w} :=
    IsStableUnderCoproducts.of_llp_eq (cofibrations V) (trivialFibrations V)
        (trivialFibrations_llp V)
  let _ : (cofibrations V).IsStableUnderTransfiniteCompositionOfShape κ.ord.ToType := by
    rw [← trivialFibrations_llp V]
    infer_instance
  exact EnrichedProjective.isLeftProper_of_generatorTensor
    (generationData d hJ hSourceI hSourceJ) d.I (cofibrations V)
    (generationData_I d hJ hSourceI hSourceJ)
    (weakEquivalences_eq d hJ hSourceI hSourceJ) hI inferInstance

/-- Every original pushout of a model weak arrow along a model cofibration remains weak. -/
theorem modelCategory_weak_of_isPushout
    {X Y Z P : EnrichedFunctorCat V A} {i : X ⟶ Y} {f : X ⟶ Z} {f' : Y ⟶ P} {j : Z ⟶ P}
    (sq : IsPushout i f f' j) :
    letI : ModelCategory (EnrichedFunctorCat V A) := modelCategory d hJ hSourceI hSourceJ
    cofibrations (EnrichedFunctorCat V A) i → weakEquivalences (EnrichedFunctorCat V A) f →
      weakEquivalences (EnrichedFunctorCat V A) f' := by
  let _ : ModelCategory (EnrichedFunctorCat V A) := modelCategory d hJ hSourceI hSourceJ
  intro hi hf
  have hp := modelCategory_isLeftProper d hJ hSourceI hSourceJ hI
  exact hp.weakEquivalences_isStableUnderCobaseChangeAgainst_cofibrations.of_isPushout sq hi hf

variable {C : Type uC} [Category.{vC} C]

/-- The same produced projective model is left proper on the actual original carrier transport. -/
theorem sourceModelCategory_isLeftProper (e : C ≌ EnrichedFunctorCat V A) :
    letI : ModelCategory C := sourceModelCategory d hJ hSourceI hSourceJ e
    IsLeftProper C := by
  let _ : ModelCategory (EnrichedFunctorCat V A) := modelCategory d hJ hSourceI hSourceJ
  let _ : ModelCategory C := sourceModelCategory d hJ hSourceI hSourceJ e
  have hp := modelCategory_isLeftProper d hJ hSourceI hSourceJ hI
  constructor
  constructor
  intro X Y i hi
  constructor
  intro Z P j f' f sq hf
  change cofibrations (EnrichedFunctorCat V A) (e.functor.map i) at hi
  change weakEquivalences (EnrichedFunctorCat V A) (e.functor.map f) at hf
  change weakEquivalences (EnrichedFunctorCat V A) (e.functor.map f')
  exact hp.weakEquivalences_isStableUnderCobaseChangeAgainst_cofibrations.of_isPushout
    (sq.map e.functor) hi hf

/-- The original carrier's literal pushout arrows retain the weak conclusion for its actual model.
-/
theorem sourceModelCategory_weak_of_isPushout (e : C ≌ EnrichedFunctorCat V A)
    {X Y Z P : C} {i : X ⟶ Y} {f : X ⟶ Z} {f' : Y ⟶ P} {j : Z ⟶ P}
    (sq : IsPushout i f f' j) :
    letI : ModelCategory C := sourceModelCategory d hJ hSourceI hSourceJ e
    cofibrations C i → weakEquivalences C f → weakEquivalences C f' := by
  let _ : ModelCategory C := sourceModelCategory d hJ hSourceI hSourceJ e
  intro hi hf
  have hp := sourceModelCategory_isLeftProper d hJ hSourceI hSourceJ hI e
  exact hp.weakEquivalences_isStableUnderCobaseChangeAgainst_cofibrations.of_isPushout sq hi hf

end HomotopicalAlgebra.EnrichedProjective.MappedSources
