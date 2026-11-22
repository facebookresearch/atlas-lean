/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.ModelCategory.OriginalEnrichedProjective
import MathlibExt.CategoryTheory.Enriched.EndOrdinaryEnrichment
import MathlibExt.AlgebraicTopology.ModelCategory.FunctorInjective.OriginalSmithModel

/-!
# Original diagram model constructions and their compatible mapping ends

The coefficient model, original generating families and source hypotheses
construct the genuine enriched projective model. All five classes, the two
complete original functorial factor records and the actual weighted-end
ordinary enrichment are retained. The ordinary injective construction is
the existing original Smith factory with its selected index equivalence.
-/

set_option autoImplicit false
noncomputable section

universe w uA uV vV uJ vJ

open CategoryTheory Limits MorphismProperty MonoidalCategory
open scoped MonoidalClosed

namespace HomotopicalAlgebra.OriginalDiagramModels

section Enriched

variable {V : Type uV} [Category.{vV} V] [MonoidalCategory V]
  [SymmetricCategory V] [MonoidalClosed V] [ModelCategory V]
  {A : Type uA} [EnrichedCategory V A]
  {κ : Cardinal.{w}} [Fact κ.IsRegular] [OrderBot κ.ord.ToType]
  [Small.{w} A] [LocallySmall.{w} V] [HasColimitsOfSize.{w, w} V]
  [HasProducts.{uA} V] [HasEqualizers V]
  (d : CofibrantGenerationData V κ)
  (s : OriginalEnrichedProjective.SourceConditions (A := A) d)

/-- The source data construct the same actual model, all five classes, original factors and end enrichment. -/
theorem constructs :
    letI : ModelCategory (EnrichedFunctorCat V A) :=
      EnrichedProjective.modelCategory d s.I_tensor s.J_tensor s.I_source s.J_source
    ∃ (g : CofibrantGenerationData (EnrichedFunctorCat V A) κ)
      (c : FunctorialFactorizationData (cofibrations (EnrichedFunctorCat V A))
        (trivialFibrations (EnrichedFunctorCat V A)))
      (f : FunctorialFactorizationData (trivialCofibrations (EnrichedFunctorCat V A))
        (fibrations (EnrichedFunctorCat V A)))
      (e : EnrichedOrdinaryCategory V (EnrichedFunctorCat V A)),
      g = OriginalEnrichedProjective.generationData d s ∧
      c = OriginalEnrichedProjective.cofibrantFactorizationData d s ∧
      f = OriginalEnrichedProjective.fibrantFactorizationData d s ∧
      e = EnrichedFunctorCat.EndOrdinaryEnrichment.enrichment (V := V) (A := A) ∧
      weakEquivalences (EnrichedFunctorCat V A) =
        EvaluationTransfer.evaluationProperty (fun a : A => EnrichedFunctorCat.evaluation a)
          (weakEquivalences V) ∧
      cofibrations (EnrichedFunctorCat V A) = (EnrichedProjective.generators (A := A) d.I).rlp.llp ∧
      fibrations (EnrichedFunctorCat V A) =
        EvaluationTransfer.evaluationProperty (fun a : A => EnrichedFunctorCat.evaluation a)
          (fibrations V) ∧
      trivialCofibrations (EnrichedFunctorCat V A) =
        (EnrichedProjective.generators (A := A) d.J).rlp.llp ∧
      trivialFibrations (EnrichedFunctorCat V A) =
        EvaluationTransfer.evaluationProperty (fun a : A => EnrichedFunctorCat.evaluation a)
          (trivialFibrations V) ∧
      ∀ a : A, (EnrichedFunctorCat.Free.adjunction (V := V) a).IsQuillenAdjunction := by
  let _ : ModelCategory (EnrichedFunctorCat V A) :=
    EnrichedProjective.modelCategory d s.I_tensor s.J_tensor s.I_source s.J_source
  exact ⟨OriginalEnrichedProjective.generationData d s,
    OriginalEnrichedProjective.cofibrantFactorizationData d s,
    OriginalEnrichedProjective.fibrantFactorizationData d s,
    EnrichedFunctorCat.EndOrdinaryEnrichment.enrichment (V := V) (A := A), rfl, rfl, rfl, rfl,
    EnrichedProjective.weakEquivalences_eq d s.I_tensor s.J_tensor s.I_source s.J_source,
    EnrichedProjective.cofibrations_eq d s.I_tensor s.J_tensor s.I_source s.J_source,
    EnrichedProjective.fibrations_eq d s.I_tensor s.J_tensor s.I_source s.J_source,
    EnrichedProjective.trivialCofibrations_eq d s.I_tensor s.J_tensor s.I_source s.J_source,
    EnrichedProjective.trivialFibrations_eq d s.I_tensor s.J_tensor s.I_source s.J_source,
    EnrichedProjective.freeAtEvaluation_isQuillenAdjunction d
      s.I_tensor s.J_tensor s.I_source s.J_source⟩

end Enriched

section OrdinaryInjective

variable {J : Type uJ} [Category.{vJ} J]
  {V : Type uV} [Category.{vV} V] [ModelCategory V]
  {κ : Cardinal.{w}} [Fact κ.IsRegular] [OrderBot κ.ord.ToType]
  (d : CofibrantGenerationData V κ) (κLP : Cardinal.{w}) [Fact κLP.IsRegular]
  [IsCardinalLocallyPresentable V κLP] (s : Functor.EssentialIndexData.{w} J V)

/-- Reuse the unchanged original combinatorial injective factory and its entire factor records. -/
theorem injectiveConstructs :
    letI : ModelCategory (J ⥤ V) := FunctorInjective.originalSmithModelCategory d κLP s
    ∃ (c : FunctorialFactorizationData (cofibrations (J ⥤ V)) (trivialFibrations (J ⥤ V)))
      (f : FunctorialFactorizationData (trivialCofibrations (J ⥤ V)) (fibrations (J ⥤ V))),
      c = FunctorInjective.originalSmithCofibrantFactorizationData d κLP s ∧
      f = FunctorInjective.originalSmithFibrantFactorizationData d κLP s ∧
      weakEquivalences (J ⥤ V) = (weakEquivalences V).functorCategory J ∧
      cofibrations (J ⥤ V) = (cofibrations V).functorCategory J ∧
      trivialCofibrations (J ⥤ V) = (trivialCofibrations V).functorCategory J ∧
      fibrations (J ⥤ V) = ((trivialCofibrations V).functorCategory J).rlp ∧
      trivialFibrations (J ⥤ V) = ((cofibrations V).functorCategory J).rlp := by
  let _ : ModelCategory (J ⥤ V) := FunctorInjective.originalSmithModelCategory d κLP s
  exact ⟨FunctorInjective.originalSmithCofibrantFactorizationData d κLP s,
    FunctorInjective.originalSmithFibrantFactorizationData d κLP s, rfl, rfl,
    FunctorInjective.originalInjectiveModel_fiveClasses d κLP s⟩

end OrdinaryInjective

end HomotopicalAlgebra.OriginalDiagramModels
