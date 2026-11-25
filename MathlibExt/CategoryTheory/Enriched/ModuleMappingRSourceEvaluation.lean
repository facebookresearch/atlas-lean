/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua

module
public import MathlibExt.CategoryTheory.Enriched.ModuleMappingRAdjunctionSourceFactories
public import MathlibExt.CategoryTheory.Monoidal.RightModuleMappingEndEvaluation

/-!
# Original source evaluation of the literal translated mapping equalizer

The source inclusion and evaluation are the original generic right-module
maps in their selected Day category. The raw identifications below retain
the entire translated action equalizer and the original Day evaluation.
They precede the commutative module-valued output construction.
-/

@[expose] public section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section

universe uV vV uI vI

open CategoryTheory Limits MonoidalCategory BraidedCategory
open scoped MonoidalClosed CategoryTheory.MonObj

namespace CategoryTheory.Enriched.ModuleMappingR

open EnrichedFunctorCat EnrichedDayKernel

attribute [local instance] Enriched.prodCategory ColimitMonoidal.smallestColimits
attribute [local instance] SphereModuleMappingEnd.moduleCategory
attribute [local instance] MonoidalLeftAction.monoidalOppositeLeftAction

variable {V : Type uV} [Category.{vV} V] [MonoidalCategory V]
  [SymmetricCategory V] [MonoidalClosed V]
  {I : Type uI} [Category.{vI} I] [MonoidalCategory I] [SymmetricCategory I]
  [EnrichedOrdinaryCategory V I]
  [HasColimitsOfSize.{uI, uI} V] [HasProducts.{uI} V] [HasEqualizers V]
  (d : EnrichedMonoidalCategoryData V I)
  (b : EnrichedBraidedMonoidalCategoryData V I d)
  (S : EnrichedFunctor V I V)
  (L : EnrichedFunctor.LaxMonoidalData d
    (MonoidalClosed.enrichedMonoidalCategoryDataSelf V) S)

/-- The original source inclusion is the full literal translated action equalizer inclusion. -/
theorem sourceι_eq (M N : Module d S L) :
    letI := ColimitMonoidal.monoidalCategory d
    letI := BraidingMonoidal.symmetricCategory d b
    letI := Closed.monoidalClosed d
    letI : MonObj (⟨S⟩ : EnrichedFunctorCat V I) := LaxMonoid.monObj d S L
    RightModuleMappingEnd.ι (⟨S⟩ : EnrichedFunctorCat V I) M N =
      ι d b S L M N := rfl

/-- The actual source evaluation retains the whole literal equalizer and Day descent. -/
theorem sourceEvaluation_eq (M N : Module d S L) :
    letI := ColimitMonoidal.monoidalCategory d
    letI := BraidingMonoidal.symmetricCategory d b
    letI := Closed.monoidalClosed d
    letI : MonObj (⟨S⟩ : EnrichedFunctorCat V I) := LaxMonoid.monObj d S L
    RightModuleMappingEnd.evaluation (⟨S⟩ : EnrichedFunctorCat V I) M N =
      (SphereModuleMappingEnd.diagram d S L M ◁ ι d b S L M N) ≫
        Closed.evaluation d (SphereModuleMappingEnd.diagram d S L M)
          (SphereModuleMappingEnd.diagram d S L N) := by
  let : MonoidalCategory (EnrichedFunctorCat V I) := ColimitMonoidal.monoidalCategory d
  let : SymmetricCategory (EnrichedFunctorCat V I) := BraidingMonoidal.symmetricCategory d b
  let : MonoidalClosed (EnrichedFunctorCat V I) := Closed.monoidalClosed d
  let : MonObj (⟨S⟩ : EnrichedFunctorCat V I) := LaxMonoid.monObj d S L
  rw [RightModuleMappingEnd.evaluation, MonoidalClosed.uncurry_eq]
  have hi := sourceι_eq d b S L M N
  have he := selectedEvaluation_eq d (SphereModuleMappingEnd.diagram d S L M)
    (SphereModuleMappingEnd.diagram d S L N)
  change (SphereModuleMappingEnd.diagram d S L M ◁
      RightModuleMappingEnd.ι (⟨S⟩ : EnrichedFunctorCat V I) M N) ≫
        (ihom.ev (SphereModuleMappingEnd.diagram d S L M)).app
          (SphereModuleMappingEnd.diagram d S L N) = _
  rw [hi]
  exact congrArg (fun ev => (SphereModuleMappingEnd.diagram d S L M ◁ ι d b S L M N) ≫ ev) he

/-- The source evaluation is the whole original inverse Day transpose of its inclusion. -/
theorem sourceEvaluation_untranspose (M N : Module d S L) :
    letI := ColimitMonoidal.monoidalCategory d
    letI := BraidingMonoidal.symmetricCategory d b
    letI := Closed.monoidalClosed d
    letI : MonObj (⟨S⟩ : EnrichedFunctorCat V I) := LaxMonoid.monObj d S L
    RightModuleMappingEnd.evaluation (⟨S⟩ : EnrichedFunctorCat V I) M N =
      Closed.untranspose d (SphereModuleMappingEnd.diagram d S L M)
        (diagram d b S L M N) (SphereModuleMappingEnd.diagram d S L N)
        (ι d b S L M N) := by
  let : MonoidalCategory (EnrichedFunctorCat V I) := ColimitMonoidal.monoidalCategory d
  let : SymmetricCategory (EnrichedFunctorCat V I) := BraidingMonoidal.symmetricCategory d b
  let : MonoidalClosed (EnrichedFunctorCat V I) := Closed.monoidalClosed d
  let : MonObj (⟨S⟩ : EnrichedFunctorCat V I) := LaxMonoid.monObj d S L
  rw [RightModuleMappingEnd.evaluation, sourceι_eq]
  change ((Closed.adjunction d (SphereModuleMappingEnd.diagram d S L M)).homEquiv
      (diagram d b S L M N) (SphereModuleMappingEnd.diagram d S L N)).symm
        (ι d b S L M N) = _
  exact Closed.adjunction_homEquiv_symm d (SphereModuleMappingEnd.diagram d S L M)
    (diagram d b S L M N) (SphereModuleMappingEnd.diagram d S L N) (ι d b S L M N)

/-- Every source evaluation generator keeps both original indices and its entire output weight. -/
@[reassoc]
theorem sourceEvaluation_gen (M N : Module d S L) (κ j c : I) :
    letI := ColimitMonoidal.monoidalCategory d
    letI := BraidingMonoidal.symmetricCategory d b
    letI := Closed.monoidalClosed d
    letI : MonObj (⟨S⟩ : EnrichedFunctorCat V I) := LaxMonoid.monObj d S L
    EnrichedDayKernel.gen d.tensorEnrichedFunctor
        (SphereModuleMappingEnd.diagram d S L M).toEnrichedFunctor
        (diagram d b S L M N).toEnrichedFunctor κ (j, c) ≫
      component (RightModuleMappingEnd.evaluation (⟨S⟩ : EnrichedFunctorCat V I) M N) κ =
      (𝟙 ((j ⊗ c) ⟶[V] κ) ⊗ₘ MonoidalClosed.uncurry (π d b S L M N c j)) ≫
        (β_ ((j ⊗ c) ⟶[V] κ)
          ((SphereModuleMappingEnd.diagram d S L N).toEnrichedFunctor.obj (j ⊗ c))).hom ≫
        MonoidalClosed.uncurry
          ((SphereModuleMappingEnd.diagram d S L N).toEnrichedFunctor.map (j ⊗ c) κ) := by
  let : MonoidalCategory (EnrichedFunctorCat V I) := ColimitMonoidal.monoidalCategory d
  let : SymmetricCategory (EnrichedFunctorCat V I) := BraidingMonoidal.symmetricCategory d b
  let : MonoidalClosed (EnrichedFunctorCat V I) := Closed.monoidalClosed d
  let : MonObj (⟨S⟩ : EnrichedFunctorCat V I) := LaxMonoid.monObj d S L
  rw [sourceEvaluation_untranspose]
  dsimp only [π, valueι]
  exact Closed.untranspose_gen d
    (SphereModuleMappingEnd.diagram d S L M) (diagram d b S L M N)
    (SphereModuleMappingEnd.diagram d S L N) (ι d b S L M N) κ (j, c)

/-- Every identity-weight source point evaluates its literal j tensor c projection. -/
@[reassoc]
theorem sourceEvaluation_point (M N : Module d S L) (j c : I) :
    letI := ColimitMonoidal.monoidalCategory d
    letI := BraidingMonoidal.symmetricCategory d b
    letI := Closed.monoidalClosed d
    letI : MonObj (⟨S⟩ : EnrichedFunctorCat V I) := LaxMonoid.monObj d S L
    Generators.point d.tensorEnrichedFunctor
        (SphereModuleMappingEnd.diagram d S L M).toEnrichedFunctor
        (diagram d b S L M N).toEnrichedFunctor (j, c) ≫
      component (RightModuleMappingEnd.evaluation (⟨S⟩ : EnrichedFunctorCat V I) M N)
        (j ⊗ c) = MonoidalClosed.uncurry (π d b S L M N c j) := by
  let : MonoidalCategory (EnrichedFunctorCat V I) := ColimitMonoidal.monoidalCategory d
  let : SymmetricCategory (EnrichedFunctorCat V I) := BraidingMonoidal.symmetricCategory d b
  let : MonoidalClosed (EnrichedFunctorCat V I) := Closed.monoidalClosed d
  let : MonObj (⟨S⟩ : EnrichedFunctorCat V I) := LaxMonoid.monObj d S L
  rw [sourceEvaluation_untranspose]
  have h := Closed.transpose_untranspose d (SphereModuleMappingEnd.diagram d S L M)
    (diagram d b S L M N) (SphereModuleMappingEnd.diagram d S L N) (ι d b S L M N)
  have hp := congrArg (fun t => component t c ≫ Closed.π d
    (SphereModuleMappingEnd.diagram d S L M) (SphereModuleMappingEnd.diagram d S L N) c j) h
  rw [Closed.transpose_component_π] at hp
  apply MonoidalClosed.curry_injective
  rw [MonoidalClosed.curry_uncurry]
  exact hp

end CategoryTheory.Enriched.ModuleMappingR
