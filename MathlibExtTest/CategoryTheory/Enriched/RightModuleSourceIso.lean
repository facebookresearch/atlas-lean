/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.CategoryTheory.Enriched.RightModuleSourceIso
import Batteries.Tactic.Lint

/-! # Complete source-action right-module isomorphism clients -/

@[expose] public section
set_option autoImplicit false
noncomputable section
universe uV vV uI vI

open CategoryTheory Limits MonoidalCategory
open scoped MonoidalClosed

namespace CategoryTheory.EnrichedDayKernel.ExternalRightModule.Clients

attribute [local instance] MonoidalLeftAction.monoidalOppositeLeftAction

variable {V : Type uV} [Category.{vV} V] [MonoidalCategory V]
  [SymmetricCategory V] [MonoidalClosed V]
  {I : Type uI} [Category.{vI} I] [MonoidalCategory I]
  [EnrichedOrdinaryCategory V I] [HasColimitsOfSize.{uI, uI} V]
  (d : EnrichedMonoidalCategoryData V I) (S : EnrichedFunctor V I V)
  (L : EnrichedFunctor.LaxMonoidalData d
    (MonoidalClosed.enrichedMonoidalCategoryDataSelf V) S)

/-- Both complete maps of the original supplied isomorphism are retained for arbitrary source modules. -/
theorem originalMaps :
    letI := ColimitMonoidal.monoidalCategory d
    letI := LaxMonoid.monObj d S L
    ∀ (M N : CommutativeModuleConversion.RightModule (⟨S⟩ : EnrichedFunctorCat V I))
      (e : M.X ≅ N.X) (h : SourceComm d S M.X N.X M.action N.action e.hom),
      (isoOfSourceComm d S L M N e h).hom.hom = e.hom ∧
        (isoOfSourceComm d S L M N e h).inv.hom = e.inv := by
  intro M N e h
  exact ⟨isoOfSourceComm_hom d S L M N e h, isoOfSourceComm_inv d S L M N e h⟩

/-- Both resulting arrows are actual inverse morphisms on the unchanged original module carriers. -/
theorem originalInverseLaws :
    letI := ColimitMonoidal.monoidalCategory d
    letI := LaxMonoid.monObj d S L
    ∀ (M N : CommutativeModuleConversion.RightModule (⟨S⟩ : EnrichedFunctorCat V I))
      (e : M.X ≅ N.X) (h : SourceComm d S M.X N.X M.action N.action e.hom),
      (isoOfSourceComm d S L M N e h).hom ≫ (isoOfSourceComm d S L M N e h).inv = 𝟙 M ∧
        (isoOfSourceComm d S L M N e h).inv ≫ (isoOfSourceComm d S L M N e h).hom = 𝟙 N := by
  intro M N e h
  exact ⟨(isoOfSourceComm d S L M N e h).hom_inv_id, (isoOfSourceComm d S L M N e h).inv_hom_id⟩

end CategoryTheory.EnrichedDayKernel.ExternalRightModule.Clients

#print axioms CategoryTheory.EnrichedDayKernel.ExternalRightModule.isoOfSourceComm
#print axioms CategoryTheory.EnrichedDayKernel.ExternalRightModule.isoOfSourceComm_hom
#print axioms CategoryTheory.EnrichedDayKernel.ExternalRightModule.isoOfSourceComm_inv
#print axioms CategoryTheory.EnrichedDayKernel.ExternalRightModule.Clients.originalMaps
#print axioms CategoryTheory.EnrichedDayKernel.ExternalRightModule.Clients.originalInverseLaws

#lint only unusedArguments in MathlibExt.CategoryTheory.Enriched.RightModuleSourceIso
