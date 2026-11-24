/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua
module

public import MathlibExt.CategoryTheory.Enriched.Monoidal.DayConvolution.ExternalRightModuleCorrespondence
public import MathlibExt.CategoryTheory.Monoidal.RightModuleFreeCoefficient

/-!
# Generic source-action isomorphisms of original right Day modules

The complete source square gives both arrows of the actual original stock
right-module isomorphism, retaining the chosen monoidal and coefficient data.
-/

@[expose] public section
set_option autoImplicit false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
noncomputable section
universe uV vV uI vI

open CategoryTheory Limits MonoidalCategory
open scoped MonoidalClosed

namespace CategoryTheory.EnrichedDayKernel.ExternalRightModule

attribute [local instance] MonoidalLeftAction.monoidalOppositeLeftAction

variable {V : Type uV} [Category.{vV} V] [MonoidalCategory V]
  [SymmetricCategory V] [MonoidalClosed V]
  {I : Type uI} [Category.{vI} I] [MonoidalCategory I]
  [EnrichedOrdinaryCategory V I] [HasColimitsOfSize.{uI, uI} V]
  (d : EnrichedMonoidalCategoryData V I) (S : EnrichedFunctor V I V)
  (L : EnrichedFunctor.LaxMonoidalData d
    (MonoidalClosed.enrichedMonoidalCategoryDataSelf V) S)

/-- Full source squares produce both arrows of the actual stock-module isomorphism. -/
def isoOfSourceComm :
    letI := EnrichedDayKernel.ColimitMonoidal.monoidalCategory d
    letI := EnrichedDayKernel.LaxMonoid.monObj d S L
    ∀ (M N : CommutativeModuleConversion.RightModule (⟨S⟩ : EnrichedFunctorCat V I))
      (e : M.X ≅ N.X), SourceComm d S M.X N.X M.action N.action e.hom → (M ≅ N) := by
  letI := EnrichedDayKernel.ColimitMonoidal.monoidalCategory d
  letI := EnrichedDayKernel.LaxMonoid.monObj d S L
  intro M N e h
  exact RightModuleFree.isoOfCarrier (⟨S⟩ : EnrichedFunctorCat V I) M N e
    ((comm_iff d S M.X N.X M.action N.action e.hom).1 h)

/-- The complete forward map is the supplied original diagram map. -/
theorem isoOfSourceComm_hom :
    letI := EnrichedDayKernel.ColimitMonoidal.monoidalCategory d
    letI := EnrichedDayKernel.LaxMonoid.monObj d S L
    ∀ (M N : CommutativeModuleConversion.RightModule (⟨S⟩ : EnrichedFunctorCat V I))
      (e : M.X ≅ N.X) (h : SourceComm d S M.X N.X M.action N.action e.hom),
      (isoOfSourceComm d S L M N e h).hom.hom = e.hom := by
  intro M N e h
  rfl

/-- The complete inverse map is the supplied original inverse diagram map. -/
theorem isoOfSourceComm_inv :
    letI := EnrichedDayKernel.ColimitMonoidal.monoidalCategory d
    letI := EnrichedDayKernel.LaxMonoid.monObj d S L
    ∀ (M N : CommutativeModuleConversion.RightModule (⟨S⟩ : EnrichedFunctorCat V I))
      (e : M.X ≅ N.X) (h : SourceComm d S M.X N.X M.action N.action e.hom),
      (isoOfSourceComm d S L M N e h).inv.hom = e.inv := by
  intro M N e h
  rfl

end CategoryTheory.EnrichedDayKernel.ExternalRightModule
