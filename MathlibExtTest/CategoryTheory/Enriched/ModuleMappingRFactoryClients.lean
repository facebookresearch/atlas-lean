/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Copyright (c) 2026 Tsutomu Okano. All rights reserved.
Authors: Tsutomu Okano <toskua@meta.com>
-/

import MathlibExt.CategoryTheory.Enriched.ModuleMappingRAdjunctionSourceFactories

/-!
# Clients of the translated Mapping_R structure factories

Select the monoidal, symmetric, and closed module structures from arbitrary enriched
source data. Their public equations identify whole internal Hom values, module arrows,
and adjunction comparisons while the closed structure constructor remains irreducible.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
noncomputable section

open CategoryTheory Limits MonoidalCategory BraidedCategory
open CategoryTheory.Enriched
open CategoryTheory.EnrichedDayKernel
open CategoryTheory.EnrichedFunctorCat
open CategoryTheory.Enriched.ModuleMappingR
open scoped MonoidalClosed CategoryTheory.MonObj

namespace MathlibExtTest.ModuleMappingRFactoryClients

universe uV vV uI vI

attribute [local instance] Enriched.prodCategory ColimitMonoidal.smallestColimits
attribute [local instance] SphereModuleMappingEnd.moduleCategory
attribute [local instance] MonoidalLeftAction.monoidalOppositeLeftAction
attribute [local irreducible] Closed.monoidalClosed moduleClosed

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
  (B : EnrichedFunctor.LaxBraidedData L)

/-- The selected internal Hom is the entire translated action-equalizer functor. -/
theorem selected_internal_hom (M : Module d S L) :
    letI := moduleMonoidal d b S L B
    letI := moduleClosed d b S L B
    ihom M = functor d b S L B M :=
  moduleClosed_ihom d b S L B M

/-- Each inferred internal Hom value retains the whole original equalizer module and action. -/
theorem selected_mapping_value (M N : Module d S L) :
    letI := moduleMonoidal d b S L B
    letI := moduleClosed d b S L B
    (ihom M).obj N = moduleObject d b S L B M N :=
  (congrArg (fun F => F.obj N) (moduleClosed_ihom d b S L B M)).trans
    (functor_obj d b S L B M N)

/-- The whole internal Hom comparison retains every target arrow without reducing the constructor. -/
theorem selected_mapping_arrow (M : Module d S L) {N N' : Module d S L} (g : N ⟶ N') :
    letI := moduleMonoidal d b S L B
    letI := moduleClosed d b S L B
    (ihom M).map g ≫ (eqToIso (moduleClosed_ihom d b S L B M)).hom.app N' =
      (eqToIso (moduleClosed_ihom d b S L B M)).hom.app N ≫ (functor d b S L B M).map g := by
  let := moduleMonoidal d b S L B
  let := moduleClosed d b S L B
  exact (eqToIso (moduleClosed_ihom d b S L B M)).hom.naturality g

/-- The inferred closed adjunction recovers every complete arrow from the selected tensor. -/
theorem selected_closed_hom_recovery (M N P : Module d S L) :
    letI := moduleMonoidal d b S L B
    letI := moduleClosed d b S L B
    ∀ (h : M ⊗ N ⟶ P),
      ((ihom.adjunction M).homEquiv N P).symm ((ihom.adjunction M).homEquiv N P h) = h := by
  let := moduleMonoidal d b S L B
  let := moduleClosed d b S L B
  intro h
  exact Equiv.symm_apply_apply _ h

/-- The source counit factors through the whole source/stock comparison and stock evaluation. -/
theorem selected_counit_comparison (M N : Module d S L) :
    letI := moduleMonoidal d b S L B
    (leftAdjunction d b S L B M).counit.app N =
      (tensorLeft M).map ((comparisonNatIso d b S L B M).hom.app N) ≫
        (stockLeftAdjunction d b S L B M).counit.app N :=
  leftAdjunction_counit_comparisonNatIso d b S L B M N

/-- Symmetry is inferred after installing the selected module structure constructors. -/
theorem selected_braid_involution (M N : Module d S L) :
    letI := moduleMonoidal d b S L B
    letI := moduleSymmetric d b S L B
    (β_ M N).hom ≫ (β_ N M).hom = 𝟙 (M ⊗ N) := by
  let := moduleMonoidal d b S L B
  let := moduleSymmetric d b S L B
  exact SymmetricCategory.symmetry M N

end MathlibExtTest.ModuleMappingRFactoryClients
