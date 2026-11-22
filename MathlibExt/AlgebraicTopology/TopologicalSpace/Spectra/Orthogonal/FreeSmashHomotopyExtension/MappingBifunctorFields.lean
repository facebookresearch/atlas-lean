/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.TopologicalSpace.Spectra.Orthogonal.FreeSmashHomotopyExtension.NativeOutputCoefficient

/-!
# Components of the module mapping bifunctor

Fixing the source of the module mapping bifunctor gives the corresponding internal
module-Hom endofunctor. A morphism in the opposite source category acts by the specified
source-precomposition natural transformation, for the same enriched monoidal and braided
module data.
-/

set_option autoImplicit false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency true
noncomputable section
universe uV vV uI vI
open CategoryTheory MonoidalCategory BraidedCategory Limits
open CategoryTheory.Enriched CategoryTheory.EnrichedFunctorCat
open scoped MonoidalClosed CategoryTheory.MonObj

namespace OrthogonalIGeneratorProbe.BifGetters

attribute [local instance] Enriched.prodCategory EnrichedDayKernel.ColimitMonoidal.smallestColimits
  SphereModuleMappingEnd.moduleCategory MonoidalLeftAction.monoidalOppositeLeftAction

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

open EnrichedDayKernel ModuleMappingR

variable (B : EnrichedFunctor.LaxBraidedData L)

theorem obj (M : Module d S L) :
    (ModuleMappingR.moduleBifunctor d b S L B).obj (Opposite.op M) =
      ModuleMappingR.functor d b S L B M := by
  rfl

theorem map {M M' : Module d S L} (f : M' ⟶ M) :
    (ModuleMappingR.moduleBifunctor d b S L B).map f.op =
      ModuleMappingR.moduleSourceNatTrans d b S L B f := by
  rfl




end OrthogonalIGeneratorProbe.BifGetters
