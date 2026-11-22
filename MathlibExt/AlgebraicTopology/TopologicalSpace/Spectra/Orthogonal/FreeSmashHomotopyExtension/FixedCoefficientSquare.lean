/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.TopologicalSpace.Spectra.Orthogonal.FreeSmashHomotopyExtension.SourceTransformationFields
import MathlibExt.AlgebraicTopology.TopologicalSpace.Spectra.Orthogonal.FreeSmashHomotopyExtension.FixedFreeMappingFamily

/-!
# Coefficient squares for free module mapping

For enriched modules over lax braided coefficients, identifies the coefficient map in the fixed-free mapping family with the module source map. A prescribed comparison square is therefore retained by the coefficient-variance functor.
-/

set_option autoImplicit false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency true
noncomputable section
universe uV vV uI vI
open CategoryTheory MonoidalCategory BraidedCategory Limits
open CategoryTheory.Enriched CategoryTheory.EnrichedFunctorCat
open scoped MonoidalClosed CategoryTheory.MonObj

namespace OrthogonalIGeneratorProbe.FixedCoefficient

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

theorem square (r : I) {K K' : V} (i : K ⟶ K') (N T T' : Module d S L)
    (e : (ModuleMappingR.functor d b S L B (FreeEvaluation.freeAt d S L r K)).obj N ≅ T)
    (e' : (ModuleMappingR.functor d b S L B (FreeEvaluation.freeAt d S L r K')).obj N ≅ T')
    (t : T' ⟶ T)
    (hc : ModuleMappingR.moduleSourceMap d b S L B
      (freeMap d S L ((Free.functor r).map i)) N ≫ e.hom = e'.hom ≫ t) :
    ((FixedFreeMapping.family d b S L B r).map i.op).app N ≫ e.hom =
      e'.hom ≫ t := by
  rw [FixedFreeMapping.map, SourceTransformationGetter.app]
  exact hc



end OrthogonalIGeneratorProbe.FixedCoefficient
