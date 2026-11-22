/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.TopologicalSpace.Spectra.Orthogonal.FreeSmashHomotopyExtension.MappingBifunctorFields
import Mathlib.CategoryTheory.EqToHom
import Mathlib.CategoryTheory.Adjunction.Parametrized

/-!
# Source families for enriched module mapping

Given a coefficient functor into enriched modules, constructs the contravariant family of module mapping functors. Its object and morphism fields agree with composition through the module mapping bifunctor.
-/

set_option autoImplicit false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency true
noncomputable section
universe uV vV uI vI
open CategoryTheory MonoidalCategory BraidedCategory Limits
open CategoryTheory.Enriched CategoryTheory.EnrichedFunctorCat
open scoped MonoidalClosed CategoryTheory.MonObj

namespace OrthogonalIGeneratorProbe.LiteralMapping

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

/-- The contravariant module-Hom family defined explicitly by the objects and maps of the source
functor `F`. -/
def functor (F : V ⥤ Module d S L) : Vᵒᵖ ⥤ (Module d S L ⥤ Module d S L) where
  obj K := ModuleMappingR.functor d b S L B (F.obj K.unop)
  map i := ModuleMappingR.moduleSourceNatTrans d b S L B (F.map i.unop)
  map_id K := by
    apply NatTrans.ext
    funext N
    change ModuleMappingR.moduleSourceMap d b S L B (F.map (𝟙 K.unop)) N = 𝟙 _
    rw [F.map_id, ModuleMappingR.moduleSourceMap_id]
  map_comp i j := by
    apply NatTrans.ext
    funext N
    change ModuleMappingR.moduleSourceMap d b S L B (F.map (j.unop ≫ i.unop)) N =
      ModuleMappingR.moduleSourceMap d b S L B (F.map i.unop) N ≫
        ModuleMappingR.moduleSourceMap d b S L B (F.map j.unop) N
    rw [F.map_comp, ModuleMappingR.moduleSourceMap_comp]

theorem obj (F : V ⥤ Module d S L) (K : Vᵒᵖ) :
    (functor d b S L B F).obj K = ModuleMappingR.functor d b S L B (F.obj K.unop) := rfl

theorem map (F : V ⥤ Module d S L) {K K' : Vᵒᵖ} (i : K ⟶ K') :
    (functor d b S L B F).map i =
      ModuleMappingR.moduleSourceNatTrans d b S L B (F.map i.unop) := rfl

theorem whole_eq (F : V ⥤ Module d S L) :
    functor d b S L B F = F.op ⋙ ModuleMappingR.moduleBifunctor d b S L B := by
  rfl






end OrthogonalIGeneratorProbe.LiteralMapping
