/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.TopologicalSpace.Spectra.Orthogonal.FreeSmashHomotopyExtension.FreeMappingFields
import Mathlib.CategoryTheory.EqToHom
import Mathlib.CategoryTheory.Adjunction.Parametrized

/-!
# Normalized free-source module Hom families

For a symmetric monoidal closed base and an enriched symmetric monoidal
index with the stated colimits, products and equalizers, the free-source
module Hom family has an explicit object formula. It uses the supplied
enriched lax monoidal and braided data and takes module Hom from the free
module at the chosen label and coefficient. The normalized whole functor
equals `FreeMappingGetters.functor`, and its contravariant coefficient maps
are heterogeneously equal to the corresponding module-source transformations.
-/

set_option autoImplicit false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency true
noncomputable section
universe uV vV uI vI
open CategoryTheory MonoidalCategory BraidedCategory Limits
open CategoryTheory.Enriched CategoryTheory.EnrichedFunctorCat
open scoped MonoidalClosed CategoryTheory.MonObj

universe uCopyA vCopyA uCopyD vCopyD

private theorem copyObject_eq {A : Type uCopyA} [Category.{vCopyA} A]
    {D : Type uCopyD} [Category.{vCopyD} D] (F : A ⥤ D) (o : A → D) (h : F.obj = o) :
    F.copyObj o (fun X => eqToIso (congrFun h X)) = F := by
  cases h
  exact CategoryTheory.Functor.ext_of_iso
    (F.isoCopyObj F.obj (fun X => eqToIso (congrFun (rfl : F.obj = F.obj) X))).symm
    (fun _ => rfl) (fun _ => rfl)

private theorem copyObject_map_heq {A : Type uCopyA} [Category.{vCopyA} A]
    {D : Type uCopyD} [Category.{vCopyD} D] (F : A ⥤ D) (o : A → D) (h : F.obj = o)
    {X Y : A} (f : X ⟶ Y) :
    HEq ((F.copyObj o (fun Z => eqToIso (congrFun h Z))).map f) (F.map f) := by
  cases h
  exact heq_of_eq (by simp [Functor.copyObj])

namespace OrthogonalIGeneratorProbe.NormalizedMapping

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

/-- The module-Hom endofunctor with the explicit free module at label `r` and coefficient
`K.unop`. -/
def objectFunction (r : I) (K : Vᵒᵖ) : Module d S L ⥤ Module d S L :=
  ModuleMappingR.functor d b S L B (FreeEvaluation.freeAt d S L r K.unop)

theorem objectFunction_eq (r : I) :
    (FreeMappingGetters.functor d b S L B r).obj = objectFunction d b S L B r := by
  funext K
  exact FreeMappingGetters.obj d b S L B r K.unop

/-- The free-source module-Hom family with its object field replaced by the equal explicit
module-Hom formula. -/
def functor (r : I) :=
  (FreeMappingGetters.functor d b S L B r).copyObj (objectFunction d b S L B r)
    (fun K => eqToIso (congrFun (objectFunction_eq d b S L B r) K))

theorem whole_eq (r : I) : functor d b S L B r = FreeMappingGetters.functor d b S L B r :=
  copyObject_eq (FreeMappingGetters.functor d b S L B r)
    (objectFunction d b S L B r) (objectFunction_eq d b S L B r)

theorem obj (r : I) (K : Vᵒᵖ) :
    (functor d b S L B r).obj K = objectFunction d b S L B r K := rfl

theorem map_heq (r : I) {K K' : V} (i : K ⟶ K') :
    HEq ((functor d b S L B r).map i.op)
      (ModuleMappingR.moduleSourceNatTrans d b S L B
        (freeMap d S L ((Free.functor r).map i))) :=
  (copyObject_map_heq
    (FreeMappingGetters.functor d b S L B r) (objectFunction d b S L B r)
    (objectFunction_eq d b S L B r) i.op).trans
      (FreeMappingGetters.map_heq d b S L B r i)







end OrthogonalIGeneratorProbe.NormalizedMapping
