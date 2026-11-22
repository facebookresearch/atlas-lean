/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.CategoryTheory.EqToHom
import MathlibExt.AlgebraicTopology.TopologicalSpace.Spectra.Orthogonal.FreeSmashHomotopyExtension.OriginalFreeMappingFamily
import MathlibExt.AlgebraicTopology.TopologicalSpace.Spectra.Orthogonal.FreeSmashHomotopyExtension.OriginalFreeFunctor
import MathlibExt.AlgebraicTopology.TopologicalSpace.Spectra.Orthogonal.FreeSmashHomotopyExtension.OriginalMappingFamily
import MathlibExt.AlgebraicTopology.TopologicalSpace.Spectra.Orthogonal.FreeSmashHomotopyExtension.FreeMappingFields
import Mathlib.CategoryTheory.Adjunction.Parametrized

/-!
# Free-source module-Hom families

With the supplied enriched monoidal module data, internal module Hom with a free source at r
forms a functor contravariant in its coefficient. The object and map formulas identify this
family with the existing free-mapping functor. Coefficient maps act through the
corresponding free-module source maps.
-/

set_option autoImplicit false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency true
noncomputable section
universe uV vV uI vI
open CategoryTheory MonoidalCategory BraidedCategory Limits
open CategoryTheory.Enriched CategoryTheory.EnrichedFunctorCat
open scoped MonoidalClosed CategoryTheory.MonObj

universe uAuxA vAuxA uAuxD vAuxD

private def functorFromFields {A : Type uAuxA} [Category.{vAuxA} A]
    {D : Type uAuxD} [Category.{vAuxD} D]
    (F : A ⥤ D) (o : A → D) (ho : F.obj = o)
    (m : ∀ {X Y : A}, (X ⟶ Y) → (o X ⟶ o Y))
    (hm : ∀ {X Y : A} (f : X ⟶ Y), HEq (F.map f) (m f)) : A ⥤ D where
  obj := o
  map := m
  map_id X := by
    cases ho
    exact (eq_of_heq (hm (𝟙 X))).symm.trans (F.map_id X)
  map_comp f g := by
    cases ho
    have hf := eq_of_heq (hm f)
    have hg := eq_of_heq (hm g)
    have hfg := eq_of_heq (hm (f ≫ g))
    exact hfg.symm.trans ((F.map_comp f g).trans (by rw [hf, hg]))

private theorem functorFromFields_eq {A : Type uAuxA} [Category.{vAuxA} A]
    {D : Type uAuxD} [Category.{vAuxD} D]
    (F : A ⥤ D) (o : A → D) (ho : F.obj = o)
    (m : ∀ {X Y : A}, (X ⟶ Y) → (o X ⟶ o Y))
    (hm : ∀ {X Y : A} (f : X ⟶ Y), HEq (F.map f) (m f)) :
    functorFromFields F o ho m hm = F := by
  cases ho
  exact Functor.hext (fun _ => rfl) (fun _ _ f => (hm f).symm)

namespace OrthogonalIGeneratorProbe.FixedFreeMapping

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

/-- Internal module-Hom endofunctors with free source at `r` and coefficient `K.unop`. -/
def objects (r : I) (K : Vᵒᵖ) : Module d S L ⥤ Module d S L :=
  ModuleMappingR.functor d b S L B (FreeEvaluation.freeAt d S L r K.unop)

theorem objects_eq (r : I) :
    (LiteralFreeMapping.family d b S L B r).obj = objects d b S L B r :=
  funext (LiteralFreeMapping.obj d b S L B r)

/-- Contravariant coefficient maps for the free-source module-Hom family. -/
def maps (r : I) {K K' : Vᵒᵖ} (i : K ⟶ K') :
    objects d b S L B r K ⟶ objects d b S L B r K' :=
  ModuleMappingR.moduleSourceNatTrans d b S L B
    (freeMap d S L ((Free.functor r).map i.unop))

theorem maps_heq (r : I) {K K' : Vᵒᵖ} (i : K ⟶ K') :
    HEq ((LiteralFreeMapping.family d b S L B r).map i) (maps d b S L B r i) :=
  heq_of_eq (LiteralFreeMapping.map d b S L B r i)

/-- The free-source mapping family assembled from its explicit object and coefficient-map fields. -/
def family (r : I) :=
  functorFromFields (LiteralFreeMapping.family d b S L B r)
    (objects d b S L B r) (objects_eq d b S L B r)
    (fun i => maps d b S L B r i) (fun i => maps_heq d b S L B r i)

theorem whole_eq (r : I) : family d b S L B r = FreeMappingGetters.functor d b S L B r :=
  (functorFromFields_eq _ _ _ _ _).trans (LiteralFreeMapping.whole_eq d b S L B r)

theorem obj (r : I) (K : Vᵒᵖ) :
    (family d b S L B r).obj K =
      ModuleMappingR.functor d b S L B (FreeEvaluation.freeAt d S L r K.unop) := rfl

theorem map (r : I) {K K' : Vᵒᵖ} (i : K ⟶ K') :
    (family d b S L B r).map i =
      ModuleMappingR.moduleSourceNatTrans d b S L B
        (freeMap d S L ((Free.functor r).map i.unop)) := rfl








end OrthogonalIGeneratorProbe.FixedFreeMapping
