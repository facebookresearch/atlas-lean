/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.TopologicalSpace.Spectra.Orthogonal.FreeSmashHomotopyExtension.FreeMappingCoefficients

/-!
# Translated coefficients of free-source mapping outputs

Coefficient precomposition commutes with the translated internal-Hom value isomorphisms.
Given output isomorphisms and their specified object and component formulas, this yields the
entire output-coefficient square for the module mapping functor. The equations retain the
same free source, coefficient map and output morphism.
-/

set_option autoImplicit false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency true
noncomputable section
universe uV vV uI vI
open CategoryTheory MonoidalCategory BraidedCategory Limits
open CategoryTheory.Enriched CategoryTheory.EnrichedFunctorCat
open scoped MonoidalClosed CategoryTheory.MonObj

namespace OrthogonalIGeneratorProbe.Coefficient

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

theorem translatedValueCoefficient (r : I) {K K' : V} (i : K ⟶ K')
    (N : Module d S L) (c : I) :
    component (pre d b S L (freeMap d S L ((Free.functor r).map i)) N) c ≫
        (FreeSourceAction.Mapping.translatedValueIso d b S L r K N c).hom =
      (FreeSourceAction.Mapping.translatedValueIso d b S L r K' N c).hom ≫
        (MonoidalClosed.pre i).app
          ((SphereModuleMappingEnd.diagram d S L N).toEnrichedFunctor.obj (c ⊗ r)) := by
  let q : (SphereModuleMappingEnd.diagram d S L N).toEnrichedFunctor.obj (r ⊗ c) ⟶
      (SphereModuleMappingEnd.diagram d S L N).toEnrichedFunctor.obj (c ⊗ r) :=
    (SphereModuleMappingEnd.diagram d S L N).toEnrichedFunctor.toOrdinaryFunctor.map (β_ r c).hom
  change component (pre d b S L (freeMap d S L ((Free.functor r).map i)) N) c ≫
      ((FreeEvaluation.valueIso d b S L r K N c).hom ≫ (ihom K).map q) =
    ((FreeEvaluation.valueIso d b S L r K' N c).hom ≫ (ihom K').map q) ≫
      (MonoidalClosed.pre i).app _
  have hn : (ihom K').map q ≫ (MonoidalClosed.pre i).app
      ((SphereModuleMappingEnd.diagram d S L N).toEnrichedFunctor.obj (c ⊗ r)) =
    (MonoidalClosed.pre i).app
      ((SphereModuleMappingEnd.diagram d S L N).toEnrichedFunctor.obj (r ⊗ c)) ≫
        (ihom K).map q := (MonoidalClosed.pre i).naturality q
  rw [← Category.assoc, freeValueCoefficient, Category.assoc]
  exact (congrArg (fun t => (FreeEvaluation.valueIso d b S L r K' N c).hom ≫ t)
    hn.symm).trans (Category.assoc _ _ _).symm

variable (B : EnrichedFunctor.LaxBraidedData L)

set_option backward.isDefEq.respectTransparency false in
theorem outputCoefficient (r : I) {K K' : V} (i : K ⟶ K')
    (N T T' : Module d S L)
    (e : (functor d b S L B (FreeEvaluation.freeAt d S L r K)).obj N ≅ T)
    (e' : (functor d b S L B (FreeEvaluation.freeAt d S L r K')).obj N ≅ T')
    (t : T' ⟶ T)
    (hObj : ∀ c : I, (SphereModuleMappingEnd.diagram d S L T).toEnrichedFunctor.obj c =
      (ihom K).obj ((SphereModuleMappingEnd.diagram d S L N).toEnrichedFunctor.obj (c ⊗ r)))
    (hObj' : ∀ c : I, (SphereModuleMappingEnd.diagram d S L T').toEnrichedFunctor.obj c =
      (ihom K').obj ((SphereModuleMappingEnd.diagram d S L N).toEnrichedFunctor.obj (c ⊗ r)))
    (he : ∀ c : I, component (SphereModuleMappingEnd.moduleMap d S L e.hom) c ≫
      eqToHom (hObj c) = (FreeSourceAction.Mapping.translatedValueIso d b S L r K N c).hom)
    (he' : ∀ c : I, component (SphereModuleMappingEnd.moduleMap d S L e'.hom) c ≫
      eqToHom (hObj' c) = (FreeSourceAction.Mapping.translatedValueIso d b S L r K' N c).hom)
    (ht : ∀ c : I, component (SphereModuleMappingEnd.moduleMap d S L t) c ≫
      eqToHom (hObj c) = eqToHom (hObj' c) ≫
        (MonoidalClosed.pre i).app
          ((SphereModuleMappingEnd.diagram d S L N).toEnrichedFunctor.obj (c ⊗ r))) :
    moduleSourceMap d b S L B (freeMap d S L ((Free.functor r).map i)) N ≫ e.hom =
      e'.hom ≫ t := by
  apply SphereModuleMappingEnd.moduleMap_ext d S L
  apply EnrichedFunctorCat.hom_ext
  intro c
  rw [SphereModuleMappingEnd.moduleMap_comp, SphereModuleMappingEnd.moduleMap_comp,
    component_comp, component_comp]
  apply (cancel_mono (eqToHom (hObj c))).1
  rw [Category.assoc, he, Category.assoc, ht, ← Category.assoc, he', moduleSourceMap_hom]
  exact translatedValueCoefficient d b S L r i N c




end OrthogonalIGeneratorProbe.Coefficient
