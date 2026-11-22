/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.CategoryTheory.Enriched.ModuleMappingRFreeSourceAction

/-!
# Coefficient naturality for mapping objects of free enriched modules

For enriched Day modules over a lax monoidal coefficient functor, free generators
are natural in maps of their coefficients. With the colimits, products, and
equalizers required for the mapping objects, this gives a coefficient-naturality
formula for the free-evaluation isomorphism. Precomposition by a free-module
coefficient map corresponds to precomposition inside the base internal Hom.
-/

set_option autoImplicit false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency true
noncomputable section
universe uV vV uI vI
open CategoryTheory MonoidalCategory BraidedCategory Limits
open CategoryTheory.Enriched CategoryTheory.EnrichedFunctorCat
open scoped MonoidalClosed CategoryTheory.MonObj

namespace OrthogonalIGeneratorProbe.Primitive
universe uC vC
attribute [local instance] MonoidalLeftAction.monoidalOppositeLeftAction
variable {C : Type uC} [Category.{vC} C] [MonoidalCategory C]
  (R : C) [MonObj R]

theorem freeGenerator_naturality {X Y : C} (f : X ⟶ Y) :
    RightModuleFree.freeGenerator R X ≫ (RightModuleFree.freeMap R f).hom =
      f ≫ RightModuleFree.freeGenerator R Y := by
  change ((ρ_ X).inv ≫ X ◁ η) ≫ (f ▷ R) = f ≫ ((ρ_ Y).inv ≫ Y ◁ η)
  rw [Category.assoc, whisker_exchange, ← Category.assoc, ← rightUnitor_inv_naturality,
    Category.assoc]


end OrthogonalIGeneratorProbe.Primitive

namespace OrthogonalIGeneratorProbe.Coefficient

attribute [local instance] Enriched.prodCategory EnrichedDayKernel.ColimitMonoidal.smallestColimits
  SphereModuleMappingEnd.moduleCategory MonoidalLeftAction.monoidalOppositeLeftAction
attribute [local irreducible] EnrichedDayKernel.Closed.monoidalClosed

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

theorem preGenerator {M M' : Module d S L} (f : M' ⟶ M)
    {K K' : V} (i : K' ⟶ K) (r : I)
    (g : K ⟶ (SphereModuleMappingEnd.diagram d S L M).toEnrichedFunctor.obj r)
    (g' : K' ⟶ (SphereModuleMappingEnd.diagram d S L M').toEnrichedFunctor.obj r)
    (hg : g' ≫ component (SphereModuleMappingEnd.moduleMap d S L f) r = i ≫ g)
    (N : Module d S L) (c : I) :
    component (pre d b S L f N) c ≫
        (π d b S L M' N c r ≫ (MonoidalClosed.pre g').app
          ((SphereModuleMappingEnd.diagram d S L N).toEnrichedFunctor.obj (r ⊗ c))) =
      (π d b S L M N c r ≫ (MonoidalClosed.pre g).app
          ((SphereModuleMappingEnd.diagram d S L N).toEnrichedFunctor.obj (r ⊗ c))) ≫
        (MonoidalClosed.pre i).app
          ((SphereModuleMappingEnd.diagram d S L N).toEnrichedFunctor.obj (r ⊗ c)) := by
  let Q := (SphereModuleMappingEnd.diagram d S L N).toEnrichedFunctor.obj (r ⊗ c)
  let j := component (SphereModuleMappingEnd.moduleMap d S L f) r
  have hp := pre_π d b S L f N c r
  have hPre : (MonoidalClosed.pre j).app Q ≫ (MonoidalClosed.pre g').app Q =
      (MonoidalClosed.pre g).app Q ≫ (MonoidalClosed.pre i).app Q := by
    calc
      _ = (MonoidalClosed.pre (g' ≫ j)).app Q :=
        (NatTrans.congr_app (MonoidalClosed.pre_map g' j) Q).symm
      _ = (MonoidalClosed.pre (i ≫ g)).app Q := congrArg (fun t => (MonoidalClosed.pre t).app Q) hg
      _ = _ := NatTrans.congr_app (MonoidalClosed.pre_map i g) Q
  exact (Category.assoc _ _ _).symm.trans
    ((congrArg (fun t => t ≫ (MonoidalClosed.pre g').app Q) hp).trans
      ((Category.assoc _ _ _).trans
        ((congrArg (fun t => π d b S L M N c r ≫ t) hPre).trans
          (Category.assoc _ _ _).symm)))

omit [SymmetricCategory I] [HasProducts V] [HasEqualizers V] in
theorem generatorMapCoefficient (r : I) {K K' : V} (i : K ⟶ K') :
    FreeEvaluation.generatorMap d S L r K ≫
        component (SphereModuleMappingEnd.moduleMap d S L
          (freeMap d S L ((Free.functor r).map i))) r =
      i ≫ FreeEvaluation.generatorMap d S L r K' := by
  let := ColimitMonoidal.monoidalCategory d
  let : MonObj (⟨S⟩ : EnrichedFunctorCat V I) := LaxMonoid.monObj d S L
  let F := Free.object r K
  let F' := Free.object r K'
  let f := (Free.functor r).map i
  have hu' : f ≫ freeUnit d S L F' = freeUnit d S L F ≫
      SphereModuleMappingEnd.moduleMap d S L (freeMap d S L f) :=
    (Primitive.freeGenerator_naturality (⟨S⟩ : EnrichedFunctorCat V I) f).symm
  have hc : component f r ≫ component (freeUnit d S L F') r =
      component (freeUnit d S L F) r ≫
        component (SphereModuleMappingEnd.moduleMap d S L (freeMap d S L f)) r :=
    (component_comp f (freeUnit d S L F') r).symm.trans
      ((congrArg (fun t => component t r) hu').trans
        (component_comp (freeUnit d S L F)
          (SphereModuleMappingEnd.moduleMap d S L (freeMap d S L f)) r))
  have hs := (Free.adjunction (V := V) r).unit.naturality i
  change i ≫ (Free.adjunction (V := V) r).unit.app K' =
    (Free.adjunction (V := V) r).unit.app K ≫ component f r at hs
  change ((Free.adjunction (V := V) r).unit.app K ≫ component (freeUnit d S L F) r) ≫
    component (SphereModuleMappingEnd.moduleMap d S L (freeMap d S L f)) r =
      i ≫ ((Free.adjunction (V := V) r).unit.app K' ≫ component (freeUnit d S L F') r)
  have ht : component (freeUnit d S L F) r ≫
      component (SphereModuleMappingEnd.moduleMap d S L (freeMap d S L f)) r =
    component f r ≫ component (freeUnit d S L F') r := hc.symm
  exact (Category.assoc _ _ _).trans
    ((congrArg (fun t => (Free.adjunction (V := V) r).unit.app K ≫ t) ht).trans
      ((Category.assoc _ _ _).symm.trans
        ((congrArg (fun t => t ≫ component (freeUnit d S L F') r) hs.symm).trans
          (Category.assoc _ _ _))))

theorem freeValueCoefficient (r : I) {K K' : V} (i : K ⟶ K')
    (N : Module d S L) (c : I) :
    component (pre d b S L (freeMap d S L ((Free.functor r).map i)) N) c ≫
        (FreeEvaluation.valueIso d b S L r K N c).hom =
      (FreeEvaluation.valueIso d b S L r K' N c).hom ≫
        (MonoidalClosed.pre i).app
          ((SphereModuleMappingEnd.diagram d S L N).toEnrichedFunctor.obj (r ⊗ c)) := by
  rw [FreeEvaluation.valueIso_generator, FreeEvaluation.valueIso_generator]
  exact preGenerator d b S L (freeMap d S L ((Free.functor r).map i)) i r
    (FreeEvaluation.generatorMap d S L r K') (FreeEvaluation.generatorMap d S L r K)
    (generatorMapCoefficient d S L r i) N c





end OrthogonalIGeneratorProbe.Coefficient
