/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.TopologicalSpace.Spectra.Orthogonal.FreeSmashHomotopyExtension.OriginalFreeFunctor
import MathlibExt.AlgebraicTopology.TopologicalSpace.Spectra.Orthogonal.FreeSmashHomotopyExtension.OriginalMappingFamily
import MathlibExt.AlgebraicTopology.TopologicalSpace.Spectra.Orthogonal.FreeSmashHomotopyExtension.FreeMappingFields
import Mathlib.CategoryTheory.EqToHom
import Mathlib.CategoryTheory.Adjunction.Parametrized

/-!
# Contravariant internal Hom from free modules

Constructs the free-module source functor explicitly from its objects and coefficient
maps, under the supplied enriched Day and lax braided coefficient data. Restricting the
module internal Hom bifunctor gives the contravariant coefficient family and identifies
it with the free/evaluation construction.
-/

set_option autoImplicit false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency true
noncomputable section
universe uV vV uI vI
open CategoryTheory MonoidalCategory BraidedCategory Limits
open CategoryTheory.Enriched CategoryTheory.EnrichedFunctorCat
open scoped MonoidalClosed CategoryTheory.MonObj

namespace OrthogonalIGeneratorProbe.LiteralFreeMapping

namespace Internal

universe uC vC uA vA

attribute [local instance] MonoidalLeftAction.monoidalOppositeLeftAction

variable {C : Type uC} [Category.{vC} C] [MonoidalCategory C] (M : C) [MonObj M]
  {A : Type uA} [Category.{vA} A]

private def freeFunctor (F : A ⥤ C) : A ⥤ CommutativeModuleConversion.RightModule M where
  obj X := RightModuleFree.freeObject M (F.obj X)
  map f := RightModuleFree.freeMap M (F.map f)
  map_id X := by
    rw [F.map_id]
    exact RightModuleFree.freeMap_id M _
  map_comp f g := by
    rw [F.map_comp]
    exact RightModuleFree.freeMap_comp M _ _

private theorem freeFunctor_eq (F : A ⥤ C) :
    freeFunctor M F = F ⋙ RightModuleFree.functor M := rfl

end Internal

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

omit [SymmetricCategory I] [HasProducts.{uI} V] [HasEqualizers V] in
private theorem originalFreeMap_id (F : EnrichedFunctorCat V I) :
    freeMap d S L (𝟙 F) = 𝟙 (freeModule d S L F) := by
  let := ColimitMonoidal.monoidalCategory d
  let : MonObj (⟨S⟩ : EnrichedFunctorCat V I) := LaxMonoid.monObj d S L
  exact RightModuleFree.freeMap_id (⟨S⟩ : EnrichedFunctorCat V I) F

omit [SymmetricCategory I] [HasProducts.{uI} V] [HasEqualizers V] in
private theorem originalFreeMap_comp {F F' F'' : EnrichedFunctorCat V I}
    (f : F ⟶ F') (g : F' ⟶ F'') :
    freeMap d S L (f ≫ g) = freeMap d S L f ≫ freeMap d S L g := by
  let := ColimitMonoidal.monoidalCategory d
  let : MonObj (⟨S⟩ : EnrichedFunctorCat V I) := LaxMonoid.monObj d S L
  exact RightModuleFree.freeMap_comp (⟨S⟩ : EnrichedFunctorCat V I) f g

/-- Keep the original complete free-module objects and maps in the functor fields, so
mapping-family readbacks do not reduce the full composite free-functor record. -/
private def originalFreeFunctor (r : I) : V ⥤ Module d S L where
  obj K := freeModule d S L ((Free.functor r).obj K)
  map i := freeMap d S L ((Free.functor r).map i)
  map_id K := by
    rw [(Free.functor r).map_id]
    exact originalFreeMap_id d S L _
  map_comp i j := by
    rw [(Free.functor r).map_comp]
    exact originalFreeMap_comp d S L _ _

omit [SymmetricCategory I] [HasProducts.{uI} V] [HasEqualizers V] in
private theorem originalFreeFunctor_eq (r : I) :
    originalFreeFunctor d S L r = LiteralFreeExt.functor d S L r := by
  let := ColimitMonoidal.monoidalCategory d
  let : MonObj (⟨S⟩ : EnrichedFunctorCat V I) := LaxMonoid.monObj d S L
  change Internal.freeFunctor (⟨S⟩ : EnrichedFunctorCat V I) (Free.functor r) = _
  exact Internal.freeFunctor_eq (⟨S⟩ : EnrichedFunctorCat V I) (Free.functor r)

/-- The contravariant mapping family with source the literal free module functor at `r`. -/
def family (r : I) : Vᵒᵖ ⥤ (Module d S L ⥤ Module d S L) :=
  LiteralMapping.functor d b S L B (originalFreeFunctor d S L r)

theorem whole_eq (r : I) : family d b S L B r = FreeMappingGetters.functor d b S L B r :=
  (LiteralMapping.whole_eq d b S L B (originalFreeFunctor d S L r)).trans
    (congrArg (fun F : V ⥤ Module d S L => F.op ⋙ ModuleMappingR.moduleBifunctor d b S L B)
      ((originalFreeFunctor_eq d S L r).trans (LiteralFreeExt.whole_eq d S L r)))

theorem obj (r : I) (K : Vᵒᵖ) :
    (family d b S L B r).obj K =
      ModuleMappingR.functor d b S L B (FreeEvaluation.freeAt d S L r K.unop) := rfl

theorem map (r : I) {K K' : Vᵒᵖ} (i : K ⟶ K') :
    (family d b S L B r).map i =
      ModuleMappingR.moduleSourceNatTrans d b S L B
        (freeMap d S L ((Free.functor r).map i.unop)) := rfl






end OrthogonalIGeneratorProbe.LiteralFreeMapping
