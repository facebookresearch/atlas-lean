/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua

module
public import MathlibExt.CategoryTheory.Enriched.ModuleMappingRSourceFactories
public import MathlibExt.CategoryTheory.Monoidal.RightModuleMappingEndComponents

/-!
# Entire selected modules of the translated Mapping_R functors

The whole object selections are proved in the same original selected Day
world as the functors and limiting-fork constructions. The equalities identify
the actual complete modules, including their original right actions.
-/

@[expose] public section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
noncomputable section

universe uV vV uI vI

open CategoryTheory Limits MonoidalCategory BraidedCategory
open scoped MonoidalClosed CategoryTheory.MonObj

namespace CategoryTheory.Enriched.ModuleMappingR

open EnrichedFunctorCat EnrichedDayKernel

attribute [local instance] Enriched.prodCategory ColimitMonoidal.smallestColimits
attribute [local instance] SphereModuleMappingEnd.moduleCategory
attribute [local instance] MonoidalLeftAction.monoidalOppositeLeftAction
attribute [local irreducible] Closed.monoidalClosed

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

/-- Every selected functor value is the entire original source equalizer module. -/
theorem functor_obj (M N : Module d S L) :
    (functor d b S L B M).obj N = moduleObject d b S L B M N := by
  let : MonoidalCategory (EnrichedFunctorCat V I) := ColimitMonoidal.monoidalCategory d
  let : SymmetricCategory (EnrichedFunctorCat V I) := BraidingMonoidal.symmetricCategory d b
  let : MonoidalClosed (EnrichedFunctorCat V I) := Closed.monoidalClosed d
  let : MonObj (⟨S⟩ : EnrichedFunctorCat V I) := LaxMonoid.monObj d S L
  let := LaxMonoid.isCommMonObj d b S L B
  have h := congrArg (fun F => F.obj N) (functor_eq_source d b S L B M)
  exact h.trans ((RightModuleMappingEnd.functor_obj
    (⟨S⟩ : EnrichedFunctorCat V I) M N).trans
      (moduleObject_eq_source d b S L B M N).symm)

end CategoryTheory.Enriched.ModuleMappingR
