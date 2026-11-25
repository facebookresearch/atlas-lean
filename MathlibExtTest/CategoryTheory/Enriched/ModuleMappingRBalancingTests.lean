/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua

import MathlibExt.CategoryTheory.Enriched.ModuleMappingRAction

/-!
# Literal right-module mapping balance with all parameters and source arrows

These clients retain the original σ_M, σ_N κ and every whole V-parameter.
No braided coefficient data or commutativity of the Day monoid is assumed.
The original full module arrows act through their actual translated projections.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section

universe uV vV uI vI

open CategoryTheory Limits MonoidalCategory
open scoped MonoidalClosed CategoryTheory.MonObj

namespace CategoryTheory.Enriched.ModuleMappingRBalancingTests

open EnrichedFunctorCat EnrichedDayKernel ModuleMappingR

attribute [local instance] Enriched.prodCategory ColimitMonoidal.smallestColimits
attribute [local instance] SphereModuleMappingEnd.moduleCategory

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

/-- The literal original action equations construct the entire represented mapping family. -/
def fromOriginalBalance (M N : Module d S L) (c : I) {P : V}
    (t : GradedNatTrans ((Center.ofBraided V).obj P)
      (SphereModuleMappingEnd.diagram d S L M).toEnrichedFunctor
      (Closed.translatedTarget d (SphereModuleMappingEnd.diagram d S L N) c).toEnrichedFunctor)
    (h : ∀ j a,
      (ExternalRightModule.sigma d S (SphereModuleMappingEnd.diagram d S L M)
        (SphereModuleMappingEnd.action d S L M) j a ▷ P) ≫
          MonoidalClosed.uncurry (t.app (j ⊗ a)) =
      coefficientSwap ((SphereModuleMappingEnd.diagram d S L M).toEnrichedFunctor.obj j)
          (S.obj a) P ≫
        (MonoidalClosed.uncurry (t.app j) ▷ S.obj a) ≫ translatedAction d S L N c j a) :
    Family d b S L M N c P where
  transformation := t
  condition := (condition_iff_actionBalance d b S L M N c t).2 h

/-- Every full original source arrow keeps its actual source and translated target action balance. -/
theorem original_source_arrow_balance {M M' : Module d S L} (f : M' ⟶ M)
    (N : Module d S L) (c : I) {P : V} (q : P ⟶ value d b S L M N c) (j a : I) :
    (ExternalRightModule.sigma d S (SphereModuleMappingEnd.diagram d S L M')
      (SphereModuleMappingEnd.action d S L M') j a ▷ P) ≫
      MonoidalClosed.uncurry
        (q ≫ π d b S L M N c (j ⊗ a) ≫
          (MonoidalClosed.pre (component (SphereModuleMappingEnd.moduleMap d S L f)
            (j ⊗ a))).app
              ((SphereModuleMappingEnd.diagram d S L N).toEnrichedFunctor.obj
                ((j ⊗ a) ⊗ c))) =
    coefficientSwap ((SphereModuleMappingEnd.diagram d S L M').toEnrichedFunctor.obj j)
        (S.obj a) P ≫
      (MonoidalClosed.uncurry
        (q ≫ π d b S L M N c j ≫
          (MonoidalClosed.pre (component (SphereModuleMappingEnd.moduleMap d S L f) j)).app
            ((SphereModuleMappingEnd.diagram d S L N).toEnrichedFunctor.obj (j ⊗ c))) ▷
              S.obj a) ≫ translatedAction d S L N c j a := by
  have h := Family.action_balance d b S L
    (toFamily d b S L M' N c (q ≫ component (pre d b S L f N) c)) j a
  simpa only [toFamily_app, Category.assoc, pre_π] using h

/-- Every full target arrow keeps the same original source action and the literal new σ_N κ. -/
theorem original_target_arrow_balance (M : Module d S L) {N N' : Module d S L}
    (g : N ⟶ N') (c : I) {P : V} (q : P ⟶ value d b S L M N c) (j a : I) :
    (ExternalRightModule.sigma d S (SphereModuleMappingEnd.diagram d S L M)
      (SphereModuleMappingEnd.action d S L M) j a ▷ P) ≫
      MonoidalClosed.uncurry
        (q ≫ π d b S L M N c (j ⊗ a) ≫
          (ihom ((SphereModuleMappingEnd.diagram d S L M).toEnrichedFunctor.obj (j ⊗ a))).map
            (component (SphereModuleMappingEnd.moduleMap d S L g) ((j ⊗ a) ⊗ c))) =
    coefficientSwap ((SphereModuleMappingEnd.diagram d S L M).toEnrichedFunctor.obj j)
        (S.obj a) P ≫
      (MonoidalClosed.uncurry
        (q ≫ π d b S L M N c j ≫
          (ihom ((SphereModuleMappingEnd.diagram d S L M).toEnrichedFunctor.obj j)).map
            (component (SphereModuleMappingEnd.moduleMap d S L g) (j ⊗ c))) ▷ S.obj a) ≫
              translatedAction d S L N' c j a := by
  have h := Family.action_balance d b S L
    (toFamily d b S L M N' c (q ≫ component (post d b S L M g) c)) j a
  simpa only [toFamily_app, Category.assoc, post_π] using h

/-- The complete represented family and its literal equations recover the whole family. -/
theorem represented_family_roundtrip (M N : Module d S L) (c : I) {P : V}
    (q : Family d b S L M N c P) :
    toFamily d b S L M N c (lift d b S L M N c q) = q :=
  toFamily_lift d b S L M N c q

end CategoryTheory.Enriched.ModuleMappingRBalancingTests
