/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua

import MathlibExt.CategoryTheory.Enriched.ModuleMappingRFamilies

/-!
# Full coefficient-first Mapping_R family clients

The coefficient monoid is arbitrary. Complete graded source naturality,
the literal κ balance, arbitrary original module maps and the whole
parameter Hom are retained in the represented families.
-/

set_option autoImplicit false
noncomputable section

universe uV vV uI vI

open CategoryTheory Limits MonoidalCategory BraidedCategory
open scoped MonoidalClosed CategoryTheory.MonObj

namespace CategoryTheory.Enriched.ModuleMappingRFamiliesTests

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

/-- The literal coefficient-first balance constructs the genuine full action-end family. -/
def fromCoefficientFirstBalance (M N : Module d S L) (c : I) (P : V)
    (t : GradedNatTrans ((Center.ofBraided V).obj P)
      (SphereModuleMappingEnd.diagram d S L M).toEnrichedFunctor
      (Closed.translatedTarget d (SphereModuleMappingEnd.diagram d S L N) c).toEnrichedFunctor)
    (h : ∀ j a,
      (P ◁ ExternalRightModule.sigma d S (SphereModuleMappingEnd.diagram d S L M)
        (SphereModuleMappingEnd.action d S L M) j a) ≫
          GradedNatTrans.gradeFirstComponent ((Center.ofBraided V).obj P) t (j ⊗ a) =
      (α_ P ((SphereModuleMappingEnd.diagram d S L M).toEnrichedFunctor.obj j)
        (S.obj a)).inv ≫
        (GradedNatTrans.gradeFirstComponent ((Center.ofBraided V).obj P) t j ▷ S.obj a) ≫
          translatedAction d S L N c j a) : Family d b S L M N c P where
  transformation := t
  condition := (condition_iff_gradeFirst_balance d b S L M N c t).2 h

/-- Every coefficient-first family retains its exact original σ_M/σ_N κ equation. -/
theorem original_coefficient_first_balance (M N : Module d S L) (c : I) (P : V)
    (q : Family d b S L M N c P) (j a : I) :
    (P ◁ ExternalRightModule.sigma d S (SphereModuleMappingEnd.diagram d S L M)
      (SphereModuleMappingEnd.action d S L M) j a) ≫ q.evaluation d b S L (j ⊗ a) =
    (α_ P ((SphereModuleMappingEnd.diagram d S L M).toEnrichedFunctor.obj j)
      (S.obj a)).inv ≫
      (q.evaluation d b S L j ▷ S.obj a) ≫ translatedAction d S L N c j a :=
  q.evaluation_action_balance d b S L j a

/-- Arbitrary coefficient and complete original source/target arrows have their full
coefficient-first evaluation formula. -/
theorem all_original_arrows {M M' N N' : Module d S L} {c : I} {P Q : V}
    (h : P ⟶ Q) (f : M' ⟶ M) (g : N ⟶ N') (q : Family d b S L M N c Q) (j : I) :
    (((q.sourceMap d b S L f).targetMap d b S L g).regrade d b S L h).evaluation
        d b S L j =
      (h ▷ (SphereModuleMappingEnd.diagram d S L M').toEnrichedFunctor.obj j) ≫
        (Q ◁ component (SphereModuleMappingEnd.moduleMap d S L f) j) ≫
        q.evaluation d b S L j ≫
          component (SphereModuleMappingEnd.moduleMap d S L g) (j ⊗ c) := by
  simp only [Family.regrade_evaluation, Family.targetMap_evaluation,
    Family.sourceMap_evaluation, Category.assoc]

/-- The parameter family uses the whole original I(c,c') object in every end projection. -/
theorem entire_parameter_hom (M N : Module d S L) (c c' : I) (P : V)
    (q : Family d b S L M N c P) (j : I) :
    (q.parameterMap d b S L c').transformation.app j =
      (q.transformation.app j ⊗ₘ
        Closed.parameterComponent d (SphereModuleMappingEnd.diagram d S L N) c c' j) ≫
        eComp V ((SphereModuleMappingEnd.diagram d S L M).toEnrichedFunctor.obj j)
          ((SphereModuleMappingEnd.diagram d S L N).toEnrichedFunctor.obj (j ⊗ c))
          ((SphereModuleMappingEnd.diagram d S L N).toEnrichedFunctor.obj (j ⊗ c')) :=
  q.parameterMap_app d b S L c' j

/-- The inverse correspondence retains the entire genuine graded family. -/
theorem complete_family_inverse (M N : Module d S L) (c : I) (P : V)
    (q : Family d b S L M N c P) :
    toFamily d b S L M N c (lift d b S L M N c q) = q :=
  toFamily_lift d b S L M N c q

/-- The forward correspondence retains every whole original end-valued coefficient map. -/
theorem complete_value_inverse (M N : Module d S L) (c : I) (P : V)
    (f : P ⟶ value d b S L M N c) :
    lift d b S L M N c (toFamily d b S L M N c f) = f :=
  lift_toFamily d b S L M N c f

end CategoryTheory.Enriched.ModuleMappingRFamiliesTests
