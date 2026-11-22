/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.SimplicialCategory.OriginalCoherentAdjunctWeakCriterion
import MathlibExt.AlgebraicTopology.ModelCategory.QuillenEquivalenceCriterion

/-!
# The SAME original coherent realization and nerve are Quillen equivalent

The genuine original raw mapping comparison, source naturality and
actual locally Kan target counit prove the exact adjunct weak-map
criterion on fibrant sources. The existing native replacement criterion
extends it to every cofibrant source. The original functors, unit and
counit remain the SAME original maps; raw C(K) need not be locally Kan.
-/

noncomputable section

universe u

open CategoryTheory Limits HomotopicalAlgebra

namespace CategoryTheory.CoherentRealization.OriginalQuillenComparison

open SimplicialEnrichment

attribute [local instance] JoyalSSet.modelCategory Bergner.modelCategory

/-- The SAME actual original Quillen counit is weak at every original Bergner-fibrant enrichment. -/
theorem counit_modelWeak (C : Carrier.{u}) [IsFibrant C] : WeakEquivalence (adjunction.counit.app C) := by
  rw [counit_original]
  exact (Bergner.weakEquivalence_iff_original _).mpr
    (counit_DKweak C (Bergner.homKan_of_isFibrant C))

/-- The SAME original left/right adjunct pair satisfies the actual weak-map criterion on every original fibrant source
and target. -/
theorem fibrantSource_homEquiv_weak_iff (K : JoyalSSet.{u}) (C : Carrier.{u})
    [IsFibrant K] [IsFibrant C] (f : left.obj K ⟶ C) :
    WeakEquivalence f ↔ WeakEquivalence (adjunction.homEquiv K C f) := by
  let _ : SSet.Quasicategory (JoyalSSet.forget.obj K) :=
    (JoyalSSet.isFibrant_iff_quasicategory K).mp inferInstance
  let g := JoyalSSet.forget.map (adjunction.homEquiv K C f)
  have hfac : realizationMap g ≫ counit C = f := by
    rw [← counit_original]
    change left.map (adjunction.homEquiv K C f) ≫ adjunction.counit.app C = f
    exact (adjunction.homEquiv_counit (g := adjunction.homEquiv K C f)).symm.trans
      ((adjunction.homEquiv K C).symm_apply_apply f)
  rw [weakEquivalence_iff, weakEquivalence_iff]
  change EnrichedDwyerKan.weakEquivalences f ↔
    JoyalSSet.modelCategory.categoryWithWeakEquivalences.weakEquivalences
      (adjunction.homEquiv K C f)
  rw [JoyalSSet.modelCategory_weakEquivalences]
  exact originalAdjunct_weak_iff (Bergner.homKan_of_isFibrant C) g f hfac

/-- The SAME actual original coherent realization/nerve adjunction is a genuine global Quillen equivalence between the
named original Joyal and varying-object Bergner model structures. -/
theorem isQuillenEquivalence :
    letI : ModelCategory JoyalSSet.{u} := JoyalSSet.modelCategory
    letI : ModelCategory Carrier.{u} := Bergner.modelCategory
    adjunction.{u}.IsQuillenEquivalence := by
  let _ : adjunction.{u}.IsQuillenAdjunction := isQuillenAdjunction
  apply Adjunction.IsQuillenEquivalence.mkOfFibrantSourceCriterion adjunction
  intro K C _ _ _ f
  simp only [← weakEquivalence_iff]
  exact fibrantSource_homEquiv_weak_iff K C f

end CategoryTheory.CoherentRealization.OriginalQuillenComparison
