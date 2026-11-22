/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.SimplicialCategory.OriginalCoherentRealizationCofibrations
import MathlibExt.AlgebraicTopology.SimplicialCategory.OriginalBergnerFibrantObjects
import MathlibExt.AlgebraicTopology.SimplicialCategory.BergnerNerveLocalFibrations
import MathlibExt.AlgebraicTopology.SimplicialSet.JoyalModelCategory
import MathlibExt.AlgebraicTopology.ModelCategory.QuillenFibrantCriterion

/-!
# The genuine original coherent-realization and coherent-nerve Quillen adjunction

The SAME original adjunction is composed with the canonical designated
Joyal carrier equivalence. Actual all-mono realization cofibrations
and actual nerve fibrations between full original Bergner fibrant
objects prove the Quillen adjunction for the two named global models.
No preservation or model-comparison certificate is an input.
-/

noncomputable section
universe u
open CategoryTheory HomotopicalAlgebra MonoidalCategory
open scoped Simplicial

namespace CategoryTheory.CoherentRealization.OriginalQuillenComparison
open SimplicialEnrichment

/-- Forget only the scalar designation before applying the SAME original coherent realization. -/
def left : JoyalSSet.{u} ⥤ Carrier.{u} :=
  JoyalSSet.forget.{u} ⋙ realizationFunctor.{u}

/-- The SAME original coherent nerve with its canonical scalar designation. -/
def right : Carrier.{u} ⥤ JoyalSSet.{u} :=
  coherentNerveFunctor.{u} ⋙ JoyalSSet.ofSSet.{u}

/-- The actual original coherent adjunction composed with the canonical scalar carrier adjunction. -/
def adjunction : left.{u} ⊣ right.{u} :=
  JoyalSSet.equivalenceSSet.{u}.toAdjunction.comp realizationAdjunction.{u}

/-- Every original source object is realized on precisely its original simplicial set. -/
theorem left_obj (K : JoyalSSet.{u}) : left.obj K = realization K.toSSet := rfl

/-- Every original left morphism is the SAME original coherent realization map. -/
theorem left_map {K L : JoyalSSet.{u}} (f : K ⟶ L) :
    left.map f = realizationFunctor.map (JoyalSSet.forget.map f) := rfl

/-- The right object retains exactly the SAME original coherent nerve. -/
theorem right_obj (C : Carrier.{u}) :
    (right.obj C).toSSet = coherentNerveFunctor.obj C := rfl

/-- The right map retains exactly the SAME full original coherent-nerve map. -/
theorem right_map {C D : Carrier.{u}} (F : C ⟶ D) :
    JoyalSSet.forget.map (right.map F) = coherentNerveFunctor.map F := rfl

/-- The adjunction unit reads back the SAME original simplex insertion on the entire original simplicial set. -/
theorem unit_original (K : JoyalSSet.{u}) :
    JoyalSSet.forget.map (adjunction.unit.app K) = unit K.toSSet := by
  rw [adjunction, Adjunction.comp_unit_app]
  change 𝟙 _ ≫ unit K.toSSet = unit K.toSSet
  exact Category.id_comp _

/-- The adjunction counit reads back the SAME original full enriched generator evaluation map. -/
theorem counit_original (C : Carrier.{u}) :
    adjunction.counit.app C = counit C := by
  rw [adjunction, Adjunction.comp_counit_app]
  change realizationFunctor.map (𝟙 _) ≫ counit C = counit C
  rw [Functor.map_id]
  change 𝟙 (realization (coherentNerveFunctor.obj C)) ≫ counit C = counit C
  exact Category.id_comp _

/-- The SAME actual original coherent adjunction is Quillen between the named global Joyal and Bergner models. -/
theorem isQuillenAdjunction :
    letI : ModelCategory JoyalSSet.{u} := JoyalSSet.modelCategory
    letI : ModelCategory Carrier.{u} := Bergner.modelCategory
    adjunction.{u}.IsQuillenAdjunction := by
  let _ : ModelCategory JoyalSSet.{u} := JoyalSSet.modelCategory
  let _ : ModelCategory Carrier.{u} := Bergner.modelCategory
  have hL : PreservesCofibrations left.{u} := by
    intro K L i hi
    have hm : Mono i := by
      change JoyalSSet.modelCategory.categoryWithCofibrations.cofibrations i at hi
      rw [JoyalSSet.modelCategory_cofibrations] at hi
      exact hi
    let _ : Mono i := hm
    let _ : Mono (JoyalSSet.forget.map i) := inferInstance
    change Bergner.generatingCofibrations.rlp.llp
      (realizationFunctor.map (JoyalSSet.forget.map i))
    exact realizationMap_cofibration_of_mono _
  have hR : PreservesFibrationsBetweenFibrantObjects right.{u} := by
    intro C D p hp
    have hLocal : Bergner.localFibrations p := hp.1
    have hD : ∀ x y : D, SSet.KanComplex (x ⟶[SSet.{u}] y) :=
      (Bergner.isFibrant_iff_original_homKan D).mp hp.2.2
    change JoyalSSet.modelCategory.categoryWithFibrations.fibrations (right.map p)
    rw [JoyalSSet.modelCategory_fibrations]
    change SSet.categoricalFibrations (coherentNerveFunctor.map p)
    exact Bergner.localFibration_nerve_categoricalFibration p hD hLocal
  exact Adjunction.IsQuillenAdjunction.mkOfPreservesCofibrationsAndFibrationsBetweenFibrantObjects hL hR

end CategoryTheory.CoherentRealization.OriginalQuillenComparison
