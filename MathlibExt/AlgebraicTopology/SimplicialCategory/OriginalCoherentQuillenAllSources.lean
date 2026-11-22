/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.SimplicialCategory.OriginalCoherentQuillenEquivalence
import MathlibExt.AlgebraicTopology.SimplicialSet.ModelCategory.Joyal.AllCofibrant

/-!
# The SAME original coherent adjunct criterion at every source

Every source is genuinely cofibrant in the named original Joyal
model. The proved global Quillen equivalence therefore gives the
actual adjunct criterion for every simplicial set, with no source
quasicategory assumption. Its readback is the SAME original unit
followed by the SAME original coherent nerve map.
-/

noncomputable section

universe u

open CategoryTheory Limits HomotopicalAlgebra

namespace CategoryTheory.CoherentRealization.OriginalQuillenComparison

open SimplicialEnrichment

attribute [local instance] JoyalSSet.modelCategory Bergner.modelCategory

/-- The entire SAME original designated adjunct reads back to the actual original unit and coherent nerve map. -/
theorem homEquiv_original (K : JoyalSSet.{u}) (C : Carrier.{u}) (F : left.obj K ⟶ C) :
    JoyalSSet.forget.map (adjunction.homEquiv K C F) =
      unit K.toSSet ≫ coherentNerveFunctor.map F := by
  rw [Adjunction.homEquiv_unit, Functor.map_comp, unit_original, right_map]
  rfl

/-- The SAME original adjunct weak-map criterion holds at EVERY original source and every genuinely fibrant target. -/
theorem allSource_homEquiv_weak_iff (K : JoyalSSet.{u}) (C : Carrier.{u}) [IsFibrant C]
    (F : left.obj K ⟶ C) : WeakEquivalence F ↔ WeakEquivalence (adjunction.homEquiv K C F) := by
  let _ : IsCofibrant K := JoyalSSet.isCofibrant K
  let _ : adjunction.{u}.IsQuillenEquivalence := isQuillenEquivalence
  exact Adjunction.IsQuillenEquivalence.weakEquivalence_homEquiv_iff F

/-- For EVERY original simplicial set and genuinely locally Kan target, original DK weakness is equivalent to
categorical weakness of the SAME original unit/nerve composite. -/
theorem allOriginalSource_unitNerve_weak_iff (K : SSet.{u}) (C : Carrier.{u})
    (hKan : ∀ x y : C, SSet.KanComplex (x ⟶[SSet.{u}] y)) (F : realization K ⟶ C) :
    EnrichedDwyerKan.weakEquivalences F ↔
      SSet.categoricalEquivalences (unit K ≫ coherentNerveFunctor.map F) := by
  let _ : IsFibrant C := Bergner.isFibrant_of_original_homKan C hKan
  let X := JoyalSSet.ofSSet.obj K
  let F' : left.obj X ⟶ C := F
  have h := allSource_homEquiv_weak_iff X C F'
  have hJ : WeakEquivalence (adjunction.homEquiv X C F') ↔
      SSet.categoricalEquivalences (JoyalSSet.forget.map (adjunction.homEquiv X C F')) := by
    rw [weakEquivalence_iff]
    change JoyalSSet.modelCategory.categoryWithWeakEquivalences.weakEquivalences
      (adjunction.homEquiv X C F') ↔ _
    rw [JoyalSSet.modelCategory_weakEquivalences]
    rfl
  have hRead : JoyalSSet.forget.map (adjunction.homEquiv X C F') =
      unit K ≫ coherentNerveFunctor.map F := homEquiv_original X C F'
  exact (Bergner.weakEquivalence_iff_original F').symm.trans
    (h.trans (hJ.trans (Iff.of_eq (congrArg
      (fun g : K ⟶ coherentNerveFunctor.obj C => SSet.categoricalEquivalences g) hRead))))

end CategoryTheory.CoherentRealization.OriginalQuillenComparison
