/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import MathlibExt.AlgebraicTopology.SimplicialSet.FiniteJoyalIntervalFreeFiller
public import Mathlib.CategoryTheory.SmallObject.TransfiniteIteration

/-!
# The chosen omega attachment functor

The native successor structure of the selected natural unit supplies the
natural-number stage diagram, its colimit and its unit. The specified zero and
successor isomorphisms retain the exact stage equations. No fibrancy or
preservation conclusion is asserted by this datum.

This is the omega specialization of Cisinski's Construction 2.4.36 and
Cisinski 2006, Construction 1.2.34.
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace SSet.joyalInterval

/-- The native stage diagram for the original selected attachment unit. -/
def auxiliaryOmegaStages : ℕ ⥤ (SSet.{u} ⥤ SSet.{u}) :=
  (SmallObject.SuccStruct.ofNatTrans auxiliaryFreeFillerUnit.{u}).iterationFunctor ℕ

/-- The colimit of the chosen natural-number stage diagram. -/
def auxiliaryOmegaFreeFiller : SSet.{u} ⥤ SSet.{u} :=
  (SmallObject.SuccStruct.ofNatTrans auxiliaryFreeFillerUnit.{u}).iteration ℕ

/-- The native unit from the identity to that same chosen colimit. -/
def auxiliaryOmegaFreeFillerUnit : 𝟭 SSet.{u} ⟶ auxiliaryOmegaFreeFiller :=
  (SmallObject.SuccStruct.ofNatTrans auxiliaryFreeFillerUnit.{u}).ιIteration ℕ

/-- The chosen zero stage identifies naturally with the identity functor. -/
def auxiliaryOmegaStagesZeroIso : auxiliaryOmegaStages.{u}.obj 0 ≅ 𝟭 SSet.{u} :=
  (SmallObject.SuccStruct.ofNatTrans auxiliaryFreeFillerUnit.{u}).iterationFunctorObjBotIso ℕ

/-- The successor stage identifies with attachment after the current stage. -/
def auxiliaryOmegaStagesSuccIso (n : ℕ) :
    auxiliaryOmegaStages.{u}.obj (n + 1) ≅
      auxiliaryOmegaStages.{u}.obj n ⋙ auxiliaryFreeFiller.{u} :=
  (SmallObject.SuccStruct.ofNatTrans auxiliaryFreeFillerUnit.{u}).iterationFunctorObjSuccIso
    n (not_isMax n)

/-- After the specified successor isomorphism, the transition is the original unit. -/
lemma auxiliaryOmegaStages_map_succ (n : ℕ) :
    auxiliaryOmegaStages.{u}.map (homOfLE (Nat.le_succ n)) ≫
      (auxiliaryOmegaStagesSuccIso.{u} n).hom =
        Functor.whiskerLeft (auxiliaryOmegaStages.{u}.obj n) auxiliaryFreeFillerUnit.{u} := by
  have h :=
    (SmallObject.SuccStruct.ofNatTrans auxiliaryFreeFillerUnit.{u}).iterationFunctor_map_succ
    n (not_isMax n)
  change auxiliaryOmegaStages.{u}.map (homOfLE (Nat.le_succ n)) =
    Functor.whiskerLeft (auxiliaryOmegaStages.{u}.obj n) auxiliaryFreeFillerUnit.{u} ≫
      (auxiliaryOmegaStagesSuccIso.{u} n).inv at h
  rw [h, Category.assoc, Iso.inv_hom_id, Category.comp_id]

/-- The unit is the inverse zero-stage isomorphism followed by its actual colimit inclusion. -/
lemma auxiliaryOmegaFreeFillerUnit_eq :
    auxiliaryOmegaFreeFillerUnit.{u} =
      auxiliaryOmegaStagesZeroIso.{u}.inv ≫ colimit.ι auxiliaryOmegaStages.{u} 0 := rfl

end SSet.joyalInterval
