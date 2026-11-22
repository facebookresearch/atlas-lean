/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.SimplicialCategory.WalkingAdjunction.BoundaryConeHornIso
import MathlibExt.AlgebraicTopology.SimplicialSet.JoyalModelCategory
import MathlibExt.AlgebraicTopology.ModelCategory.Under
import Mathlib.CategoryTheory.LiftingProperties.Adjunction

/-!
# The original join with a point preserves monomorphisms

The already proved coned-boundary map is monic. The native structured
join adjunction carries its lifting property to the right adjoint.
The original boundary weak factorization system then detects every
source monomorphism. In the named Joyal Under model, this yields the
actual target cofibration and hence the original whole monomorphism.
No additional join coefficient formula or model structure is chosen.
-/

set_option autoImplicit false

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits CategoryTheory.MorphismProperty HomotopicalAlgebra
open scoped Simplicial

namespace SSet.WalkingAdjunction

attribute [local instance] JoyalSSet.modelCategory

/-- Join with the identical original point preserves every original simplicial monomorphism. -/
theorem mono_join_point {X Y : SSet.{u}} (f : X ⟶ Y) [Mono f] :
    Mono ((join.map f).app (Δ[0] : SSet.{u})) := by
  let E : Under (Δ[0] : SSet.{u}) ≌ Under (JoyalSSet.ofSSet.obj (Δ[0] : SSet.{u})) :=
    Under.postEquiv (X := (Δ[0] : SSet.{u})) JoyalSSet.equivalenceSSet.symm
  let L : SSet.{u} ⥤ Under (JoyalSSet.ofSSet.obj (Δ[0] : SSet.{u})) :=
    joinOver (Δ[0] : SSet.{u}) ⋙ E.functor
  let R : Under (JoyalSSet.ofSSet.obj (Δ[0] : SSet.{u})) ⥤ SSet.{u} :=
    E.inverse ⋙ joinRightDivision (Δ[0] : SSet.{u})
  let adj : L ⊣ R := (joinOverAdjunction (Δ[0] : SSet.{u})).comp E.toAdjunction
  have hl : cofibrations (Under (JoyalSSet.ofSSet.obj (Δ[0] : SSet.{u}))) (L.map f) := by
    rw [← llp_eq_of_wfs
      (cofibrations (Under (JoyalSSet.ofSSet.obj (Δ[0] : SSet.{u}))))
      (trivialFibrations (Under (JoyalSSet.ofSSet.obj (Δ[0] : SSet.{u}))))]
    intro A B p hp
    let _ : Fibration p := (mem_trivialFibrations_iff _ |>.mp hp).1
    let _ : WeakEquivalence p := (mem_trivialFibrations_iff _ |>.mp hp).2
    have hr : modelCategoryQuillen.I.rlp (R.map p) := by
      rintro K H i ⟨n⟩
      let _ : Mono ((join.map (boundary.{u} n).ι).app (Δ[0] : SSet.{u})) :=
        BoundaryConeHornIso.mono_join_boundary n
      have hc : Cofibration (L.map (boundary.{u} n).ι) := by
        apply (cofibrations_under_iff _ _).mpr
        rw [cofibration_iff]
        change JoyalSSet.modelCategory.categoryWithCofibrations.cofibrations
          (JoyalSSet.ofSSet.map ((join.map (boundary.{u} n).ι).app (Δ[0] : SSet.{u})))
        rw [JoyalSSet.modelCategory_cofibrations]
        exact inferInstance
      have hLift : HasLiftingProperty (L.map (boundary.{u} n).ι) p :=
        hasLiftingProperty_of_wfs _ _ ((cofibration_iff _).mp hc) hp
      exact (adj.hasLiftingProperty_iff (boundary.{u} n).ι p).mp hLift
    have hf : modelCategoryQuillen.I.rlp.llp f := by
      rw [modelCategoryQuillen.llp_rlp_I]
      exact inferInstance
    exact (adj.hasLiftingProperty_iff f p).mpr (hf (R.map p) hr)
  have hc : Cofibration (L.map f) := (cofibration_iff _).mpr hl
  have hraw : Cofibration (JoyalSSet.ofSSet.map ((join.map f).app (Δ[0] : SSet.{u}))) :=
    (cofibrations_under_iff _ _).mp hc
  have hm : Mono (JoyalSSet.ofSSet.map ((join.map f).app (Δ[0] : SSet.{u}))) := by
    have h := (cofibration_iff _).mp hraw
    change JoyalSSet.modelCategory.categoryWithCofibrations.cofibrations
      (JoyalSSet.ofSSet.map ((join.map f).app (Δ[0] : SSet.{u}))) at h
    rw [JoyalSSet.modelCategory_cofibrations] at h
    exact h
  exact JoyalSSet.ofSSet.{u}.mono_of_mono_map hm

end SSet.WalkingAdjunction
