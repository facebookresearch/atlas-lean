/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.SimplicialCategory.BergnerTwoLabelFibrationSquare

/-!
# Actual full original global interval lifts from exact paired coefficient data

Both full original object functions and unit coefficients determine the
actual two-label fibration frame. The exact original coefficient equation
pairs the same unit maps in its actual full Hom pullback. The proved
native interval section constructs the unchanged whole global enriched
lift. Its whole right triangle and every original vertex image are kept.
-/

noncomputable section
universe u
open CategoryTheory HomotopicalAlgebra MonoidalCategory
open scoped Simplicial

namespace CategoryTheory.SimplicialEnrichment.BergnerTwoLabelFibrationSquare
open FixedObjects OriginalWalkingArrowFreeSingleHomIso ComponentCategory
attribute [local instance] FixedObjectModel.modelCategory
variable {E D : Carrier.{u}} (r : E ⟶ D) (hr : Bergner.homFibrations r)
variable (H : FixedObjects walking.{u}) [IsCofibrant H]
variable (hH : FixedObjectModel.weakEquivalences walking (CodiscreteTerminal.toTerminal H))
variable (F : H.val ⟶ D) (a : walking.{u} → E)

include hr hH in
/-- Exact original full paired coefficients construct a genuine whole enriched interval lift with every prescribed
original vertex. -/
theorem exists_original_lift (hObj : ∀ z, r.obj (a z) = F.obj (vertex H z))
    (x y : walking.{u})
    (hxy : (x = BergnerTwoObject.source (𝟙_ SSet.{u}) ∧ y = BergnerTwoObject.target (𝟙_ SSet.{u})) ∨
      (x = BergnerTwoObject.target (𝟙_ SSet.{u}) ∧ y = BergnerTwoObject.source (𝟙_ SSet.{u})))
    (qA : 𝟙_ SSet.{u} ⟶ (a x ⟶[SSet.{u}] a y)) (qH : 𝟙_ SSet.{u} ⟶ hom H x y)
    (hq : qA ≫ (r.map (a x) (a y) ≫ eqToHom
      (congrArg₂ (fun s t : D => s ⟶[SSet.{u}] t) (hObj x) (hObj y))) =
        qH ≫ F.map (vertex H x) (vertex H y))
    (hA : IsIso (arrowOf E (SSet.unitHomEquiv _ qA)))
    (hHom : IsIso (arrowOf H.val (SSet.unitHomEquiv _ qH))) :
    ∃ l : H.val ⟶ E, l ≫ r = F ∧ ∀ z, l.obj (vertex H z) = a z := by
  let b : walking.{u} → D := fun z => F.obj (vertex H z)
  let R := right r a b hObj
  let B : H ⟶ target b := CarrierLabelReadback.map H b F (fun _ => rfl)
  have hB (i j : walking.{u}) : homMap B i j = F.map (vertex H i) (vertex H j) := by
    have h := CarrierLabelReadback.homMap_map H b F (fun _ => rfl) i j
    change homMap B i j = F.map (vertex H i) (vertex H j) ≫ eqToHom _ at h
    exact h.trans (Category.comp_id _)
  have hc : qA ≫ homMap R x y = qH ≫ homMap B x y :=
    (congrArg (fun k => qA ≫ k) (right_hom r a b hObj x y)).trans
      (hq.trans (congrArg (fun k => qH ≫ k) (hB x y)).symm)
  have hA' : IsIso (arrowOf (source a).val (SSet.unitHomEquiv _ qA)) := unit_isIso a x y qA hA
  obtain ⟨L, hL⟩ := OriginalFixedLabelIntervalLift.exists_lift_at_pair R B
    (right_fibration r a b hObj hr) hH x y hxy qA qH hc hA' hHom
  let l : H.val ⟶ E := L.val ≫ CarrierReindexing.toTarget E a
  have hRight : l ≫ r = F := by
    change (L.val ≫ CarrierReindexing.toTarget E a) ≫ r = F
    exact (Category.assoc _ _ _).trans
      ((congrArg (fun k => L.val ≫ k) (right_projection r a b hObj).symm).trans
        ((Category.assoc _ _ _).symm.trans
          ((congrArg (fun k : H ⟶ target b => k.val ≫ CarrierReindexing.toTarget D b) hL).trans
            (CarrierLabelReadback.map_fac H b F (fun _ => rfl)))))
  refine ⟨l, hRight, ?_⟩
  intro z
  exact congrArg (CarrierReindexing.toTarget E a).obj (map_vertex L z)

end CategoryTheory.SimplicialEnrichment.BergnerTwoLabelFibrationSquare
