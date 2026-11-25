/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua, Avocado
module

public import MathlibExt.AlgebraicTopology.ModelCategory.StrongDeformationData
public import Mathlib.AlgebraicTopology.ModelCategory.IsCofibrant

/-!
# Strong deformation data from a cylinder corner

In a model category, a trivial cofibration between fibrant objects has strong
deformation data for any functorial precylinder whose boundary corner on that
map is again a trivial cofibration. This isolates the exact cylinder/model
compatibility used by the construction.
-/

@[expose] public section

set_option autoImplicit false
noncomputable section

universe v u

open CategoryTheory CategoryTheory.Limits
open CategoryTheory.MorphismProperty

namespace HomotopicalAlgebra.Precylinder

variable {C : Type u} [Category.{v} C] [ModelCategory C]

/-- A trivial cofibration between fibrant objects admits strong deformation
data when its boundary corner is a trivial cofibration for the same chosen
precylinder. -/
theorem nonempty_strongDeformationData_of_trivialCofibration
    (P : Precylinder (𝟭 C)) {X Y : C} (i : X ⟶ Y)
    (hi : trivialCofibrations C i)
    (hcorner : trivialCofibrations C (P.boundaryCorner i))
    (hX : IsFibrant X) (hY : IsFibrant Y) :
    Nonempty (P.StrongDeformationData i) := by
  let _ : Cofibration i := (cofibration_iff i).2 hi.1
  let _ : WeakEquivalence i := (weakEquivalence_iff i).2 hi.2
  let _ : IsFibrant X := hX
  let _ : IsFibrant Y := hY
  let retractSq : CommSq (𝟙 X) i (terminal.from X) (terminal.from Y) :=
    ⟨by simp⟩
  let _ : HasLiftingProperty i (terminal.from X) :=
    ModelCategory.cm4a i (terminal.from X)
  let r : Y ⟶ X := retractSq.lift
  have hr : i ≫ r = 𝟙 X := retractSq.fac_left
  let boundaryMap : Y ⨿ Y ⟶ Y := coprod.desc (𝟙 Y) (r ≫ i)
  let cylinderMap : P.I.obj X ⟶ Y := (P.app X).π ≫ i
  have compatibility :
      coprod.map i i ≫ boundaryMap = (P.app X).i ≫ cylinderMap := by
    apply coprod.hom_ext
    · simp only [boundaryMap, cylinderMap, coprod.inl_map_assoc,
        coprod.inl_desc, Category.comp_id]
      rw [(P.app X).inl_i_assoc, (P.app X).i₀_π_assoc]
    · simp only [boundaryMap, cylinderMap, coprod.inr_map_assoc,
        coprod.inr_desc]
      rw [(P.app X).inr_i_assoc, (P.app X).i₁_π_assoc,
        ← Category.assoc, hr, Category.id_comp]
  let partialMap : pushout (coprod.map i i) (P.app X).i ⟶ Y :=
    pushout.desc boundaryMap cylinderMap compatibility
  let _ : Cofibration (P.boundaryCorner i) :=
    (cofibration_iff _).2 hcorner.1
  let _ : WeakEquivalence (P.boundaryCorner i) :=
    (weakEquivalence_iff _).2 hcorner.2
  let homotopySq :
      CommSq partialMap (P.boundaryCorner i) (terminal.from Y)
        (terminal.from (P.I.obj Y)) :=
    ⟨terminalIsTerminal.hom_ext _ _⟩
  let _ : HasLiftingProperty (P.boundaryCorner i) (terminal.from Y) :=
    ModelCategory.cm4a (P.boundaryCorner i) (terminal.from Y)
  let H : P.I.obj Y ⟶ Y := homotopySq.lift
  have hHboundary : P.boundaryCorner i ≫ H = partialMap :=
    homotopySq.fac_left
  refine ⟨{
    retraction := r
    retract := hr
    homotopy :=
      { h := H
        h₀ := ?_
        h₁ := ?_
        stationary := ?_ } }⟩
  · calc
      (P.app Y).i₀ ≫ H =
          coprod.inl ≫ ((P.app Y).i ≫ H) := by
            rw [← Category.assoc, (P.app Y).inl_i]
      _ = coprod.inl ≫
          (pushout.inl (coprod.map i i) (P.app X).i ≫
            P.boundaryCorner i ≫ H) := by
            rw [P.inl_boundaryCorner_assoc]
      _ = coprod.inl ≫
          (pushout.inl (coprod.map i i) (P.app X).i ≫ partialMap) := by
            rw [hHboundary]
      _ = 𝟙 Y := by simp [partialMap, boundaryMap]
  · calc
      (P.app Y).i₁ ≫ H =
          coprod.inr ≫ ((P.app Y).i ≫ H) := by
            rw [← Category.assoc, (P.app Y).inr_i]
      _ = coprod.inr ≫
          (pushout.inl (coprod.map i i) (P.app X).i ≫
            P.boundaryCorner i ≫ H) := by
            rw [P.inl_boundaryCorner_assoc]
      _ = coprod.inr ≫
          (pushout.inl (coprod.map i i) (P.app X).i ≫ partialMap) := by
            rw [hHboundary]
      _ = r ≫ i := by simp [partialMap, boundaryMap]
  · rw [Category.comp_id, ← P.inr_boundaryCorner_assoc i H,
      hHboundary]
    simp [partialMap, cylinderMap]

end HomotopicalAlgebra.Precylinder
