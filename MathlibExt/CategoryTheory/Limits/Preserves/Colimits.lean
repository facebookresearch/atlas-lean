/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua, Avocado
module

public import Mathlib.CategoryTheory.Limits.FilteredColimitCommutesFiniteLimit

@[expose] public section
set_option autoImplicit false
noncomputable section
universe uC vC uS vS uK vK uL vL
open CategoryTheory CategoryTheory.Limits

namespace CategoryTheory.Functor

/-- A supplied original colimit point preserves every limit shape commuting with C-colimits. -/
theorem preservesLimitsOfShape_of_isColimit
    {C : Type uC} [Category.{vC} C]
    {S : Type uS} [Category.{vS} S]
    {K : Type uK} [Category.{vK} K]
    {L : Type uL} [Category.{vL} L]
    [HasColimitsOfShape K C]
    [PreservesLimitsOfShape L (colim : (K ⥤ C) ⥤ C)]
    (H : K ⥤ S ⥤ C) [∀ k, PreservesLimitsOfShape L (H.obj k)]
    (c : Cocone H) (hc : IsColimit c) :
    PreservesLimitsOfShape L c.pt := by
  have hFlip : PreservesLimitsOfShape L H.flip := by
    apply preservesLimitsOfShape_of_evaluation H.flip L
    intro k
    change PreservesLimitsOfShape L (H.obj k)
    infer_instance
  let _ : PreservesLimitsOfShape L H.flip := hFlip
  let _ : PreservesLimitsOfShape L
      (H.flip ⋙ (colim : (K ⥤ C) ⥤ C)) := inferInstance
  let _ : PreservesLimitsOfShape L (colimit H) :=
    preservesLimitsOfShape_of_natIso (colimitIsoFlipCompColim H).symm
  let e : colimit H ≅ c.pt :=
    (colimit.isColimit H).coconePointUniqueUpToIso hc
  exact preservesLimitsOfShape_of_natIso e

end CategoryTheory.Functor

namespace CategoryTheory.Limits

/-- Arrow colimits commute with pullbacks through BOTH original native projections. -/
theorem arrow_colim_preservesPullbacks
    {C : Type uC} [Category.{vC} C]
    {K : Type uK} [Category.{vK} K]
    [HasLimitsOfShape WalkingCospan C] [HasColimitsOfShape K C]
    [PreservesLimitsOfShape WalkingCospan (colim : (K ⥤ C) ⥤ C)] :
    PreservesLimitsOfShape WalkingCospan (colim : (K ⥤ Arrow C) ⥤ Arrow C) := by
  let π₁ : Arrow C ⥤ C := Comma.fst _ _
  let π₂ : Arrow C ⥤ C := Comma.snd _ _
  let _ : PreservesColimitsOfShape K π₁ := by
    change PreservesColimitsOfShape K (Arrow.leftFunc : Arrow C ⥤ C)
    infer_instance
  let _ : PreservesColimitsOfShape K π₂ := by
    change PreservesColimitsOfShape K (Arrow.rightFunc : Arrow C ⥤ C)
    infer_instance
  have projectionPreserves (A : WalkingCospan ⥤ Arrow C) :
      PreservesLimit A π₁ ∧ PreservesLimit A π₂ := by
    let leftCone := limit.cone (A ⋙ Comma.fst _ _)
    let rightCone := limit.cone (A ⋙ Comma.snd _ _)
    let leftLimit := limit.isLimit (A ⋙ Comma.fst _ _)
    let rightLimit := limit.isLimit (A ⋙ Comma.snd _ _)
    let jointCone := Comma.coneOfPreserves A leftCone rightLimit
    have jointLimit : IsLimit jointCone :=
      Comma.coneOfPreservesIsLimit A leftLimit rightLimit
    have leftMapped : IsLimit (π₁.mapCone jointCone) := by
      change IsLimit leftCone
      exact leftLimit
    have rightMapped : IsLimit (π₂.mapCone jointCone) := by
      change IsLimit rightCone
      exact rightLimit
    exact ⟨preservesLimit_of_preserves_limit_cone jointLimit leftMapped,
      preservesLimit_of_preserves_limit_cone jointLimit rightMapped⟩
  let _ : PreservesLimitsOfShape WalkingCospan π₁ :=
    ⟨fun {A} => (projectionPreserves A).1⟩
  let _ : PreservesLimitsOfShape WalkingCospan π₂ :=
    ⟨fun {A} => (projectionPreserves A).2⟩
  let W₁ := (Functor.whiskeringRight K (Arrow C) C).obj π₁
  let W₂ := (Functor.whiskeringRight K (Arrow C) C).obj π₂
  let _ : PreservesLimitsOfShape WalkingCospan W₁ := inferInstance
  let _ : PreservesLimitsOfShape WalkingCospan W₂ := inferInstance
  let _ : PreservesLimitsOfShape WalkingCospan (W₁ ⋙ (colim : (K ⥤ C) ⥤ C)) :=
    inferInstance
  let _ : PreservesLimitsOfShape WalkingCospan (W₂ ⋙ (colim : (K ⥤ C) ⥤ C)) :=
    inferInstance
  let _ : PreservesLimitsOfShape WalkingCospan
      ((colim : (K ⥤ Arrow C) ⥤ Arrow C) ⋙ π₁) :=
    preservesLimitsOfShape_of_natIso (preservesColimitNatIso (J := K) π₁).symm
  let _ : PreservesLimitsOfShape WalkingCospan
      ((colim : (K ⥤ Arrow C) ⥤ Arrow C) ⋙ π₂) :=
    preservesLimitsOfShape_of_natIso (preservesColimitNatIso (J := K) π₂).symm
  refine { preservesLimit := fun {A} => { preserves := fun {c} hc => ?_ } }
  have hleft : IsLimit (π₁.mapCone
      ((colim : (K ⥤ Arrow C) ⥤ Arrow C).mapCone c)) :=
    isLimitOfPreserves ((colim : (K ⥤ Arrow C) ⥤ Arrow C) ⋙ π₁) hc
  have hright : IsLimit (π₂.mapCone
      ((colim : (K ⥤ Arrow C) ⥤ Arrow C).mapCone c)) :=
    isLimitOfPreserves ((colim : (K ⥤ Arrow C) ⥤ Arrow C) ⋙ π₂) hc
  exact ⟨Comma.fstSndJointlyReflectLimit hleft hright⟩

end CategoryTheory.Limits

universe u
namespace CategoryTheory.Limits
open CategoryTheory CategoryTheory.Limits

/-- The existing Type exactness and native functor-category lift derive C commutation. -/
theorem filtered_colim_preservesPullbacks_of_presheaf_equivalence
    {C : Type uC} [Category.{vC} C]
    {S : Type uS} [Category.{vS} S]
    (F : C ⥤ S ⥤ Type u) [F.IsEquivalence]
    {K : Type uK} [Category.{vK} K] [Small.{u} K] [IsFiltered K]
    [HasColimitsOfShape K C] :
    PreservesLimitsOfShape WalkingCospan (colim : (K ⥤ C) ⥤ C) := by
  let R := S ⥤ Type u
  let _ : HasLimitsOfShape WalkingCospan C :=
    Adjunction.hasLimitsOfShape_of_equivalence F
  let _ : PreservesFiniteLimits (colim : (K ⥤ Type u) ⥤ Type u) :=
    filtered_colim_preservesFiniteLimits_of_types
  let _ : PreservesLimitsOfShape WalkingCospan
      (colim : (K ⥤ R) ⥤ R) := inferInstance
  let W := (Functor.whiskeringRight K C R).obj F
  let _ : PreservesLimitsOfShape WalkingCospan W := inferInstance
  let _ : PreservesLimitsOfShape WalkingCospan (W ⋙ (colim : (K ⥤ R) ⥤ R)) :=
    inferInstance
  let _ : PreservesLimitsOfShape WalkingCospan ((colim : (K ⥤ C) ⥤ C) ⋙ F) :=
    preservesLimitsOfShape_of_natIso (preservesColimitNatIso (J := K) F).symm
  exact preservesLimitsOfShape_of_reflects_of_preserves
    (colim : (K ⥤ C) ⥤ C) F

end CategoryTheory.Limits
