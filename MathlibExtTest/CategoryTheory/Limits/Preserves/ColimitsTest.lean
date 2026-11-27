/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua, Avocado
module

public import MathlibExt.CategoryTheory.Limits.Preserves.Colimits

@[expose] public section
set_option autoImplicit false
noncomputable section
universe uC vC uS vS uK vK uL vL
open CategoryTheory CategoryTheory.Limits

namespace CategoryTheory.Functor.SuppliedColimitTest

/-- Preserve the actual original supplied limit cone; C needs no global L-limits. -/
def mappedOriginalLimit
    {C : Type uC} [Category.{vC} C]
    {S : Type uS} [Category.{vS} S]
    {K : Type uK} [Category.{vK} K]
    {L : Type uL} [Category.{vL} L]
    [HasColimitsOfShape K C]
    [PreservesLimitsOfShape L (colim : (K ⥤ C) ⥤ C)]
    (H : K ⥤ S ⥤ C) [∀ k, PreservesLimitsOfShape L (H.obj k)]
    (c : Cocone H) (hc : IsColimit c)
    {D : L ⥤ S} (s : Cone D) (hs : IsLimit s) :
    IsLimit (c.pt.mapCone s) := by
  let _ : PreservesLimitsOfShape L c.pt :=
    Functor.preservesLimitsOfShape_of_isColimit H c hc
  exact isLimitOfPreserves c.pt hs

/-- The unique original point comparison retains every whole NatTrans injection,
including its inverse triangle; no preservation or limit-existence premise is needed. -/
theorem original_injection_triangles
    {C : Type uC} [Category.{vC} C]
    {S : Type uS} [Category.{vS} S]
    {K : Type uK} [Category.{vK} K]
    [HasColimitsOfShape K C]
    (H : K ⥤ S ⥤ C) (c : Cocone H) (hc : IsColimit c) :
    let e : colimit H ≅ c.pt :=
      (colimit.isColimit H).coconePointUniqueUpToIso hc
    ∀ k, colimit.ι H k ≫ e.hom = c.ι.app k ∧
      c.ι.app k ≫ e.inv = colimit.ι H k := by
  dsimp only
  intro k
  exact ⟨(colimit.isColimit H).comp_coconePointUniqueUpToIso_hom hc k,
    (colimit.isColimit H).comp_coconePointUniqueUpToIso_inv hc k⟩

end CategoryTheory.Functor.SuppliedColimitTest

namespace CategoryTheory.Limits.ArrowColimitTest

/-- The whole original K-diagram pullback cone is preserved by actual Arrow colim. -/
def mappedOriginalPullback
    {C : Type uC} [Category.{vC} C]
    {K : Type uK} [Category.{vK} K]
    [HasLimitsOfShape WalkingCospan C] [HasColimitsOfShape K C]
    [PreservesLimitsOfShape WalkingCospan (colim : (K ⥤ C) ⥤ C)]
    {A : WalkingCospan ⥤ K ⥤ Arrow C} (s : Cone A) (hs : IsLimit s) :
    IsLimit ((colim : (K ⥤ Arrow C) ⥤ Arrow C).mapCone s) := by
  let _ : PreservesLimitsOfShape WalkingCospan
      (colim : (K ⥤ Arrow C) ⥤ Arrow C) := arrow_colim_preservesPullbacks
  exact isLimitOfPreserves (colim : (K ⥤ Arrow C) ⥤ Arrow C) hs

/-- Both original projection comparison NatIso components retain each injection,
with both hom and inverse triangles. No limit-preservation hypothesis is added. -/
theorem projected_comparison_triangles
    {C : Type uC} [Category.{vC} C]
    {K : Type uK} [Category.{vK} K] [HasColimitsOfShape K C]
    (D : K ⥤ Arrow C) :
    let e₁ := (preservesColimitNatIso (J := K) (Arrow.leftFunc : Arrow C ⥤ C)).app D
    let e₂ := (preservesColimitNatIso (J := K) (Arrow.rightFunc : Arrow C ⥤ C)).app D
    ∀ k, (colimit.ι D k).left ≫ e₁.hom = colimit.ι (D ⋙ Arrow.leftFunc) k ∧
      colimit.ι (D ⋙ Arrow.leftFunc) k ≫ e₁.inv = (colimit.ι D k).left ∧
      (colimit.ι D k).right ≫ e₂.hom = colimit.ι (D ⋙ Arrow.rightFunc) k ∧
      colimit.ι (D ⋙ Arrow.rightFunc) k ≫ e₂.inv = (colimit.ι D k).right := by
  dsimp only
  intro k
  exact ⟨ι_preservesColimitIso_hom Arrow.leftFunc D k,
    ι_preservesColimitIso_inv Arrow.leftFunc D k,
    ι_preservesColimitIso_hom Arrow.rightFunc D k,
    ι_preservesColimitIso_inv Arrow.rightFunc D k⟩

/-- The same supplied original Arrow-functor cocone preserves the actual input cone.
The two independent production results supply the instance; no stage packet is assumed. -/
def suppliedArrowPointPullback
    {C : Type uC} [Category.{vC} C]
    {S : Type uS} [Category.{vS} S]
    {K : Type uK} [Category.{vK} K]
    [HasLimitsOfShape WalkingCospan C] [HasColimitsOfShape K C]
    [PreservesLimitsOfShape WalkingCospan (colim : (K ⥤ C) ⥤ C)]
    (H : K ⥤ S ⥤ Arrow C)
    [∀ k, PreservesLimitsOfShape WalkingCospan (H.obj k)]
    (c : Cocone H) (hc : IsColimit c)
    {A : WalkingCospan ⥤ S} (s : Cone A) (hs : IsLimit s) :
    IsLimit (c.pt.mapCone s) := by
  let _ : PreservesLimitsOfShape WalkingCospan
      (colim : (K ⥤ Arrow C) ⥤ Arrow C) := arrow_colim_preservesPullbacks
  let _ : PreservesLimitsOfShape WalkingCospan c.pt :=
    Functor.preservesLimitsOfShape_of_isColimit (L := WalkingCospan) H c hc
  exact isLimitOfPreserves c.pt hs

end CategoryTheory.Limits.ArrowColimitTest

universe u
namespace CategoryTheory.Limits.PresheafFilteredColimitTest
open CategoryTheory CategoryTheory.Limits

/-- The actual presheaf equivalence derives commutation; the SAME supplied original
colimit point preserves its original pullback cone. No stage certificate is supplied. -/
def mappedOriginalSuppliedPullback
    {C : Type uC} [Category.{vC} C]
    {S : Type uS} [Category.{vS} S]
    (F : C ⥤ S ⥤ Type u) [F.IsEquivalence]
    {K : Type uK} [Category.{vK} K] [Small.{u} K] [IsFiltered K]
    [HasColimitsOfShape K C]
    (H : K ⥤ C ⥤ C)
    [∀ k, PreservesLimitsOfShape WalkingCospan (H.obj k)]
    (c : Cocone H) (hc : IsColimit c)
    {A : WalkingCospan ⥤ C} (s : Cone A) (hs : IsLimit s) :
    IsLimit (c.pt.mapCone s) := by
  let _ : PreservesLimitsOfShape WalkingCospan (colim : (K ⥤ C) ⥤ C) :=
    filtered_colim_preservesPullbacks_of_presheaf_equivalence F
  let _ : PreservesLimitsOfShape WalkingCospan c.pt :=
    Functor.preservesLimitsOfShape_of_isColimit (L := WalkingCospan) H c hc
  exact isLimitOfPreserves c.pt hs

end CategoryTheory.Limits.PresheafFilteredColimitTest
