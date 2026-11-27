/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua, Avocado

module

public import Mathlib.CategoryTheory.Presentable.Basic
public import Mathlib.CategoryTheory.Limits.FunctorCategory.Basic
public import Mathlib.CategoryTheory.Adjunction.Limits

/-!
# Colimits of accessible functors

The original diagram of accessible functors has an accessible chosen
colimit, using pointwise evaluation, the colimit adjunction and their native
natural comparison. Index and test universes remain independent.
-/

public section
set_option autoImplicit false
noncomputable section
universe uC vC uD vD uI vI μU
open CategoryTheory CategoryTheory.Limits
namespace CategoryTheory.Functor

/-- The actual colimit functor of accessible functors is accessible. -/
theorem isCardinalAccessible_colimit
    {C : Type uC} [Category.{vC} C]
    {D : Type uD} [Category.{vD} D]
    {I : Type uI} [Category.{vI} I] [HasColimitsOfShape I D]
    (μ : Cardinal.{μU}) [Fact μ.IsRegular]
    (H : I ⥤ C ⥤ D) [∀ i, (H.obj i).IsCardinalAccessible μ] :
    (colimit H).IsCardinalAccessible μ := by
  have hFlip : H.flip.IsCardinalAccessible μ := by
    refine { preservesColimitOfShape := fun J _ _ => ?_ }
    apply preservesColimitsOfShape_of_evaluation H.flip J
    intro i
    change PreservesColimitsOfShape J (H.obj i)
    exact (H.obj i).preservesColimitsOfShape_of_isCardinalAccessible μ J
  let _ : H.flip.IsCardinalAccessible μ := hFlip
  let _ : PreservesColimitsOfSize.{μU, μU} (colim : (I ⥤ D) ⥤ D) :=
    (colimConstAdj (J := I) (C := D)).leftAdjoint_preservesColimits
  let _ : (colim : (I ⥤ D) ⥤ D).IsCardinalAccessible μ := inferInstance
  let _ : (H.flip ⋙ (colim : (I ⥤ D) ⥤ D)).IsCardinalAccessible μ := inferInstance
  exact isCardinalAccessible_of_natIso (colimitIsoFlipCompColim H).symm μ

/-- The SAME supplied original colimit cocone point is accessible. -/
theorem isCardinalAccessible_of_isColimit
    {C : Type uC} [Category.{vC} C]
    {D : Type uD} [Category.{vD} D]
    {I : Type uI} [Category.{vI} I] [HasColimitsOfShape I D]
    (μ : Cardinal.{μU}) [Fact μ.IsRegular]
    (H : I ⥤ C ⥤ D) [∀ i, (H.obj i).IsCardinalAccessible μ]
    (c : Cocone H) (hc : IsColimit c) : c.pt.IsCardinalAccessible μ := by
  let _ : (colimit H).IsCardinalAccessible μ := isCardinalAccessible_colimit μ H
  let e : colimit H ≅ c.pt := (colimit.isColimit H).coconePointUniqueUpToIso hc
  exact isCardinalAccessible_of_natIso e μ

end CategoryTheory.Functor
