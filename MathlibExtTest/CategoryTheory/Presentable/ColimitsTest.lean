/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua, Avocado

module

public import MathlibExt.CategoryTheory.Presentable.Colimits

public section
set_option autoImplicit false
noncomputable section
universe uC vC uI vI μU uJ vJ
open CategoryTheory CategoryTheory.Limits
namespace CategoryTheory.AccessibleColimitsTest
variable {C : Type uC} [Category.{vC} C]
    {I : Type uI} [Category.{vI} I] [HasColimitsOfShape I C]
    (μ : Cardinal.{μU}) [Fact μ.IsRegular]
    (H : I ⥤ C ⥤ C) [∀ i, (H.obj i).IsCardinalAccessible μ]

/-- The SAME supplied original cocone point is accessible. -/
theorem original_cocone_point (c : Cocone H) (hc : IsColimit c) :
    c.pt.IsCardinalAccessible μ := by
  exact Functor.isCardinalAccessible_of_isColimit μ H c hc

/-- Comparison preserves every original injection as a WHOLE natural transformation. -/
theorem original_injection (c : Cocone H) (hc : IsColimit c) (i : I) :
    colimit.ι H i ≫ ((colimit.isColimit H).coconePointUniqueUpToIso hc).hom =
      c.ι.app i :=
  IsColimit.comp_coconePointUniqueUpToIso_hom _ _ i

/-- An independently sized actual test cocone is preserved by the SAME colimit functor. -/
def originalTestCocone {J : Type uJ} [Category.{vJ} J]
    [EssentiallySmall.{μU} J] [IsCardinalFiltered J μ]
    {G : J ⥤ C} (c : Cocone G) (hc : IsColimit c) :
    IsColimit ((colimit H).mapCocone c) := by
  let _ : (colimit H).IsCardinalAccessible μ := Functor.isCardinalAccessible_colimit μ H
  let _ : PreservesColimitsOfShape J (colimit H) :=
    (colimit H).preservesColimitsOfShape_of_isCardinalAccessible_of_essentiallySmall μ J
  exact isColimitOfPreserves (colimit H) hc

/-- Empty I uses the actual initial colimit. The empty condition specializes
this client; the general accessibility proof also applies to this case. -/
theorem empty_index [_emptyIndex : IsEmpty I] : (colimit H).IsCardinalAccessible μ :=
  Functor.isCardinalAccessible_colimit μ H

end CategoryTheory.AccessibleColimitsTest
