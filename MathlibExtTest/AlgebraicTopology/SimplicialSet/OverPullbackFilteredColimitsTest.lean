/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua
module
public import MathlibExt.AlgebraicTopology.SimplicialSet.OverPullbackFilteredColimits
@[expose] public section
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
universe u v w
open CategoryTheory CategoryTheory.Limits
namespace SSet.SharpSaturation.Tests

/-- Transport the full original colimit cocone data through actual pullback. -/
def originalMappedCocone (J : Type v) [Category.{w} J] [Small.{u} J] [IsFiltered J]
    {X Y : SSet.{u}} (p : X ⟶ Y) (F : J ⥤ Over Y)
    (c : Cocone F) (hc : IsColimit c) :
    IsColimit ((Over.pullback p).mapCocone c) := by
  let _ := overPullback_preservesColimitsOfShape_of_isFiltered J p
  exact isColimitOfPreserves (Over.pullback p) hc

theorem originalFirstLeg {X Y : SSet.{u}} (p : X ⟶ Y)
    {a b : Over Y} (q : a ⟶ b) :
    ((Over.pullback p).map q).left ≫ pullback.fst b.hom p =
      pullback.fst a.hom p ≫ q.left := by
  simp [Over.pullback]

theorem originalSecondLeg {X Y : SSet.{u}} (p : X ⟶ Y)
    {a b : Over Y} (q : a ⟶ b) :
    ((Over.pullback p).map q).left ≫ pullback.snd b.hom p =
      pullback.snd a.hom p := by
  simp [Over.pullback]

end SSet.SharpSaturation.Tests
