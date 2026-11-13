/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/




import Code.FK.PeriodicPlanarSheffieldPreferenceInterface










open Set SimpleGraph

namespace StatMech.FK.PeriodicPlanar

open Lattice



theorem exists_common_preference_grid_witness
    {n m : Nat} (hn : 0 < n)
    (vertical horizontal : PreferenceGridVertex n m -> Bool)
    (bottomColor topColor : Bool)
    (hbottom : forall i : Fin (n + 1), vertical (i, 0) = bottomColor)
    (htop : forall i : Fin (n + 1),
      vertical (i, Fin.last m) = topColor)
    (hverticalEnds : bottomColor ≠ topColor)
    (hleft : forall j : Fin (m + 1), horizontal (0, j) = true)
    (hright : forall j : Fin (m + 1),
      horizontal (Fin.last n, j) = false) :
    exists x : PreferenceGridVertex n m,
      vertical x = true /\ horizontal x = true /\
      (exists xVertical : PreferenceGridVertex n m,
        KingAdj (preferenceGridSite x) (preferenceGridSite xVertical) /\
          vertical xVertical = false) /\
      (exists xHorizontal : PreferenceGridVertex n m,
        KingAdj (preferenceGridSite x) (preferenceGridSite xHorizontal) /\
          horizontal xHorizontal = false) := by
  classical
  have hreach := preferenceInterface_left_reachable_right vertical hn
    bottomColor topColor hbottom htop hverticalEnds
  have hbottomDegree :=
    preferenceInterface_bottom_degree_zero vertical bottomColor hbottom
  have htopDegree :=
    preferenceInterface_top_degree_zero vertical topColor htop
  have hflag := preferenceFlagCrossing_of_reachable vertical
    hbottomDegree htopDegree hreach
  obtain ⟨leftPoint, rightPoint, hleftCol, hrightCol, hboundary⟩ :=
    preferenceGridBoundary_reachable_left_right_of_flagCrossing vertical hflag
  have hsiteReach := hboundary.map (preferenceGridBoundaryGraphHom vertical)
  obtain ⟨p⟩ := hsiteReach
  let leftSite := preferenceGridBoundaryToSite vertical leftPoint
  let rightSite := preferenceGridBoundaryToSite vertical rightPoint
  have hleftMem : (leftSite : Site 2) ∈ preferenceGridTrueSet horizontal := by
    have hi : leftPoint.val.1 = 0 := Fin.ext hleftCol
    have hp : leftPoint.val = (0, leftPoint.val.2) := Prod.ext hi rfl
    refine ⟨leftPoint.val, ?_, rfl⟩
    change horizontal leftPoint.val = true
    rw [hp]
    exact hleft leftPoint.val.2
  have hrightNot : (rightSite : Site 2) ∉ preferenceGridTrueSet horizontal := by
    have hi : rightPoint.val.1 = Fin.last n := Fin.ext hrightCol
    have hp : rightPoint.val = (Fin.last n, rightPoint.val.2) := Prod.ext hi rfl
    rintro ⟨z, hz, heq⟩
    have hzr : z = rightPoint.val := preferenceGridSite_injective heq
    subst z
    change horizontal rightPoint.val = true at hz
    rw [hp] at hz
    exact Bool.noConfusion ((hright rightPoint.val.2).symm.trans hz)
  have hwitness := exists_preference_witness_of_boundary_walk
    (preferenceGridRectangle n m) (preferenceGridTrueSet vertical)
    (preferenceGridTrueSet horizontal) p hleftMem hrightNot
  obtain ⟨xSite, hxRect, hxVertical, hxHorizontal,
      ⟨xVerticalSite, hxVerticalRect, hxVerticalAdj, hxVerticalNot⟩,
      ⟨xHorizontalSite, hxHorizontalRect, hxHorizontalAdj,
        hxHorizontalNot⟩⟩ := hwitness
  obtain ⟨x, _hxuniv, hx⟩ := hxRect
  have hxVtrue : vertical x = true := by
    obtain ⟨z, hz, hzx⟩ := hxVertical
    have hzx' : z = x := preferenceGridSite_injective (hzx.trans hx.symm)
    simpa [hzx'] using hz
  have hxHtrue : horizontal x = true := by
    obtain ⟨z, hz, hzx⟩ := hxHorizontal
    have hzx' : z = x := preferenceGridSite_injective (hzx.trans hx.symm)
    simpa [hzx'] using hz
  obtain ⟨xVertical, _hxVerticalUniv, hxVerticalEq⟩ := hxVerticalRect
  have hxVerticalFalse : vertical xVertical = false := by
    cases hcolor : vertical xVertical with
    | false => rfl
    | true =>
        exact (hxVerticalNot ⟨xVertical, hcolor, hxVerticalEq⟩).elim
  obtain ⟨xHorizontal, _hxHorizontalUniv, hxHorizontalEq⟩ := hxHorizontalRect
  have hxHorizontalFalse : horizontal xHorizontal = false := by
    cases hcolor : horizontal xHorizontal with
    | false => rfl
    | true =>
        exact (hxHorizontalNot ⟨xHorizontal, hcolor, hxHorizontalEq⟩).elim
  refine ⟨x, hxVtrue, hxHtrue, ⟨xVertical, ?_, hxVerticalFalse⟩,
    ⟨xHorizontal, ?_, hxHorizontalFalse⟩⟩
  · simpa only [hx, hxVerticalEq] using hxVerticalAdj
  · simpa only [hx, hxHorizontalEq] using hxHorizontalAdj

end StatMech.FK.PeriodicPlanar
