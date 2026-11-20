/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/




import Code.FrontierD.FKRectRefinedIntersectionCriterion










namespace StatMech.FrontierD

open StatMech.Onsager
open IntegralSquareTorusCycle

noncomputable section



def fkRectSquareCoverDartList (R : FKRectTorus)
    (l : List FKRectIntegralSquareDart) (u : Int × Int) :
    List (ons_Dart (fkRectSquareCoverSide R)) :=
  (fkRectRepeatTranslatedDartPath l u (fkRectSquareCoverSide R)).map
    (fkRectIntegralSquareDartMod (fkRectSquareCoverSide R))



theorem fkRectSquareCoverDartList_balanced
    (R : FKRectTorus) {p u : Int × Int}
    {l : List FKRectIntegralSquareDart}
    (h : FKRectIntegralSquareDartPath p
      (p.1 + u.1, p.2 + u.2) l) :
    DartListBalanced (fkRectSquareCoverDartList R l u) := by
  let L := fkRectSquareCoverSide R
  have hrepeated : FKRectIntegralSquareDartPath p
      (p.1 + (L : Int) * u.1, p.2 + (L : Int) * u.2)
      (fkRectRepeatTranslatedDartPath l u L) :=
    h.repeatTranslated L
  have hpointMod : fkRectIntegralSquarePointMod L p =
      fkRectIntegralSquarePointMod L
        (p.1 + (L : Int) * u.1, p.2 + (L : Int) * u.2) := by
    apply Prod.ext <;> simp [fkRectIntegralSquarePointMod]
  exact hrepeated.dartListBalanced_of_pointMod_eq L hpointMod



theorem fkRectSquareCoverDartList_xWrap_eq
    (R : FKRectTorus) {p u : Int × Int}
    {l : List FKRectIntegralSquareDart}
    (h : FKRectIntegralSquareDartPath p
      (p.1 + u.1, p.2 + u.2) l) :
    ((fkRectSquareCoverDartList R l u).map ons_xWrapSign).sum = u.1 := by
  let L := fkRectSquareCoverSide R
  have hrepeated : FKRectIntegralSquareDartPath p
      (p.1 + (L : Int) * u.1, p.2 + (L : Int) * u.2)
      (fkRectRepeatTranslatedDartPath l u L) :=
    h.repeatTranslated L
  have hpointMod : fkRectIntegralSquarePointMod L p =
      fkRectIntegralSquarePointMod L
        (p.1 + (L : Int) * u.1, p.2 + (L : Int) * u.2) := by
    apply Prod.ext <;> simp [fkRectIntegralSquarePointMod]
  have hx := hrepeated.displacement_x_eq_wrap (L := L)
  rw [hpointMod] at hx
  simp only [sub_self, zero_add, add_sub_cancel_left] at hx
  have hL : (L : Int) ≠ 0 := by
    exact_mod_cast (ne_of_gt (lt_trans (by norm_num : 0 < 2)
      (fkRectSquareCoverSide_gt_two R)))
  apply mul_left_cancel₀ hL
  dsimp [fkRectSquareCoverDartList, L]
  exact hx.symm



theorem fkRectSquareCoverDartList_yWrap_eq
    (R : FKRectTorus) {p u : Int × Int}
    {l : List FKRectIntegralSquareDart}
    (h : FKRectIntegralSquareDartPath p
      (p.1 + u.1, p.2 + u.2) l) :
    ((fkRectSquareCoverDartList R l u).map ons_yWrapSign).sum = u.2 := by
  let L := fkRectSquareCoverSide R
  have hrepeated : FKRectIntegralSquareDartPath p
      (p.1 + (L : Int) * u.1, p.2 + (L : Int) * u.2)
      (fkRectRepeatTranslatedDartPath l u L) :=
    h.repeatTranslated L
  have hpointMod : fkRectIntegralSquarePointMod L p =
      fkRectIntegralSquarePointMod L
        (p.1 + (L : Int) * u.1, p.2 + (L : Int) * u.2) := by
    apply Prod.ext <;> simp [fkRectIntegralSquarePointMod]
  have hy := hrepeated.displacement_y_eq_wrap (L := L)
  rw [hpointMod] at hy
  simp only [sub_self, zero_add, add_sub_cancel_left] at hy
  have hL : (L : Int) ≠ 0 := by
    exact_mod_cast (ne_of_gt (lt_trans (by norm_num : 0 < 2)
      (fkRectSquareCoverSide_gt_two R)))
  apply mul_left_cancel₀ hL
  dsimp [fkRectSquareCoverDartList, L]
  exact hy.symm




theorem fkRectSquareCoverDartList_interaction_ne_zero_iff
    (R : FKRectTorus) [Fact (8 < fkRectSquareCoverSide R)]
    {p q u v : Int × Int}
    {a b : List FKRectIntegralSquareDart}
    (ha : FKRectIntegralSquareDartPath p
      (p.1 + u.1, p.2 + u.2) a)
    (hb : FKRectIntegralSquareDartPath q
      (q.1 + v.1, q.2 + v.2) b) :
    fkRectRefinedRawInteraction
        (fkRectSquareCoverDartList R a u)
        (fkRectSquareCoverDartList R b v) ≠ 0 ↔
      FKRectWindingIndependent u v := by
  rw [fkRectRefinedRawInteraction_ne_zero_iff_windingIndependent
    _ _ (fkRectSquareCoverDartList_balanced R ha)
      (fkRectSquareCoverDartList_balanced R hb),
    fkRectSquareCoverDartList_xWrap_eq R ha,
    fkRectSquareCoverDartList_yWrap_eq R ha,
    fkRectSquareCoverDartList_xWrap_eq R hb,
    fkRectSquareCoverDartList_yWrap_eq R hb]


theorem fkRectSquareCoverDartList_interaction_eq_zero_iff
    (R : FKRectTorus) [Fact (8 < fkRectSquareCoverSide R)]
    {p q u v : Int × Int}
    {a b : List FKRectIntegralSquareDart}
    (ha : FKRectIntegralSquareDartPath p
      (p.1 + u.1, p.2 + u.2) a)
    (hb : FKRectIntegralSquareDartPath q
      (q.1 + v.1, q.2 + v.2) b) :
    fkRectRefinedRawInteraction
        (fkRectSquareCoverDartList R a u)
        (fkRectSquareCoverDartList R b v) = 0 ↔
      ¬ FKRectWindingIndependent u v := by
  rw [fkRectRefinedRawInteraction_eq_zero_iff_not_windingIndependent
    _ _ (fkRectSquareCoverDartList_balanced R ha)
      (fkRectSquareCoverDartList_balanced R hb),
    fkRectSquareCoverDartList_xWrap_eq R ha,
    fkRectSquareCoverDartList_yWrap_eq R ha,
    fkRectSquareCoverDartList_xWrap_eq R hb,
    fkRectSquareCoverDartList_yWrap_eq R hb]

end

end StatMech.FrontierD
