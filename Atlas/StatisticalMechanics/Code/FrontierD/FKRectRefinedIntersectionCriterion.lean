/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/




import Code.FrontierD.FKRectRefinedInteractionCore










namespace StatMech.FrontierD

open StatMech.Onsager
open IntegralSquareTorusCycle

noncomputable section



theorem FKRectSquareCoverCycleWitness.windingIndependent_iff_intersection_ne_zero
    {R : FKRectTorus} {u v : Int × Int}
    (C : FKRectSquareCoverCycleWitness R u)
    (D : FKRectSquareCoverCycleWitness R v) :
    FKRectWindingIndependent u v ↔ C.cycle.intersection D.cycle ≠ 0 := by
  unfold FKRectWindingIndependent
  rw [C.cycle.intersection_eq_flux_det D.cycle,
    C.xFlux_eq, C.yFlux_eq, D.xFlux_eq, D.yFlux_eq]



theorem fkRectRefinedSquareCoverIntersection_ne_zero_iff_windingIndependent
    (R : FKRectTorus) (u v : Int × Int)
    (C : FKRectSquareCoverCycleWitness R
      (4 * (fkRectSquareDeckTranslation R u).1,
        4 * (fkRectSquareDeckTranslation R u).2))
    (D : FKRectSquareCoverCycleWitness R
      (4 * (fkRectSquareDeckTranslation R v).1,
        4 * (fkRectSquareDeckTranslation R v).2)) :
    C.cycle.intersection D.cycle ≠ 0 ↔
      FKRectWindingIndependent u v := by
  rw [← C.windingIndependent_iff_intersection_ne_zero D,
    fkRectWindingIndependent_four_squareDeck_iff]



theorem fkRectFourSquareDeck_ne_zero_iff
    (R : FKRectTorus) (u : Int × Int) :
    (4 * (fkRectSquareDeckTranslation R u).1,
        4 * (fkRectSquareDeckTranslation R u).2) ≠ (0, 0) ↔
      u ≠ (0, 0) := by
  constructor
  · intro h hu
    apply h
    rw [hu]
    simp [fkRectSquareDeckTranslation]
  · intro hu hscaled
    apply hu
    apply fkRectSquareDeckHom_injective R
    change fkRectSquareDeckTranslation R u =
      fkRectSquareDeckTranslation R (0, 0)
    have hx := congrArg Prod.fst hscaled
    have hy := congrArg Prod.snd hscaled
    apply Prod.ext
    · simp only [Prod.fst, mul_eq_zero] at hx
      simp [fkRectSquareDeckTranslation]
      exact hx.resolve_left (by norm_num)
    · simp only [Prod.snd, mul_eq_zero] at hy
      simp [fkRectSquareDeckTranslation]
      exact hy.resolve_left (by norm_num)



theorem fkRectRefinedRawInteraction_ne_zero_iff_windingIndependent
    {L : Nat} [Fact (8 < L)] (a b : List (ons_Dart L))
    (ha : DartListBalanced a) (hb : DartListBalanced b) :
    fkRectRefinedRawInteraction a b ≠ 0 ↔
      FKRectWindingIndependent
        ((a.map ons_xWrapSign).sum, (a.map ons_yWrapSign).sum)
        ((b.map ons_xWrapSign).sum, (b.map ons_yWrapSign).sum) := by
  rw [fkRectRefinedRawInteraction_eq_wrap_det a b ha hb]
  rfl


theorem fkRectRefinedRawInteraction_eq_zero_iff_not_windingIndependent
    {L : Nat} [Fact (8 < L)] (a b : List (ons_Dart L))
    (ha : DartListBalanced a) (hb : DartListBalanced b) :
    fkRectRefinedRawInteraction a b = 0 ↔
      ¬ FKRectWindingIndependent
        ((a.map ons_xWrapSign).sum, (a.map ons_yWrapSign).sum)
        ((b.map ons_xWrapSign).sum, (b.map ons_yWrapSign).sum) := by
  rw [← not_ne_iff]
  exact not_congr
    (fkRectRefinedRawInteraction_ne_zero_iff_windingIndependent
      a b ha hb)

end

end StatMech.FrontierD
