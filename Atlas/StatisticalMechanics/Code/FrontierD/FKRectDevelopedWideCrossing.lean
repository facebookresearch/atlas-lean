/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/




import Code.FrontierD.FKRectDevelopedSquare
import Code.Lattice.JordanExteriorClosure
import Code.Universality.BXPAspectTransfer



open Set

namespace StatMech.FrontierD

open StatMech.Lattice
open StatMech.RSW.Box

noncomputable section



def fkRectDevelopedRectangleHorizontalCrossingEvent
    (R : FKRectTorus) (placement : Nat) (a b c d : Int) :
    Set R.Configuration :=
  fkRectDevelopedSquarePullback R placement ⁻¹'
    horizontalCrossingEvent a b c d



def fkRectDevelopedRectangleVerticalCrossingEvent
    (R : FKRectTorus) (placement : Nat) (a b c d : Int) :
    Set R.Configuration :=
  fkRectDevelopedSquarePullback R placement ⁻¹'
    verticalCrossingEvent a b c d

theorem fkRectDevelopedRectangleHorizontalCrossingEvent_isIncreasing
    (R : FKRectTorus) (placement : Nat) (a b c d : Int) :
    IsIncreasing
      (fkRectDevelopedRectangleHorizontalCrossingEvent
        R placement a b c d) := by
  intro omega tau hot hcross
  exact horizontalCrossingEvent_increasing
    (fkRectDevelopedSquarePullback_mono R placement hot) hcross

theorem fkRectDevelopedRectangleVerticalCrossingEvent_isIncreasing
    (R : FKRectTorus) (placement : Nat) (a b c d : Int) :
    IsIncreasing
      (fkRectDevelopedRectangleVerticalCrossingEvent
        R placement a b c d) := by
  intro omega tau hot hcross
  exact verticalCrossingEvent_increasing
    (fkRectDevelopedSquarePullback_mono R placement hot) hcross




theorem fkRectDevelopedRectangle_HVH_subset_horizontal
    (R : FKRectTorus) (placement : Nat)
    {a m m' b c d : Int}
    (ham : a <= m) (hmm' : m <= m') (hm'b : m' <= b)
    (hamL : a < m') (hmbR : m < b) (hcd : c <= d) :
    (fkRectDevelopedRectangleHorizontalCrossingEvent
          R placement a m' c d ∩
        fkRectDevelopedRectangleVerticalCrossingEvent
          R placement m m' c d) ∩
      fkRectDevelopedRectangleHorizontalCrossingEvent
        R placement m b c d ⊆
      fkRectDevelopedRectangleHorizontalCrossingEvent
        R placement a b c d := by
  intro omega homega
  let sigma := fkRectDevelopedSquarePullback R placement omega
  have hsepL := StatMech.Universality.vsFix_arc_sides_imp
    sigma a m' m m' c d
      (StatMech.Lattice.jec_vsFix_arc_sides sigma hamL hcd)
  have hsepR := StatMech.Universality.vsFix_arc_sides_imp
    sigma m b m m' c d
      (StatMech.Lattice.jec_vsFix_arc_sides sigma hmbR hcd)
  have hinter := StatMech.Universality.vsFix_hvIntersection
    sigma ham hmm' hm'b hsepL hsepR
  exact hinter homega.1.1 homega.1.2 homega.2


theorem fkRectCritical_developedRectangle_horizontalMass_ge_HVH
    (R : FKRectTorus) (placement : Nat) {q : Real} (hq : 1 <= q)
    {a m m' b c d : Int}
    (ham : a <= m) (hmm' : m <= m') (hm'b : m' <= b)
    (hamL : a < m') (hmbR : m < b) (hcd : c <= d) :
    fkRectCriticalEventMass R q
          (fkRectDevelopedRectangleHorizontalCrossingEvent
            R placement a m' c d) *
        fkRectCriticalEventMass R q
          (fkRectDevelopedRectangleVerticalCrossingEvent
            R placement m m' c d) *
        fkRectCriticalEventMass R q
          (fkRectDevelopedRectangleHorizontalCrossingEvent
            R placement m b c d) <=
      fkRectCriticalEventMass R q
        (fkRectDevelopedRectangleHorizontalCrossingEvent
          R placement a b c d) := by
  let A := fkRectDevelopedRectangleHorizontalCrossingEvent
    R placement a m' c d
  let B := fkRectDevelopedRectangleVerticalCrossingEvent
    R placement m m' c d
  let C := fkRectDevelopedRectangleHorizontalCrossingEvent
    R placement m b c d
  let D := fkRectDevelopedRectangleHorizontalCrossingEvent
    R placement a b c d
  have hA : IsIncreasing A :=
    fkRectDevelopedRectangleHorizontalCrossingEvent_isIncreasing
      R placement a m' c d
  have hB : IsIncreasing B :=
    fkRectDevelopedRectangleVerticalCrossingEvent_isIncreasing
      R placement m m' c d
  have hC : IsIncreasing C :=
    fkRectDevelopedRectangleHorizontalCrossingEvent_isIncreasing
      R placement m b c d
  have hAB : IsIncreasing (A ∩ B) := by
    intro omega tau hot homega
    exact ⟨hA hot homega.1, hB hot homega.2⟩
  have hq0 : 0 < q := zero_lt_one.trans_le hq
  calc
    fkRectCriticalEventMass R q A *
          fkRectCriticalEventMass R q B *
        fkRectCriticalEventMass R q C <=
      fkRectCriticalEventMass R q (A ∩ B) *
        fkRectCriticalEventMass R q C :=
      mul_le_mul_of_nonneg_right
        (fkRectCriticalEventMass_mul_le_inter R hq hA hB)
        (fkRectCriticalEventMass_nonneg R hq0 C)
    _ <= fkRectCriticalEventMass R q ((A ∩ B) ∩ C) :=
      fkRectCriticalEventMass_mul_le_inter R hq hAB hC
    _ <= fkRectCriticalEventMass R q D :=
      fkRectCriticalEventMass_mono R hq0
        (fkRectDevelopedRectangle_HVH_subset_horizontal
          R placement ham hmm' hm'b hamL hmbR hcd)



theorem fkRectDevelopedRectangle_VHV_subset_vertical
    (R : FKRectTorus) (placement : Nat)
    {a b c m m' d : Int}
    (hab : a <= b) (hcm : c <= m) (hmm' : m <= m')
    (hm'd : m' <= d) (hcm' : c < m') (hmd : m < d) :
    (fkRectDevelopedRectangleVerticalCrossingEvent
          R placement a b c m' ∩
        fkRectDevelopedRectangleHorizontalCrossingEvent
          R placement a b m m') ∩
      fkRectDevelopedRectangleVerticalCrossingEvent
        R placement a b m d ⊆
      fkRectDevelopedRectangleVerticalCrossingEvent
        R placement a b c d := by
  intro omega homega
  exact StatMech.Universality.bat_verticalIntersection
    (fkRectDevelopedSquarePullback R placement omega)
    hab hcm hmm' hm'd hcm' hmd homega.1.1 homega.1.2 homega.2


theorem fkRectCritical_developedRectangle_verticalMass_ge_VHV
    (R : FKRectTorus) (placement : Nat) {q : Real} (hq : 1 <= q)
    {a b c m m' d : Int}
    (hab : a <= b) (hcm : c <= m) (hmm' : m <= m')
    (hm'd : m' <= d) (hcm' : c < m') (hmd : m < d) :
    fkRectCriticalEventMass R q
          (fkRectDevelopedRectangleVerticalCrossingEvent
            R placement a b c m') *
        fkRectCriticalEventMass R q
          (fkRectDevelopedRectangleHorizontalCrossingEvent
            R placement a b m m') *
        fkRectCriticalEventMass R q
          (fkRectDevelopedRectangleVerticalCrossingEvent
            R placement a b m d) <=
      fkRectCriticalEventMass R q
        (fkRectDevelopedRectangleVerticalCrossingEvent
          R placement a b c d) := by
  let A := fkRectDevelopedRectangleVerticalCrossingEvent
    R placement a b c m'
  let B := fkRectDevelopedRectangleHorizontalCrossingEvent
    R placement a b m m'
  let C := fkRectDevelopedRectangleVerticalCrossingEvent
    R placement a b m d
  let D := fkRectDevelopedRectangleVerticalCrossingEvent
    R placement a b c d
  have hA : IsIncreasing A :=
    fkRectDevelopedRectangleVerticalCrossingEvent_isIncreasing
      R placement a b c m'
  have hB : IsIncreasing B :=
    fkRectDevelopedRectangleHorizontalCrossingEvent_isIncreasing
      R placement a b m m'
  have hC : IsIncreasing C :=
    fkRectDevelopedRectangleVerticalCrossingEvent_isIncreasing
      R placement a b m d
  have hAB : IsIncreasing (A ∩ B) := by
    intro omega tau hot homega
    exact ⟨hA hot homega.1, hB hot homega.2⟩
  have hq0 : 0 < q := zero_lt_one.trans_le hq
  calc
    fkRectCriticalEventMass R q A *
          fkRectCriticalEventMass R q B *
        fkRectCriticalEventMass R q C <=
      fkRectCriticalEventMass R q (A ∩ B) *
        fkRectCriticalEventMass R q C :=
      mul_le_mul_of_nonneg_right
        (fkRectCriticalEventMass_mul_le_inter R hq hA hB)
        (fkRectCriticalEventMass_nonneg R hq0 C)
    _ <= fkRectCriticalEventMass R q ((A ∩ B) ∩ C) :=
      fkRectCriticalEventMass_mul_le_inter R hq hAB hC
    _ <= fkRectCriticalEventMass R q D :=
      fkRectCriticalEventMass_mono R hq0
        (fkRectDevelopedRectangle_VHV_subset_vertical
          R placement hab hcm hmm' hm'd hcm' hmd)




theorem fkRectCritical_developedThreeByOne_horizontalMass_ge
    (R : FKRectTorus) (n : Nat) {q : Real} (hn : 0 < n) (hq : 1 <= q) :
    fkRectCriticalEventMass R q
          (fkRectDevelopedRectangleHorizontalCrossingEvent
            R n 0 (2 * (n : Int)) 0 n) *
        fkRectCriticalEventMass R q
          (fkRectDevelopedRectangleVerticalCrossingEvent
            R n n (2 * (n : Int)) 0 n) *
        fkRectCriticalEventMass R q
          (fkRectDevelopedRectangleHorizontalCrossingEvent
            R n n (3 * (n : Int)) 0 n) <=
      fkRectCriticalEventMass R q
        (fkRectDevelopedRectangleHorizontalCrossingEvent
          R n 0 (3 * (n : Int)) 0 n) := by
  apply fkRectCritical_developedRectangle_horizontalMass_ge_HVH
    R n hq
  all_goals omega




theorem fkRectCritical_developedOneByThree_verticalMass_ge
    (R : FKRectTorus) (n : Nat) {q : Real} (hn : 0 < n) (hq : 1 <= q) :
    fkRectCriticalEventMass R q
          (fkRectDevelopedRectangleVerticalCrossingEvent
            R n 0 n 0 (2 * (n : Int))) *
        fkRectCriticalEventMass R q
          (fkRectDevelopedRectangleHorizontalCrossingEvent
            R n 0 n n (2 * (n : Int))) *
        fkRectCriticalEventMass R q
          (fkRectDevelopedRectangleVerticalCrossingEvent
            R n 0 n n (3 * (n : Int))) <=
      fkRectCriticalEventMass R q
        (fkRectDevelopedRectangleVerticalCrossingEvent
          R n 0 n 0 (3 * (n : Int))) := by
  apply fkRectCritical_developedRectangle_verticalMass_ge_VHV
    R n hq
  all_goals omega




theorem fkRectCritical_developedThreeByThree_bottomTopHorizontalMass_mul_le_inter
    (R : FKRectTorus) (n : Nat) {q : Real} (hq : 1 <= q) :
    fkRectCriticalEventMass R q
          (fkRectDevelopedRectangleHorizontalCrossingEvent
            R n 0 (3 * (n : Int)) 0 n) *
        fkRectCriticalEventMass R q
          (fkRectDevelopedRectangleHorizontalCrossingEvent
            R n 0 (3 * (n : Int)) (2 * (n : Int)) (3 * (n : Int))) <=
      fkRectCriticalEventMass R q
        (fkRectDevelopedRectangleHorizontalCrossingEvent
              R n 0 (3 * (n : Int)) 0 n ∩
          fkRectDevelopedRectangleHorizontalCrossingEvent
            R n 0 (3 * (n : Int)) (2 * (n : Int)) (3 * (n : Int))) :=
  fkRectCriticalEventMass_mul_le_inter R hq
    (fkRectDevelopedRectangleHorizontalCrossingEvent_isIncreasing
      R n 0 (3 * (n : Int)) 0 n)
    (fkRectDevelopedRectangleHorizontalCrossingEvent_isIncreasing
      R n 0 (3 * (n : Int)) (2 * (n : Int)) (3 * (n : Int)))




theorem fkRectDevelopedSquareVertical_subset_threeByOneVertical
    (R : FKRectTorus) (n : Nat) :
    fkRectDevelopedRectangleVerticalCrossingEvent R n 0 n 0 n ⊆
      fkRectDevelopedRectangleVerticalCrossingEvent
        R n 0 (3 * (n : Int)) 0 n := by
  intro omega hcross
  obtain ⟨x, y, hxy⟩ := hcross
  let sigma := fkRectDevelopedSquarePullback R n omega
  have hsub : rect 0 (n : Int) 0 n ⊆
      rect 0 (3 * (n : Int)) 0 n := by
    intro z hz
    rw [mem_rect] at hz ⊢
    omega
  have hx : (x : Site 2) ∈ bottomSide 0 (3 * (n : Int)) 0 n := by
    exact ⟨hsub x.2.1, x.2.2⟩
  have hy : (y : Site 2) ∈ topSide 0 (3 * (n : Int)) 0 n := by
    exact ⟨hsub y.2.1, y.2.2⟩
  refine ⟨⟨x, hx⟩, ⟨y, hy⟩, ?_⟩
  exact StatMech.RSW.Strip.connectedWithin_mono_set sigma hsub hxy

theorem fkRectCritical_developedSquareVerticalMass_le_threeByOneVerticalMass
    (R : FKRectTorus) (n : Nat) {q : Real} (hq : 0 < q) :
    fkRectCriticalEventMass R q
        (fkRectDevelopedRectangleVerticalCrossingEvent R n 0 n 0 n) <=
      fkRectCriticalEventMass R q
        (fkRectDevelopedRectangleVerticalCrossingEvent
          R n 0 (3 * (n : Int)) 0 n) :=
  fkRectCriticalEventMass_mono R hq
    (fkRectDevelopedSquareVertical_subset_threeByOneVertical R n)

end

end StatMech.FrontierD
