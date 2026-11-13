/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/




import Code.FrontierD.FKRectRefinedBoundary



open scoped BigOperators
open Finset

namespace StatMech.FrontierD

open StatMech.Onsager
open IntegralSquareTorusCycle

noncomputable section



def fkRectRefinedCoverTorus (R : FKRectTorus) : FKRectTorus where
  width := 4 * R.width
  height := R.height
  width_gt_two := by
    have := R.width_pos
    omega
  height_gt_two := R.height_gt_two
  height_even := R.height_even

@[simp] theorem fkRectRefinedCoverSide_eq (R : FKRectTorus) :
    fkRectSquareCoverSide (fkRectRefinedCoverTorus R) =
      4 * fkRectSquareCoverSide R := by
  simp [fkRectRefinedCoverTorus, fkRectSquareCoverSide, Nat.mul_assoc]

theorem fkRectSquareCoverSide_gt_eight (R : FKRectTorus) :
    8 < fkRectSquareCoverSide R := by
  have hw : 3 <= R.width := R.width_gt_two
  have hh : 3 <= R.height := R.height_gt_two
  calc
    8 < 3 * 3 := by norm_num
    _ <= R.width * R.height := by
      simpa [fkRectSquareCoverSide] using Nat.mul_le_mul hw hh

instance fkRectRefinedCoverSide_fact_eight (R : FKRectTorus) :
    Fact (8 < fkRectSquareCoverSide (fkRectRefinedCoverTorus R)) :=
  ⟨fkRectSquareCoverSide_gt_eight (fkRectRefinedCoverTorus R)⟩

theorem FKRectSquareCoverCycleWitness.windingIndependent_of_intersection_ne_zero
    {R : FKRectTorus} {u v : Int × Int}
    (C : FKRectSquareCoverCycleWitness R u)
    (D : FKRectSquareCoverCycleWitness R v)
    (hne : C.cycle.intersection D.cycle ≠ 0) :
    FKRectWindingIndependent u v := by
  unfold FKRectWindingIndependent
  intro hdet
  apply hne
  rw [C.cycle.intersection_eq_flux_det D.cycle,
    C.xFlux_eq, C.yFlux_eq, D.xFlux_eq, D.yFlux_eq, hdet]

theorem fkRectWindingIndependent_four_iff (u v : Int × Int) :
    FKRectWindingIndependent (4 * u.1, 4 * u.2)
        (4 * v.1, 4 * v.2) <->
      FKRectWindingIndependent u v := by
  unfold FKRectWindingIndependent
  constructor
  · intro h hz
    apply h
    linear_combination 16 * hz
  · intro h hs
    apply h
    have hscaled : (16 : Int) * (u.1 * v.2 - u.2 * v.1) = 0 := by
      linear_combination hs
    exact (mul_eq_zero.mp hscaled).resolve_left (by norm_num)

theorem fkRectWindingIndependent_four_squareDeck_iff
    (R : FKRectTorus) (u v : Int × Int) :
    FKRectWindingIndependent
        (4 * (fkRectSquareDeckTranslation R u).1,
          4 * (fkRectSquareDeckTranslation R u).2)
        (4 * (fkRectSquareDeckTranslation R v).1,
          4 * (fkRectSquareDeckTranslation R v).2) <->
      FKRectWindingIndependent u v := by
  rw [fkRectWindingIndependent_four_iff,
    fkRectWindingIndependent_squareDeck_iff]

theorem not_windingIndependent_trans_of_middle_ne_zero
    (u b v : Int × Int) (hb : b ≠ (0, 0))
    (hub : ¬ FKRectWindingIndependent u b)
    (hbv : ¬ FKRectWindingIndependent b v) :
    ¬ FKRectWindingIndependent u v := by
  unfold FKRectWindingIndependent at hub hbv ⊢
  simp only [not_ne_iff] at hub hbv ⊢
  have hcoord : b.1 ≠ 0 ∨ b.2 ≠ 0 := by
    by_contra h
    push Not at h
    exact hb (Prod.ext h.1 h.2)
  rcases hcoord with hb1 | hb2
  · have hmul : b.1 * (u.1 * v.2 - u.2 * v.1) = 0 := by
      linear_combination u.1 * hbv + v.1 * hub
    exact (mul_eq_zero.mp hmul).resolve_left hb1
  · have hmul : b.2 * (u.1 * v.2 - u.2 * v.1) = 0 := by
      linear_combination v.2 * hub + u.2 * hbv
    exact (mul_eq_zero.mp hmul).resolve_left hb2

variable {L : Nat} [Fact (8 < L)]

local instance : Fact (2 < L) :=
  ⟨lt_trans (by omega) (Fact.out : 8 < L)⟩

local instance : Fact (1 < L) :=
  ⟨lt_trans (by omega) (Fact.out : 8 < L)⟩


def fkRectRefinedRawInteraction (v w : List (ons_Dart L)) : Int :=
  ∑ p : ZMod L × ZMod L,
    ((v.map (fun d => dartHorizontal d p)).sum *
        (w.map (fun d => dartVertical d (p.1, p.2 - 1))).sum -
      (v.map (fun d => dartVertical d p)).sum *
        (w.map (fun d => dartHorizontal d (p.1 - 1, p.2))).sum)

theorem fkRectRefinedRawInteraction_append_left
    (a b c : List (ons_Dart L)) :
    fkRectRefinedRawInteraction (a ++ b) c =
      fkRectRefinedRawInteraction a c +
        fkRectRefinedRawInteraction b c := by
  classical
  unfold fkRectRefinedRawInteraction
  simp only [List.map_append, List.sum_append, add_mul,
    Finset.sum_add_distrib, Finset.sum_sub_distrib]
  ring

theorem fkRectRefinedRawInteraction_append_right
    (a b c : List (ons_Dart L)) :
    fkRectRefinedRawInteraction a (b ++ c) =
      fkRectRefinedRawInteraction a b +
        fkRectRefinedRawInteraction a c := by
  classical
  unfold fkRectRefinedRawInteraction
  simp only [List.map_append, List.sum_append, mul_add,
    Finset.sum_add_distrib, Finset.sum_sub_distrib]
  ring

theorem fkRectRefinedRawInteraction_eq_intersection
    (a b : List (ons_Dart L))
    (ha : DartListBalanced a) (hb : DartListBalanced b) :
    fkRectRefinedRawInteraction a b =
      (ofDartList a ha).intersection (ofDartList b hb) :=
  rfl

theorem fkRectRefinedRawInteraction_eq_wrap_det
    (a b : List (ons_Dart L))
    (ha : DartListBalanced a) (hb : DartListBalanced b) :
    fkRectRefinedRawInteraction a b =
      (a.map ons_xWrapSign).sum * (b.map ons_yWrapSign).sum -
        (a.map ons_yWrapSign).sum * (b.map ons_xWrapSign).sum := by
  rw [fkRectRefinedRawInteraction_eq_intersection a b ha hb,
    IntegralSquareTorusCycle.intersection_eq_flux_det,
    IntegralSquareTorusCycle.ofDartList_xFlux,
    IntegralSquareTorusCycle.ofDartList_yFlux,
    IntegralSquareTorusCycle.ofDartList_xFlux,
    IntegralSquareTorusCycle.ofDartList_yFlux]


def fkRectRefinedPointTranslate (u p : ZMod L × ZMod L) :
    ZMod L × ZMod L :=
  (p.1 + u.1, p.2 + u.2)


def fkRectRefinedDartTranslateMod (u : ZMod L × ZMod L)
    (d : ons_Dart L) : ons_Dart L :=
  (fkRectRefinedPointTranslate u d.1, d.2)

private theorem pointMass_translate
    (u a p : ZMod L × ZMod L) :
    pointMass (fkRectRefinedPointTranslate u a)
        (fkRectRefinedPointTranslate u p) = pointMass a p := by
  unfold pointMass fkRectRefinedPointTranslate
  congr 1
  apply propext
  simp only [Prod.ext_iff]
  constructor <;> rintro ⟨h1, h2⟩
  · exact ⟨add_right_cancel h1, add_right_cancel h2⟩
  · exact ⟨congrArg (fun z => z + u.1) h1,
      congrArg (fun z => z + u.2) h2⟩

private theorem dartHorizontal_translate
    (u p : ZMod L × ZMod L) (d : ons_Dart L) :
    dartHorizontal (fkRectRefinedDartTranslateMod u d)
        (fkRectRefinedPointTranslate u p) = dartHorizontal d p := by
  rcases d with ⟨⟨x, y⟩, mu⟩
  fin_cases mu
  · change pointMass (fkRectRefinedPointTranslate u (x, y))
        (fkRectRefinedPointTranslate u p) = pointMass (x, y) p
    exact pointMass_translate u (x, y) p
  · simp [dartHorizontal, fkRectRefinedDartTranslateMod]
  · change -pointMass (x + u.1 - 1, y + u.2)
        (fkRectRefinedPointTranslate u p) = -pointMass (x - 1, y) p
    rw [show (x + u.1 - 1, y + u.2) =
        fkRectRefinedPointTranslate u (x - 1, y) by
      apply Prod.ext <;> simp [fkRectRefinedPointTranslate] <;> ring,
      pointMass_translate]
  · simp [dartHorizontal, fkRectRefinedDartTranslateMod]

private theorem dartVertical_translate
    (u p : ZMod L × ZMod L) (d : ons_Dart L) :
    dartVertical (fkRectRefinedDartTranslateMod u d)
        (fkRectRefinedPointTranslate u p) = dartVertical d p := by
  rcases d with ⟨⟨x, y⟩, mu⟩
  fin_cases mu
  · simp [dartVertical, fkRectRefinedDartTranslateMod]
  · change pointMass (fkRectRefinedPointTranslate u (x, y))
        (fkRectRefinedPointTranslate u p) = pointMass (x, y) p
    exact pointMass_translate u (x, y) p
  · simp [dartVertical, fkRectRefinedDartTranslateMod]
  · change -pointMass (x + u.1, y + u.2 - 1)
        (fkRectRefinedPointTranslate u p) = -pointMass (x, y - 1) p
    rw [show (x + u.1, y + u.2 - 1) =
        fkRectRefinedPointTranslate u (x, y - 1) by
      apply Prod.ext <;> simp [fkRectRefinedPointTranslate] <;> ring,
      pointMass_translate]



theorem fkRectRefinedRawInteraction_translate
    (u : ZMod L × ZMod L) (a b : List (ons_Dart L)) :
    fkRectRefinedRawInteraction
        (a.map (fkRectRefinedDartTranslateMod u))
        (b.map (fkRectRefinedDartTranslateMod u)) =
      fkRectRefinedRawInteraction a b := by
  classical
  unfold fkRectRefinedRawInteraction
  rw [show (∑ p : ZMod L × ZMod L, _) =
      ∑ p : ZMod L × ZMod L,
        (((a.map (fkRectRefinedDartTranslateMod u)).map
            (fun d => dartHorizontal d
              (fkRectRefinedPointTranslate u p))).sum *
          ((b.map (fkRectRefinedDartTranslateMod u)).map
            (fun d => dartVertical d
              ((fkRectRefinedPointTranslate u p).1,
                (fkRectRefinedPointTranslate u p).2 - 1))).sum -
          ((a.map (fkRectRefinedDartTranslateMod u)).map
            (fun d => dartVertical d
              (fkRectRefinedPointTranslate u p))).sum *
          ((b.map (fkRectRefinedDartTranslateMod u)).map
            (fun d => dartHorizontal d
              ((fkRectRefinedPointTranslate u p).1 - 1,
                (fkRectRefinedPointTranslate u p).2))).sum) by
    simpa [fkRectRefinedPointTranslate] using
      (Equiv.sum_comp
        (Equiv.prodCongr (Equiv.addRight u.1) (Equiv.addRight u.2))
        (fun p : ZMod L × ZMod L =>
          (((a.map (fkRectRefinedDartTranslateMod u)).map
              (fun d => dartHorizontal d p)).sum *
            ((b.map (fkRectRefinedDartTranslateMod u)).map
              (fun d => dartVertical d (p.1, p.2 - 1))).sum -
            ((a.map (fkRectRefinedDartTranslateMod u)).map
              (fun d => dartVertical d p)).sum *
            ((b.map (fkRectRefinedDartTranslateMod u)).map
              (fun d => dartHorizontal d (p.1 - 1, p.2))).sum))).symm]
  apply Finset.sum_congr rfl
  intro p hp
  simp only [List.map_map]
  have hs : ((fkRectRefinedPointTranslate u p).1,
      (fkRectRefinedPointTranslate u p).2 - 1) =
      fkRectRefinedPointTranslate u (p.1, p.2 - 1) := by
    apply Prod.ext <;> simp [fkRectRefinedPointTranslate] <;> ring
  have hw : ((fkRectRefinedPointTranslate u p).1 - 1,
      (fkRectRefinedPointTranslate u p).2) =
      fkRectRefinedPointTranslate u (p.1 - 1, p.2) := by
    apply Prod.ext <;> simp [fkRectRefinedPointTranslate] <;> ring
  rw [hs, hw]
  rw [show (fun d => dartHorizontal d
        (fkRectRefinedPointTranslate u p)) ∘
        fkRectRefinedDartTranslateMod u =
      fun d => dartHorizontal d p from
    funext (fun d => dartHorizontal_translate u p d)]
  rw [show (fun d => dartVertical d
        (fkRectRefinedPointTranslate u (p.1, p.2 - 1))) ∘
        fkRectRefinedDartTranslateMod u =
      fun d => dartVertical d (p.1, p.2 - 1) from
    funext (fun d => dartVertical_translate u (p.1, p.2 - 1) d)]
  rw [show (fun d => dartVertical d
        (fkRectRefinedPointTranslate u p)) ∘
        fkRectRefinedDartTranslateMod u =
      fun d => dartVertical d p from
    funext (fun d => dartVertical_translate u p d)]
  rw [show (fun d => dartHorizontal d
        (fkRectRefinedPointTranslate u (p.1 - 1, p.2))) ∘
        fkRectRefinedDartTranslateMod u =
      fun d => dartHorizontal d (p.1 - 1, p.2) from
    funext (fun d => dartHorizontal_translate u (p.1 - 1, p.2) d)]



theorem fkRectIntegralSquareDartMod_translate
    (u : Int × Int) (d : FKRectIntegralSquareDart) :
    fkRectIntegralSquareDartMod L
        (fkRectIntegralSquareDartTranslate u d) =
      fkRectRefinedDartTranslateMod ((u.1 : ZMod L), (u.2 : ZMod L))
        (fkRectIntegralSquareDartMod L d) := by
  rcases d with ⟨⟨x, y⟩, mu⟩
  apply Prod.ext
  · apply Prod.ext <;>
      simp [fkRectIntegralSquareDartMod,
        fkRectIntegralSquareDartTranslate,
        fkRectRefinedDartTranslateMod, fkRectRefinedPointTranslate]
  · rfl



theorem fkRectRefinedRawInteraction_integralTranslate
    (u : Int × Int)
    (a b : List FKRectIntegralSquareDart) :
    fkRectRefinedRawInteraction
        ((a.map (fkRectIntegralSquareDartTranslate u)).map
          (fkRectIntegralSquareDartMod L))
        ((b.map (fkRectIntegralSquareDartTranslate u)).map
          (fkRectIntegralSquareDartMod L)) =
      fkRectRefinedRawInteraction
        (a.map (fkRectIntegralSquareDartMod L))
        (b.map (fkRectIntegralSquareDartMod L)) := by
  simpa only [List.map_map, Function.comp_def,
    fkRectIntegralSquareDartMod_translate] using
    fkRectRefinedRawInteraction_translate
      (L := L) ((u.1 : ZMod L), (u.2 : ZMod L))
      (a.map (fkRectIntegralSquareDartMod L))
      (b.map (fkRectIntegralSquareDartMod L))

end

end StatMech.FrontierD
