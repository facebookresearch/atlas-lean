/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/




import Code.FrontierD.FKRectRefinedInteractionCore










open scoped BigOperators
open Finset

namespace StatMech.FrontierD

open StatMech.Onsager
open IntegralSquareTorusCycle

noncomputable section

variable {L : Nat} [Fact (8 < L)]

local instance : Fact (2 < L) :=
  ⟨lt_trans (by omega) (Fact.out : 8 < L)⟩

local instance : Fact (1 < L) :=
  ⟨lt_trans (by omega) (Fact.out : 8 < L)⟩

private theorem pointMass_mul_sum (a b : ZMod L × ZMod L) :
    (∑ p, pointMass a p * pointMass b p) =
      if a = b then 1 else 0 := by
  classical
  by_cases h : a = b
  · subst b
    simp [pointMass]
  · have hs : ¬ b = a := fun hba => h hba.symm
    simp [pointMass, h, hs]

private theorem pointMass_west_normalized
    (a p : ZMod L × ZMod L) :
    pointMass a (-1 + p.1, p.2) =
      pointMass (a.1 + 1, a.2) p := by
  convert pointMass_west a p using 1 <;> ring

private theorem pointMass_south_normalized
    (a p : ZMod L × ZMod L) :
    pointMass a (p.1, -1 + p.2) =
      pointMass (a.1, a.2 + 1) p := by
  convert pointMass_south a p using 1 <;> ring

private theorem zmod_two_ne_zero : (2 : ZMod L) ≠ 0 := by
  change ((2 : Nat) : ZMod L) ≠ 0
  rw [Ne, ZMod.natCast_eq_zero_iff]
  intro hdvd
  have hle := Nat.le_of_dvd (by norm_num : 0 < 2) hdvd
  have hL := (Fact.out : 8 < L)
  omega

private theorem zmod_three_ne_zero : (3 : ZMod L) ≠ 0 := by
  change ((3 : Nat) : ZMod L) ≠ 0
  rw [Ne, ZMod.natCast_eq_zero_iff]
  intro hdvd
  have hle := Nat.le_of_dvd (by norm_num : 0 < 3) hdvd
  have hL := (Fact.out : 8 < L)
  omega



theorem fkRectRefined_horizontal_west_interaction (x y : ZMod L) :
    fkRectRefinedRawInteraction
        [((x - 1, y - 1), 1), ((x - 1, y), 1)]
        [((x + 2, y), 2), ((x + 1, y), 2), ((x, y), 2),
          ((x - 1, y), 2)] = 1 := by
  classical
  unfold fkRectRefinedRawInteraction
  simp only [dartHorizontal, dartVertical, List.map_cons, List.map_nil,
    List.sum_cons, List.sum_nil, Fin.isValue, Fin.reduceEq,
    ↓reduceIte, add_zero, if_false, if_true, neg_zero, zero_mul, mul_zero]
  ring_nf
  have h2 := zmod_two_ne_zero (L := L)
  have h3 := zmod_three_ne_zero (L := L)
  have hm12 : (2 : ZMod L) ≠ -1 := by
    intro h
    apply h3
    calc
      (3 : ZMod L) = 2 - (-1) := by ring
      _ = 0 := by rw [h]; ring
  have hm11 : (1 : ZMod L) ≠ -1 := by
    intro h
    apply h2
    calc
      (2 : ZMod L) = 1 + 1 := by ring
      _ = (-1) + 1 := congrArg (fun z : ZMod L => z + 1) h
      _ = 0 := by ring
  repeat' rw [Finset.sum_add_distrib]
  simp_rw [pointMass_west_normalized]
  simp_rw [pointMass_mul_sum]
  have ha : ¬ (-1 + x = 1 + x + 1) := by
    intro h
    apply h3
    calc
      (3 : ZMod L) = (1 + x + 1) - (-1 + x) := by ring
      _ = 0 := by rw [h]; ring
  have hb : ¬ (-1 + x = x + 1) := by
    intro h
    apply h2
    calc
      (2 : ZMod L) = (x + 1) - (-1 + x) := by ring
      _ = 0 := by rw [h]; ring
  have hc : -1 + x = -2 + x + 1 := by ring
  have hn : (-2 : ZMod L) ≠ 1 := by
    intro h
    apply h3
    calc
      (3 : ZMod L) = 1 - (-2) := by ring
      _ = 0 := by rw [h]; ring
  simp [ha, hb, hc, hn, h2]



theorem fkRectRefined_horizontal_east_interaction (x y : ZMod L) :
    fkRectRefinedRawInteraction
        [((x + 1, y + 1), 3), ((x + 1, y), 3)]
        [((x + 2, y), 2), ((x + 1, y), 2), ((x, y), 2),
          ((x - 1, y), 2)] = -1 := by
  classical
  unfold fkRectRefinedRawInteraction
  simp only [dartHorizontal, dartVertical, List.map_cons, List.map_nil,
    List.sum_cons, List.sum_nil, Fin.isValue, Fin.reduceEq,
    ↓reduceIte, add_zero, if_false, if_true, neg_zero, zero_mul, mul_zero]
  ring_nf
  have h1 : (1 : ZMod L) ≠ 0 := one_ne_zero
  have h2 := zmod_two_ne_zero (L := L)
  have h3 := zmod_three_ne_zero (L := L)
  simp only [Finset.sum_sub_distrib, Finset.sum_neg_distrib]
  repeat' rw [Finset.sum_add_distrib]
  simp_rw [pointMass_west_normalized]
  simp_rw [pointMass_mul_sum]
  have ha : ¬ (x + 1 = 1 + x + 1) := by
    intro h
    apply h1
    calc
      (1 : ZMod L) = (1 + x + 1) - (x + 1) := by ring
      _ = 0 := by rw [h]; ring
  have hb : 1 + x = x + 1 := by ring
  have hc : ¬ (1 + x = -2 + x + 1) := by
    intro h
    apply h2
    calc
      (2 : ZMod L) = (1 + x) - (-2 + x + 1) := by ring
      _ = 0 := by rw [h]; ring
  simp [ha, hb, hc, h1, h2, h3]



theorem fkRectRefined_vertical_west_interaction (x y : ZMod L) :
    fkRectRefinedRawInteraction
        [((x - 1, y - 1), 0), ((x, y - 1), 0)]
        [((x, y - 2), 1), ((x, y - 1), 1), ((x, y), 1),
          ((x, y + 1), 1)] = 1 := by
  classical
  unfold fkRectRefinedRawInteraction
  simp only [dartHorizontal, dartVertical, List.map_cons, List.map_nil,
    List.sum_cons, List.sum_nil, Fin.isValue, Fin.reduceEq,
    ↓reduceIte, add_zero, if_false, if_true, neg_zero, zero_mul, mul_zero]
  ring_nf
  repeat' rw [Finset.sum_add_distrib]
  simp_rw [pointMass_south_normalized]
  simp_rw [pointMass_mul_sum]
  have h1 : (1 : ZMod L) ≠ 0 := one_ne_zero
  have h2 := zmod_two_ne_zero (L := L)
  have h3 := zmod_three_ne_zero (L := L)
  have hm11 : (-1 : ZMod L) ≠ 1 := by
    intro h
    apply h2
    calc
      (2 : ZMod L) = 1 - (-1) := by ring
      _ = 0 := by rw [h]; ring
  have hm12 : (-1 : ZMod L) ≠ 2 := by
    intro h
    apply h3
    calc
      (3 : ZMod L) = 2 - (-1) := by ring
      _ = 0 := by rw [h]; ring
  ring_nf
  simp [h1, h2, h3, hm11, hm12]



theorem fkRectRefined_vertical_east_interaction (x y : ZMod L) :
    fkRectRefinedRawInteraction
        [((x + 1, y + 1), 2), ((x, y + 1), 2)]
        [((x, y - 2), 1), ((x, y - 1), 1), ((x, y), 1),
          ((x, y + 1), 1)] = -1 := by
  classical
  unfold fkRectRefinedRawInteraction
  simp only [dartHorizontal, dartVertical, List.map_cons, List.map_nil,
    List.sum_cons, List.sum_nil, Fin.isValue, Fin.reduceEq,
    ↓reduceIte, add_zero, if_false, if_true, neg_zero, zero_mul, mul_zero]
  ring_nf
  simp only [Finset.sum_sub_distrib, Finset.sum_neg_distrib]
  repeat' rw [Finset.sum_add_distrib]
  simp_rw [pointMass_south_normalized]
  simp_rw [pointMass_mul_sum]
  have h1 : (1 : ZMod L) ≠ 0 := one_ne_zero
  have h2 := zmod_two_ne_zero (L := L)
  have h3 := zmod_three_ne_zero (L := L)
  have hm11 : (1 : ZMod L) ≠ -1 := by
    intro h
    apply h2
    calc
      (2 : ZMod L) = 1 - (-1) := by ring
      _ = 0 := by rw [← h]; ring
  have h12 : (1 : ZMod L) ≠ 2 := by
    intro h
    apply h1
    calc
      (1 : ZMod L) = 2 - 1 := by ring
      _ = 0 := by rw [← h]; ring
  ring_nf
  simp [h1, h2, h3, hm11, h12]



def fkRectRefinedPrimalCenterlineDarts (pairing : Bool) (c : Int × Int) :
    List FKRectIntegralSquareDart :=
  if pairing then
    [((c.1 + 2, c.2), 2), ((c.1 + 1, c.2), 2), ((c.1, c.2), 2),
      ((c.1 - 1, c.2), 2)]
  else
    [((c.1, c.2 - 2), 1), ((c.1, c.2 - 1), 1), ((c.1, c.2), 1),
      ((c.1, c.2 + 1), 1)]



theorem fkRectRefinedPrimalEdgeDarts_eq_centerline
    (R : FKRectTorus) (e : R.EdgeIndex) :
    fkRectRefinedPrimalEdgeDarts R e =
      fkRectRefinedPrimalCenterlineDarts
        (fkRectClosedPairingAtEdge e)
        (fkRectRefinedPrimalEdgeCenter R e) := by
  have h := fkRectCanonicalSquareEdgeStep_eq R e
  by_cases hp : fkRectClosedPairingAtEdge e
  · simp [hp] at h
    unfold fkRectRefinedPrimalEdgeDarts
      fkRectRefinedPrimalCenterlineDarts
    simp only [hp, if_true]
    unfold fkRectRefinedPrimalEdgeStart fkRectRefinedPrimalEdgeCenter
    have h1 := congrArg Prod.fst h
    have h2 := congrArg Prod.snd h
    simp only [Prod.fst_sub, Prod.snd_sub] at h1 h2
    simp
    all_goals omega
  · simp [hp] at h
    unfold fkRectRefinedPrimalEdgeDarts
      fkRectRefinedPrimalCenterlineDarts
    simp only [hp]
    unfold fkRectRefinedPrimalEdgeStart fkRectRefinedPrimalEdgeCenter
    have h1 := congrArg Prod.fst h
    have h2 := congrArg Prod.snd h
    simp only [Prod.fst_sub, Prod.snd_sub] at h1 h2
    simp
    all_goals omega



theorem fkRectRefinedLocalDarts_west_interaction
    (pairing : Bool) (c : Int × Int) :
    fkRectRefinedRawInteraction
        ((fkRectRefinedLocalDarts pairing c .west).map
          (fkRectIntegralSquareDartMod L))
        ((fkRectRefinedPrimalCenterlineDarts pairing c).map
          (fkRectIntegralSquareDartMod L)) = 1 := by
  cases pairing
  · convert fkRectRefined_vertical_west_interaction
      (L := L) (c.1 : ZMod L) (c.2 : ZMod L) using 1 <;>
      simp [fkRectRefinedPrimalCenterlineDarts,
        fkRectRefinedLocalDarts, fkRectRefinedDartPoint,
        fkRectRefinedSideOffset, fkRectIntegralSquareDartMod] <;> ring
  · convert fkRectRefined_horizontal_west_interaction
      (L := L) (c.1 : ZMod L) (c.2 : ZMod L) using 1 <;>
      simp [fkRectRefinedPrimalCenterlineDarts,
        fkRectRefinedLocalDarts, fkRectRefinedDartPoint,
        fkRectRefinedSideOffset, fkRectIntegralSquareDartMod] <;> ring


theorem fkRectRefinedLocalDarts_east_interaction
    (pairing : Bool) (c : Int × Int) :
    fkRectRefinedRawInteraction
        ((fkRectRefinedLocalDarts pairing c .east).map
          (fkRectIntegralSquareDartMod L))
        ((fkRectRefinedPrimalCenterlineDarts pairing c).map
          (fkRectIntegralSquareDartMod L)) = -1 := by
  cases pairing
  · simpa [fkRectRefinedPrimalCenterlineDarts,
      fkRectRefinedLocalDarts, fkRectRefinedDartPoint,
      fkRectRefinedSideOffset, fkRectIntegralSquareDartMod] using
      fkRectRefined_vertical_east_interaction
        (L := L) (c.1 : ZMod L) (c.2 : ZMod L)
  · simpa [fkRectRefinedPrimalCenterlineDarts,
      fkRectRefinedLocalDarts, fkRectRefinedDartPoint,
      fkRectRefinedSideOffset, fkRectIntegralSquareDartMod] using
      fkRectRefined_horizontal_east_interaction
        (L := L) (c.1 : ZMod L) (c.2 : ZMod L)



theorem fkRectRefinedPrimalEdge_west_interaction
    (R : FKRectTorus) (e : R.EdgeIndex) :
    fkRectRefinedRawInteraction
        ((fkRectRefinedLocalDarts (fkRectClosedPairingAtEdge e)
          (fkRectRefinedPrimalEdgeCenter R e) .west).map
            (fkRectIntegralSquareDartMod L))
        ((fkRectRefinedPrimalEdgeDarts R e).map
          (fkRectIntegralSquareDartMod L)) = 1 := by
  rw [fkRectRefinedPrimalEdgeDarts_eq_centerline]
  exact fkRectRefinedLocalDarts_west_interaction _ _



theorem fkRectRefinedPrimalEdge_east_interaction
    (R : FKRectTorus) (e : R.EdgeIndex) :
    fkRectRefinedRawInteraction
        ((fkRectRefinedLocalDarts (fkRectClosedPairingAtEdge e)
          (fkRectRefinedPrimalEdgeCenter R e) .east).map
            (fkRectIntegralSquareDartMod L))
        ((fkRectRefinedPrimalEdgeDarts R e).map
          (fkRectIntegralSquareDartMod L)) = -1 := by
  rw [fkRectRefinedPrimalEdgeDarts_eq_centerline]
  exact fkRectRefinedLocalDarts_east_interaction _ _



theorem fkRectRefinedLocalDarts_open_interaction
    (closedPairing : Bool) (c : Int × Int) (side : FKMedialSide) :
    fkRectRefinedRawInteraction
        ((fkRectRefinedLocalDarts (!closedPairing) c side).map
          (fkRectIntegralSquareDartMod L))
        ((fkRectRefinedPrimalCenterlineDarts closedPairing c).map
          (fkRectIntegralSquareDartMod L)) = 0 := by
  cases closedPairing <;> cases side <;>
    simp [fkRectRefinedRawInteraction, fkRectRefinedLocalDarts,
      fkRectRefinedDartPoint, fkRectRefinedSideOffset,
      fkRectRefinedPrimalCenterlineDarts, fkRectIntegralSquareDartMod,
      dartHorizontal, dartVertical]




def fkRectRefinedScalePoint (p : Int × Int) : Int × Int :=
  (4 * p.1, 4 * p.2)



def fkRectRefinedScaleDart (d : FKRectIntegralSquareDart) :
    List FKRectIntegralSquareDart :=
  let p := fkRectRefinedScalePoint d.1
  match d.2 with
  | 0 => [(p, 0), ((p.1 + 1, p.2), 0), ((p.1 + 2, p.2), 0),
      ((p.1 + 3, p.2), 0)]
  | 1 => [(p, 1), ((p.1, p.2 + 1), 1), ((p.1, p.2 + 2), 1),
      ((p.1, p.2 + 3), 1)]
  | 2 => [(p, 2), ((p.1 - 1, p.2), 2), ((p.1 - 2, p.2), 2),
      ((p.1 - 3, p.2), 2)]
  | 3 => [(p, 3), ((p.1, p.2 - 1), 3), ((p.1, p.2 - 2), 3),
      ((p.1, p.2 - 3), 3)]


theorem fkRectRefinedScaleDart_path (d : FKRectIntegralSquareDart) :
    FKRectIntegralSquareDartPath
      (fkRectRefinedScalePoint d.1)
      (fkRectRefinedScalePoint (fkRectIntegralSquareDartEnd d))
      (fkRectRefinedScaleDart d) := by
  rcases d with ⟨⟨x, y⟩, mu⟩
  fin_cases mu
  · convert fkRectRefinedFourEast_path
      (fkRectRefinedScalePoint (x, y)) using 1 <;>
      simp [fkRectRefinedScalePoint, fkRectIntegralSquareDartEnd,
        StatMech.Onsager.ons_dirExponentX,
        StatMech.Onsager.ons_dirExponentY] <;> ring
  · convert fkRectRefinedFourNorth_path_public
      (fkRectRefinedScalePoint (x, y)) using 1 <;>
      simp [fkRectRefinedScalePoint, fkRectIntegralSquareDartEnd,
        StatMech.Onsager.ons_dirExponentX,
        StatMech.Onsager.ons_dirExponentY] <;> ring
  · convert fkRectRefinedFourWest_path_public
      (fkRectRefinedScalePoint (x, y)) using 1 <;>
      simp [fkRectRefinedScalePoint, fkRectIntegralSquareDartEnd,
        StatMech.Onsager.ons_dirExponentX,
        StatMech.Onsager.ons_dirExponentY] <;> ring
  · convert fkRectRefinedFourSouth_path
      (fkRectRefinedScalePoint (x, y)) using 1 <;>
      simp [fkRectRefinedScalePoint, fkRectIntegralSquareDartEnd,
        StatMech.Onsager.ons_dirExponentX,
        StatMech.Onsager.ons_dirExponentY] <;> ring


def fkRectRefinedScaleDarts (l : List FKRectIntegralSquareDart) :
    List FKRectIntegralSquareDart :=
  l.flatMap fkRectRefinedScaleDart


theorem FKRectIntegralSquareDartPath.refinedScale
    {p q : Int × Int} {l : List FKRectIntegralSquareDart}
    (h : FKRectIntegralSquareDartPath p q l) :
    FKRectIntegralSquareDartPath
      (fkRectRefinedScalePoint p) (fkRectRefinedScalePoint q)
      (fkRectRefinedScaleDarts l) := by
  induction h with
  | nil p => exact FKRectIntegralSquareDartPath.nil _
  | @cons d q r l hend tail ih =>
      unfold fkRectRefinedScaleDarts
      rw [List.flatMap_cons]
      have hd := fkRectRefinedScaleDart_path d
      rw [hend] at hd
      exact hd.append ih



theorem FKRectSquareWalkLift.exists_refinedDartPath
    (R : FKRectTorus) {G : SimpleGraph R.Vertex}
    {x y : R.Vertex} {w : G.Walk x y} {p q : Int × Int}
    (h : FKRectSquareWalkLift R w p q) :
    ∃ l : List FKRectIntegralSquareDart,
      FKRectIntegralSquareDartPath
        (fkRectRefinedScalePoint (fkRectSquareDevelopPoint p))
        (fkRectRefinedScalePoint (fkRectSquareDevelopPoint q)) l := by
  obtain ⟨l, hl, -⟩ := h.exists_integralDartPath R
  exact ⟨fkRectRefinedScaleDarts l, hl.refinedScale⟩



theorem FKRectSquareWalkLift.exists_refinedSquareCoverCycleWitness
    (R : FKRectTorus) {G : SimpleGraph R.Vertex}
    {x : R.Vertex} {w : G.Walk x x} {p q : Int × Int}
    (h : FKRectSquareWalkLift R w p q) :
    Nonempty (FKRectSquareCoverCycleWitness R
      (4 * (fkRectSquareDevelopPoint q -
          fkRectSquareDevelopPoint p).1,
        4 * (fkRectSquareDevelopPoint q -
          fkRectSquareDevelopPoint p).2)) := by
  obtain ⟨l, hl⟩ := h.exists_refinedDartPath R
  let u : Int × Int :=
    (4 * (fkRectSquareDevelopPoint q - fkRectSquareDevelopPoint p).1,
      4 * (fkRectSquareDevelopPoint q - fkRectSquareDevelopPoint p).2)
  have hend : fkRectRefinedScalePoint (fkRectSquareDevelopPoint q) =
      ((fkRectRefinedScalePoint (fkRectSquareDevelopPoint p)).1 + u.1,
        (fkRectRefinedScalePoint (fkRectSquareDevelopPoint p)).2 + u.2) := by
    apply Prod.ext <;>
      simp [fkRectRefinedScalePoint, u] <;> ring
  rw [hend] at hl
  exact hl.exists_squareCoverCycleWitness R



theorem FKRectSquareWalkLift.exists_refinedLargeCoverCycleWitness
    (R : FKRectTorus) {G : SimpleGraph R.Vertex}
    {x : R.Vertex} {w : G.Walk x x} {p q : Int × Int}
    (h : FKRectSquareWalkLift R w p q) :
    Nonempty (FKRectSquareCoverCycleWitness (fkRectRefinedCoverTorus R)
      (4 * (fkRectSquareDevelopPoint q -
          fkRectSquareDevelopPoint p).1,
        4 * (fkRectSquareDevelopPoint q -
          fkRectSquareDevelopPoint p).2)) := by
  obtain ⟨l, hl⟩ := h.exists_refinedDartPath R
  let u : Int × Int :=
    (4 * (fkRectSquareDevelopPoint q - fkRectSquareDevelopPoint p).1,
      4 * (fkRectSquareDevelopPoint q - fkRectSquareDevelopPoint p).2)
  have hend : fkRectRefinedScalePoint (fkRectSquareDevelopPoint q) =
      ((fkRectRefinedScalePoint (fkRectSquareDevelopPoint p)).1 + u.1,
        (fkRectRefinedScalePoint (fkRectSquareDevelopPoint p)).2 + u.2) := by
    apply Prod.ext <;>
      simp [fkRectRefinedScalePoint, u] <;> ring
  rw [hend] at hl
  exact hl.exists_squareCoverCycleWitness (fkRectRefinedCoverTorus R)



theorem FKRectSquareWalkLift.windingIndependent_of_refinedIntersection_ne_zero
    (R : FKRectTorus)
    {G H : SimpleGraph R.Vertex} {x y : R.Vertex}
    {w : G.Walk x x} {z : H.Walk y y}
    {p q a b : Int × Int}
    (hw : FKRectSquareWalkLift R w p q)
    (hz : FKRectSquareWalkLift R z a b)
    (C : FKRectSquareCoverCycleWitness R
      (4 * (fkRectSquareDevelopPoint q -
          fkRectSquareDevelopPoint p).1,
        4 * (fkRectSquareDevelopPoint q -
          fkRectSquareDevelopPoint p).2))
    (D : FKRectSquareCoverCycleWitness R
      (4 * (fkRectSquareDevelopPoint b -
          fkRectSquareDevelopPoint a).1,
        4 * (fkRectSquareDevelopPoint b -
          fkRectSquareDevelopPoint a).2))
    (hne : C.cycle.intersection D.cycle ≠ 0) :
    FKRectWindingIndependent
      (fkRectWalkWinding R w) (fkRectWalkWinding R z) := by
  have hscaled := C.windingIndependent_of_intersection_ne_zero D hne
  have hdeveloped : FKRectWindingIndependent
      (fkRectSquareDevelopPoint q - fkRectSquareDevelopPoint p)
      (fkRectSquareDevelopPoint b - fkRectSquareDevelopPoint a) :=
    (fkRectWindingIndependent_four_iff _ _).mp hscaled
  exact (hw.closed_developedIndependent_iff R hz).mp hdeveloped




def fkRectRefinedBoundaryCanonicalCenter
    (R : FKRectTorus) (d : FKMedialDart R.medialTorus) : Int × Int :=
  fkRectRefinedPrimalEdgeCenter R
    (fkRectTorusMedialEdgeEquiv R d.1)



def fkRectMedialBoundaryPrimalSeamIncrement
    (R : FKRectTorus)
    (pairing : FKMedialLoopPairing R.medialTorus)
    (d : FKMedialDart R.medialTorus) : Int × Int :=
  let a := fkRectMedialDartPrimalLabel R d
  let b := fkRectMedialDartPrimalLabel R
    (fkMedialBoundaryStep pairing d)
  (fkRectHorizontalSeamIncrement R a b,
    fkRectVerticalSeamIncrement R a b)



def fkRectRefinedBoundaryPrimalLift
    (R : FKRectTorus) (d : FKMedialDart R.medialTorus) : Int × Int :=
  let e := fkRectTorusMedialEdgeEquiv R d.1
  let ends := fkRectLiftedIndexedEdgeEnds R e
  match fkRectClosedPairingAtEdge e, d.2 with
  | true, .east | true, .north | false, .west | false, .north => ends.1
  | true, .west | true, .south | false, .east | false, .south => ends.2



def fkRectRefinedBoundaryPrimalPotential
    (R : FKRectTorus) (d : FKMedialDart R.medialTorus) : Int × Int :=
  let z := fkRectSquareDevelopPoint (fkRectRefinedBoundaryPrimalLift R d)
  let a := fkRectVertexSquarePoint R (fkRectMedialDartPrimalLabel R d)
  (4 * (z.1 - a.1), 4 * (z.2 - a.2))

private theorem fkRectEven_add_self (k : Nat) : Even (k + k) :=
  ⟨k, rfl⟩

private theorem fkRectNotEven_add_self_add_one (k : Nat) :
    ¬ Even (k + k + 1) := by
  intro h
  obtain ⟨m, hm⟩ := h
  omega

private theorem fkRectEven_two_mul (k : Nat) : Even (2 * k) :=
  ⟨k, by omega⟩

private theorem fkRectNotEven_two_mul_add_one (k : Nat) :
    ¬ Even (2 * k + 1) := by
  intro h
  obtain ⟨m, hm⟩ := h
  omega

private theorem fkRectEven_two_mul_add_two (k : Nat) :
    Even (2 * k + 1 + 1) := ⟨k + 1, by omega⟩

private theorem fkRectNotEven_height_pred (R : FKRectTorus) :
    ¬ Even (R.height - 1) := by
  intro hpred
  obtain ⟨m, hm⟩ := hpred
  obtain ⟨n, hn⟩ := R.height_even
  have hpos := R.height_pos
  omega

private theorem fkRectWidth_ne_two (R : FKRectTorus) : R.width ≠ 2 :=
  ne_of_gt R.width_gt_two

private theorem fkRectHeight_ne_two (R : FKRectTorus) : R.height ≠ 2 :=
  ne_of_gt R.height_gt_two

private theorem fkRectInt_add_self_ediv_two (k : Nat) :
    ((k : Int) + k) / 2 = k := by omega

private theorem fkRectInt_add_self_add_one_ediv_two (k : Nat) :
    ((k : Int) + k + 1) / 2 = k := by omega

private theorem fkRectInt_add_self_add_two_ediv_two (k : Nat) :
    ((k : Int) + k + 1 + 1) / 2 = k + 1 := by omega

private theorem fkRectInt_two_mul_add_one_ediv_two (k : Nat) :
    (2 * (k : Int) + 1) / 2 = k := by omega

private theorem fkRectInt_two_mul_add_two_ediv_two (k : Nat) :
    (2 * (k : Int) + 1 + 1) / 2 = k + 1 := by omega

private theorem fkRectInt_one_add_mul_two_ediv_two (k : Nat) :
    (1 + (k : Int) * 2) / 2 = k := by omega

private theorem fkRectInt_two_add_mul_two_ediv_two (k : Nat) :
    (2 + (k : Int) * 2) / 2 = k + 1 := by omega

private theorem fkRectInt_three_add_mul_two_ediv_two (k : Nat) :
    (3 + (k : Int) * 2) / 2 = k + 1 := by omega

private theorem fkRectInt_neg_one_add_mul_two_ediv_two (k : Nat) :
    (-1 + (k : Int) * 2) / 2 = (k : Int) - 1 := by omega

private theorem fkRectInt_neg_two_add_mul_two_ediv_two (k : Nat) :
    (-2 + (k : Int) * 2) / 2 = (k : Int) - 1 := by omega

private theorem fkRectHeight_int_ediv_two (R : FKRectTorus) :
    (R.height : Int) / 2 = (R.height / 2 : Nat) := by
  have hhalf : (2 : Int) * (R.height / 2 : Nat) = R.height := by
    norm_cast
    exact Nat.two_mul_div_two_of_even R.height_even
  omega

private theorem fkRectHeight_pred_int_ediv_two (R : FKRectTorus) :
    ((R.height - 1 : Nat) : Int) / 2 = (R.height / 2 : Nat) - 1 := by
  have hhalf : (2 : Int) * (R.height / 2 : Nat) = R.height := by
    norm_cast
    exact Nat.two_mul_div_two_of_even R.height_even
  have hsub : R.height - 1 + 1 = R.height :=
    Nat.sub_add_cancel (Nat.one_le_iff_ne_zero.mpr
      (ne_of_gt R.height_pos))
  omega

private theorem fkRectHeight_pred_add_one_int_ediv_two
    (R : FKRectTorus) :
    (((R.height - 1 : Nat) : Int) + 1) / 2 =
      (R.height / 2 : Nat) := by
  have hhalf : (2 : Int) * (R.height / 2 : Nat) = R.height := by
    norm_cast
    exact Nat.two_mul_div_two_of_even R.height_even
  have hsub : R.height - 1 + 1 = R.height :=
    Nat.sub_add_cancel (Nat.one_le_iff_ne_zero.mpr
      (ne_of_gt R.height_pos))
  omega

private theorem fkRectWidth_pred_int_cast (R : FKRectTorus) :
    ((R.width - 1 : Nat) : Int) = (R.width : Int) - 1 := by
  rw [Nat.cast_sub (Nat.one_le_iff_ne_zero.mpr
    (ne_of_gt R.width_pos))]
  norm_num

private theorem fkRectHeight_pred_int_cast (R : FKRectTorus) :
    ((R.height - 1 : Nat) : Int) = (R.height : Int) - 1 := by
  rw [Nat.cast_sub (Nat.one_le_iff_ne_zero.mpr
    (ne_of_gt R.height_pos))]
  norm_num

private theorem fkRectHeight_int_sub_one_ediv_two (R : FKRectTorus) :
    ((R.height : Int) - 1) / 2 = (R.height / 2 : Nat) - 1 := by
  rw [← fkRectHeight_pred_int_cast]
  exact fkRectHeight_pred_int_ediv_two R

private theorem fkRectHeight_int_sub_one_add_one_ediv_two
    (R : FKRectTorus) :
    (((R.height : Int) - 1) + 1) / 2 =
      (R.height / 2 : Nat) := by
  rw [← fkRectHeight_pred_int_cast]
  exact fkRectHeight_pred_add_one_int_ediv_two R

private theorem fkRectNotEven_mul_two_sub_one (k : Nat) (hk : k ≠ 0) :
    ¬ Even (k * 2 - 1) := by
  obtain ⟨j, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hk
  intro h
  obtain ⟨m, hm⟩ := h
  omega

private theorem fkRectMulTwoSubOne_int_ediv_two
    (k : Nat) (hk : k ≠ 0) :
    (((k * 2 - 1 : Nat) : Int)) / 2 = (k : Int) - 1 := by
  obtain ⟨j, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hk
  omega

private theorem fkRectOneAddMulTwoSubOne_int_ediv_two
    (k : Nat) (hk : k ≠ 0) :
    (1 + ((k * 2 - 1 : Nat) : Int)) / 2 = k := by
  obtain ⟨j, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hk
  omega

private theorem fkRectFinPred_int_cast {n : Nat} (x : Fin n)
    (hx : x.val ≠ 0) :
    ((x.val - 1 : Nat) : Int) = (x.val : Int) - 1 := by
  omega

private theorem fkRectAddSelfSubOne_int_cast (k : Nat) (hk : k ≠ 0) :
    ((k + k - 1 : Nat) : Int) = (k : Int) + k - 1 := by
  omega

private theorem fkRectAddSelfSubOne_int_ediv_two
    (k : Nat) (hk : k ≠ 0) :
    ((k + k - 1 : Nat) : Int) / 2 = (k : Int) - 1 := by
  omega

private theorem fkRectAddSelfSubOne_add_one_int_ediv_two
    (k : Nat) (hk : k ≠ 0) :
    (((k + k - 1 : Nat) : Int) + 1) / 2 = k := by
  omega

private theorem fkRectHeight_int_negOne_add_ediv_two (R : FKRectTorus) :
    (-1 + (R.height : Int)) / 2 = (R.height / 2 : Nat) - 1 := by
  convert fkRectHeight_int_sub_one_ediv_two R using 1 <;> ring

private theorem fkRectHeight_int_negTwo_add_ediv_two (R : FKRectTorus) :
    (-2 + (R.height : Int)) / 2 = (R.height / 2 : Nat) - 1 := by
  have hhalf : (2 : Int) * (R.height / 2 : Nat) = R.height := by
    norm_cast
    exact Nat.two_mul_div_two_of_even R.height_even
  omega

private theorem fkRectHeight_one_add_negOne_add_ediv_two
    (R : FKRectTorus) :
    (1 + (-1 + (R.height : Int))) / 2 =
      (R.height / 2 : Nat) := by
  convert fkRectHeight_int_sub_one_add_one_ediv_two R using 1 <;> ring

set_option maxHeartbeats 20000000 in
set_option maxRecDepth 20000 in



theorem fkRectRefinedBoundaryBondCenter_eq_canonical_add_deck
    (R : FKRectTorus)
    (pairing : FKMedialLoopPairing R.medialTorus)
    (d : FKMedialDart R.medialTorus) :
    fkRectRefinedBondCenter (fkRectRefinedBoundaryCanonicalCenter R d)
        (fkMedialLocalMate pairing d).2 =
      ((fkRectRefinedBoundaryCanonicalCenter R
          (fkMedialBoundaryStep pairing d)).1 +
          4 * (fkRectSquareDeckTranslation R
            (fkRectMedialBoundaryPrimalSeamIncrement R pairing d)).1 +
          (fkRectRefinedBoundaryPrimalPotential R d).1 -
          (fkRectRefinedBoundaryPrimalPotential R
            (fkMedialBoundaryStep pairing d)).1,
        (fkRectRefinedBoundaryCanonicalCenter R
          (fkMedialBoundaryStep pairing d)).2 +
          4 * (fkRectSquareDeckTranslation R
            (fkRectMedialBoundaryPrimalSeamIncrement R pairing d)).2 +
          (fkRectRefinedBoundaryPrimalPotential R d).2 -
          (fkRectRefinedBoundaryPrimalPotential R
            (fkMedialBoundaryStep pairing d)).2) := by
  unfold fkRectRefinedBoundaryCanonicalCenter
    fkRectMedialBoundaryPrimalSeamIncrement
    fkRectRefinedBoundaryPrimalPotential
    fkRectRefinedBoundaryPrimalLift
  simp only [fkMedialBoundaryStep_apply]
  rw [fkRectTorusMedialEdgeEquiv_bondMate]
  rw [fkRectMedialDartPrimalLabel_bondMate]
  have hW1 : 1 ≠ R.width :=
    Nat.ne_of_lt (lt_trans Nat.one_lt_two R.width_gt_two)
  have hH1 : 1 ≠ R.height :=
    Nat.ne_of_lt (lt_trans Nat.one_lt_two R.height_gt_two)
  have hWgt := R.width_gt_two
  have hHgt := R.height_gt_two
  have hhalf : (2 : Int) * (R.height / 2 : Nat) = R.height := by
    norm_cast
    exact Nat.two_mul_div_two_of_even R.height_even
  have hWsub : R.width - 1 + 1 = R.width :=
    Nat.sub_add_cancel
      (Nat.one_le_iff_ne_zero.mpr (ne_of_gt R.width_pos))
  have hHsub : R.height - 1 + 1 = R.height :=
    Nat.sub_add_cancel
      (Nat.one_le_iff_ne_zero.mpr (ne_of_gt R.height_pos))
  rcases d with ⟨v, side⟩
  let e := fkRectTorusMedialEdgeEquiv R v
  have hv : v = fkRectMedialVertexOfEdge R e :=
    ((fkRectTorusMedialEdgeEquiv R).symm_apply_apply v).symm
  rw [hv]
  rcases e with ⟨b, x, y⟩
  cases hp : pairing (fkRectMedialVertexOfEdge R (b, x, y)) <;>
    cases b <;> cases side <;>
    by_cases hy : Even y.val <;>
    by_cases hx0 : x.val = 0 <;> by_cases hy0 : y.val = 0 <;>
    by_cases hxl : x.val + 1 = R.width <;>
    by_cases hyl : y.val + 1 = R.height
  all_goals try omega
  all_goals
    first
    | obtain ⟨k, hk⟩ := hy
    | obtain ⟨k, hk⟩ := Nat.not_even_iff_odd.mp hy
  all_goals
    simp_all only [fkRectMedialDartPrimalLabel, fkMedialLocalMate,
      fkMedialBondMate,
      fkRectMedialBondEdgeIndex,
      fkRectMedialWestPrimal, fkRectMedialEastPrimal,
      fkRectClosedPairingAtEdge, even_finitePeriodicSucc_iff,
      even_cyclicPred_iff, Nat.even_add_one,
      fkRectTorusMedialEdgeEquiv_vertexOfEdge]
  all_goals simp_all
  all_goals by_cases hk0 : k = 0
  all_goals try omega
  all_goals
    simp_all only [fkRectRefinedBondCenter, fkRectRefinedSideOffset,
      fkRectRefinedPrimalEdgeCenter, fkRectLiftedIndexedEdgeEnds,
      fkRectSquareDeckTranslation,
      fkRectHorizontalSeamIncrement, fkRectVerticalSeamIncrement,
      fkRectSquareDevelopPoint, fkRectVertexSquarePoint,
      finitePeriodicSucc_val,
      fkRectCyclicPred_val,
      fkRectTorusMedialEdgeEquiv_vertexOfEdge,
      fkRectWidth_ne_two, fkRectHeight_ne_two,
      hk0,
      Bool.false_eq_true, Bool.true_eq_false, if_false, if_true,
      true_and, and_true, false_and, and_false,
      Prod.fst, Prod.snd, Fin.val_mk]
  all_goals by_cases hk1 : k = 0
  all_goals try omega
  all_goals simp_all only [hk0, hk1]
  all_goals
    try simp only [hk0, hk1, fkRectEven_add_self,
      fkRectNotEven_add_self_add_one, fkRectEven_two_mul,
      fkRectNotEven_two_mul_add_one,
      fkRectEven_two_mul_add_two,
      fkRectNotEven_height_pred] at *
  all_goals
    first
    | (have hkpred := fkRectNotEven_mul_two_sub_one k hk1
       simp only [hkpred] at *)
    | skip
  all_goals
    try simp only [hk0, hk1, fkRectInt_add_self_ediv_two,
      fkRectInt_add_self_add_one_ediv_two,
      fkRectInt_add_self_add_two_ediv_two,
      fkRectInt_two_mul_add_one_ediv_two,
      fkRectInt_two_mul_add_two_ediv_two,
      fkRectHeight_int_ediv_two,
      fkRectHeight_pred_int_ediv_two,
      fkRectHeight_pred_add_one_int_ediv_two,
      fkRectWidth_pred_int_cast,
      fkRectHeight_pred_int_cast,
      fkRectHeight_int_sub_one_ediv_two,
      fkRectHeight_int_sub_one_add_one_ediv_two,
      fkRectHeight_int_negOne_add_ediv_two,
      fkRectHeight_one_add_negOne_add_ediv_two] at *
  all_goals
    first
    | (have hkdiv := fkRectMulTwoSubOne_int_ediv_two k hk1
       have hkdiv' := fkRectOneAddMulTwoSubOne_int_ediv_two k hk1
       simp only [hkdiv, hkdiv'] at *)
    | skip
  all_goals try (split_ifs at *)
  all_goals
    try simp only [fkRectNotEven_height_pred, fkRectNotEven_mul_two_sub_one,
      fkRectWidth_pred_int_cast,
      fkRectHeight_pred_int_cast, fkRectHeight_int_sub_one_ediv_two,
      fkRectHeight_int_sub_one_add_one_ediv_two,
      fkRectHeight_int_negOne_add_ediv_two,
      fkRectHeight_one_add_negOne_add_ediv_two,
      fkRectInt_add_self_ediv_two,
      fkRectInt_add_self_add_one_ediv_two,
      fkRectInt_add_self_add_two_ediv_two,
      fkRectMulTwoSubOne_int_ediv_two,
      fkRectOneAddMulTwoSubOne_int_ediv_two,
      fkRectFinPred_int_cast,
      fkRectAddSelfSubOne_int_cast,
      fkRectAddSelfSubOne_int_ediv_two,
      fkRectAddSelfSubOne_add_one_int_ediv_two]
  all_goals
    first
    | (have hxzero : x.val = 0 := by omega
       simp only [hxzero, Nat.zero_sub, Nat.cast_zero] at *)
    | (have hxpred := fkRectFinPred_int_cast x (by omega)
       rw [hxpred] at *)
    | skip
  all_goals
    first
    | (have hkzero : k = 0 := by omega
       simp only [hkzero, Nat.zero_mul, Nat.zero_add, Nat.sub_self,
         Nat.cast_zero] at *)
    | (have hkpredCast := fkRectAddSelfSubOne_int_cast k (by omega)
       have hkpredDiv := fkRectAddSelfSubOne_int_ediv_two k (by omega)
       have hkpredDiv' :=
         fkRectAddSelfSubOne_add_one_int_ediv_two k (by omega)
       simp only [hkpredCast, hkpredDiv, hkpredDiv'] at *)
    | skip
  all_goals norm_num at *
  all_goals ring_nf at *
  all_goals
    try simp only [fkRectWidth_pred_int_cast,
      fkRectHeight_pred_int_cast,
      fkRectHeight_int_negOne_add_ediv_two,
      fkRectHeight_one_add_negOne_add_ediv_two,
      fkRectInt_one_add_mul_two_ediv_two,
      fkRectInt_two_add_mul_two_ediv_two,
      fkRectInt_neg_one_add_mul_two_ediv_two] at *
  all_goals try (rw [fkRectWidth_pred_int_cast R] at *)
  all_goals try (rw [fkRectHeight_int_ediv_two R] at *)
  all_goals try (rw [fkRectHeight_int_negOne_add_ediv_two R] at *)
  all_goals try (rw [fkRectInt_one_add_mul_two_ediv_two] at *)
  all_goals try (rw [fkRectInt_two_add_mul_two_ediv_two] at *)
  all_goals try (rw [fkRectInt_neg_one_add_mul_two_ediv_two] at *)
  all_goals ring_nf at *
  all_goals try norm_num
  all_goals try (rw [fkRectHeight_int_sub_one_ediv_two R] at *)
  all_goals try (rw [fkRectHeight_int_negOne_add_ediv_two R] at *)
  all_goals try norm_num
  all_goals
    have hwidthGt := R.width_gt_two
    have hheightGt := R.height_gt_two
    have hwidthGtInt : (2 : Int) < R.width := by exact_mod_cast hwidthGt
    have hheightGtInt : (2 : Int) < R.height := by exact_mod_cast hheightGt
    try (rw [fkRectWidth_pred_int_cast R] at *)
    try (rw [fkRectHeight_int_ediv_two R] at *)
    try (rw [fkRectHeight_int_negTwo_add_ediv_two R] at *)
    try (rw [fkRectInt_three_add_mul_two_ediv_two] at *)
    try (rw [fkRectInt_neg_two_add_mul_two_ediv_two] at *)
  all_goals
    try simp_all only [fkRectNotEven_height_pred,
      fkRectNotEven_mul_two_sub_one]
  all_goals try constructor
  all_goals ring_nf at *
  all_goals
    first
    | exact (fkRectNotEven_mul_two_sub_one k (by omega)) (by assumption)
    | linarith
    | omega


def fkRectMedialBoundaryPrimalSeamTrace
    (R : FKRectTorus)
    (pairing : FKMedialLoopPairing R.medialTorus) :
    FKMedialDart R.medialTorus → Nat → Int × Int
  | _, 0 => (0, 0)
  | d, n + 1 =>
      let a := fkRectMedialBoundaryPrimalSeamIncrement R pairing d
      let z := fkRectMedialBoundaryPrimalSeamTrace R pairing
        (fkMedialBoundaryStep pairing d) n
      (a.1 + z.1, a.2 + z.2)





theorem fkRectRefinedBoundaryCenterAfter_eq_canonical_add_deck
    (R : FKRectTorus)
    (pairing : FKMedialLoopPairing R.medialTorus)
    (d : FKMedialDart R.medialTorus) (t : Int × Int) (n : Nat) :
    fkRectRefinedBoundaryCenterAfter pairing d
        ((fkRectRefinedBoundaryCanonicalCenter R d).1 + t.1,
          (fkRectRefinedBoundaryCanonicalCenter R d).2 + t.2) n =
      ((fkRectRefinedBoundaryCanonicalCenter R
          ((fkMedialBoundaryStep pairing)^[n] d)).1 + t.1 +
          4 * (fkRectSquareDeckTranslation R
            (fkRectMedialBoundaryPrimalSeamTrace R pairing d n)).1 +
          (fkRectRefinedBoundaryPrimalPotential R d).1 -
          (fkRectRefinedBoundaryPrimalPotential R
            ((fkMedialBoundaryStep pairing)^[n] d)).1,
        (fkRectRefinedBoundaryCanonicalCenter R
          ((fkMedialBoundaryStep pairing)^[n] d)).2 + t.2 +
          4 * (fkRectSquareDeckTranslation R
            (fkRectMedialBoundaryPrimalSeamTrace R pairing d n)).2 +
          (fkRectRefinedBoundaryPrimalPotential R d).2 -
          (fkRectRefinedBoundaryPrimalPotential R
            ((fkMedialBoundaryStep pairing)^[n] d)).2) := by
  induction n generalizing d t with
  | zero =>
      simp [fkRectRefinedBoundaryCenterAfter,
        fkRectMedialBoundaryPrimalSeamTrace,
        fkRectSquareDeckTranslation]
  | succ n ih =>
      let next := fkMedialBoundaryStep pairing d
      let a := fkRectMedialBoundaryPrimalSeamIncrement R pairing d
      let A := fkRectSquareDeckTranslation R a
      have hone :=
        fkRectRefinedBoundaryBondCenter_eq_canonical_add_deck R pairing d
      have hstart : fkRectRefinedBondCenter
          ((fkRectRefinedBoundaryCanonicalCenter R d).1 + t.1,
            (fkRectRefinedBoundaryCanonicalCenter R d).2 + t.2)
          (fkMedialLocalMate pairing d).2 =
        ((fkRectRefinedBoundaryCanonicalCenter R next).1 +
            (t.1 + 4 * A.1 +
              (fkRectRefinedBoundaryPrimalPotential R d).1 -
              (fkRectRefinedBoundaryPrimalPotential R next).1),
          (fkRectRefinedBoundaryCanonicalCenter R next).2 +
            (t.2 + 4 * A.2 +
              (fkRectRefinedBoundaryPrimalPotential R d).2 -
              (fkRectRefinedBoundaryPrimalPotential R next).2)) := by
        dsimp [next, A, a] at hone ⊢
        have hone1 := congrArg Prod.fst hone
        have hone2 := congrArg Prod.snd hone
        unfold fkRectRefinedBondCenter at hone1 hone2 ⊢
        apply Prod.ext
        · simp only [Prod.fst, Prod.snd] at hone1 ⊢
          omega
        · simp only [Prod.fst, Prod.snd] at hone2 ⊢
          omega
      rw [fkRectRefinedBoundaryCenterAfter, hstart]
      rw [ih next
        (t.1 + 4 * A.1 +
            (fkRectRefinedBoundaryPrimalPotential R d).1 -
            (fkRectRefinedBoundaryPrimalPotential R next).1,
          t.2 + 4 * A.2 +
            (fkRectRefinedBoundaryPrimalPotential R d).2 -
            (fkRectRefinedBoundaryPrimalPotential R next).2)]
      simp only [Function.iterate_succ_apply]
      change _ =
        ((fkRectRefinedBoundaryCanonicalCenter R
              ((fkMedialBoundaryStep pairing)^[n] next)).1 + t.1 +
            4 * (fkRectSquareDeckTranslation R
              (fkRectMedialBoundaryPrimalSeamTrace R pairing d
                (n + 1))).1 +
            (fkRectRefinedBoundaryPrimalPotential R d).1 -
            (fkRectRefinedBoundaryPrimalPotential R
              ((fkMedialBoundaryStep pairing)^[n] next)).1,
          (fkRectRefinedBoundaryCanonicalCenter R
              ((fkMedialBoundaryStep pairing)^[n] next)).2 + t.2 +
            4 * (fkRectSquareDeckTranslation R
              (fkRectMedialBoundaryPrimalSeamTrace R pairing d
                (n + 1))).2 +
            (fkRectRefinedBoundaryPrimalPotential R d).2 -
            (fkRectRefinedBoundaryPrimalPotential R
              ((fkMedialBoundaryStep pairing)^[n] next)).2)
      simp only [fkRectMedialBoundaryPrimalSeamTrace]
      dsimp [next, A, a]
      unfold fkRectSquareDeckTranslation
      apply Prod.ext <;> simp <;> ring



theorem fkRectMedialBoundaryPrimalStepWalk_winding
    (R : FKRectTorus) (omega : R.Configuration)
    (d : FKMedialDart R.medialTorus) :
    fkRectWalkWinding R
        (fkRectMedialBoundaryPrimalStepWalk R omega d) =
      fkRectMedialBoundaryPrimalSeamIncrement R
        (fkRectConfigurationToMedialPairing R omega) d := by
  by_cases heq : fkRectMedialDartPrimalLabel R d =
      fkRectMedialDartPrimalLabel R
        (fkMedialBoundaryStep
          (fkRectConfigurationToMedialPairing R omega) d)
  · have hseam : fkRectMedialBoundaryPrimalSeamIncrement R
        (fkRectConfigurationToMedialPairing R omega) d = (0, 0) := by
      unfold fkRectMedialBoundaryPrimalSeamIncrement
      rw [← heq]
      dsimp
      rw [fkRectHorizontalSeamIncrement_same_fst,
        fkRectVerticalSeamIncrement_same_snd]
    rw [hseam]
    unfold fkRectMedialBoundaryPrimalStepWalk
    split
    · rw [fkRectWalkWinding_copy]
      rfl
    · contradiction
  · have heq' : ¬ fkRectMedialDartPrimalLabel R d =
        fkRectMedialDartPrimalLabel R
          (fkMedialBondMate R.medialTorus
            (fkMedialLocalMate
              (fkRectConfigurationToMedialPairing R omega) d)) := by
      simpa only [fkMedialBoundaryStep_apply] using heq
    simp [fkRectMedialBoundaryPrimalStepWalk, heq',
      fkRectMedialBoundaryPrimalSeamIncrement, fkRectWalkWinding]



theorem fkRectMedialBoundaryPrimalTrace_winding
    (R : FKRectTorus) (omega : R.Configuration)
    (d : FKMedialDart R.medialTorus) (n : Nat) :
    fkRectWalkWinding R
        (fkRectMedialBoundaryPrimalTrace R omega d n) =
      fkRectMedialBoundaryPrimalSeamTrace R
        (fkRectConfigurationToMedialPairing R omega) d n := by
  induction n generalizing d with
  | zero =>
      simp [fkRectMedialBoundaryPrimalTrace, fkRectWalkWinding,
        fkRectMedialBoundaryPrimalSeamTrace]
  | succ n ih =>
      simp only [fkRectMedialBoundaryPrimalTrace]
      change fkRectWalkWinding R
        ((fkRectMedialBoundaryPrimalStepWalk R omega d).append
          (fkRectMedialBoundaryPrimalTrace R omega
            (fkMedialBoundaryStep
              (fkRectConfigurationToMedialPairing R omega) d) n)) = _
      rw [fkRectWalkWinding_append,
        fkRectMedialBoundaryPrimalStepWalk_winding, ih]
      simp [fkRectMedialBoundaryPrimalSeamTrace]


def fkRectRefinedBoundaryOrbitTranslation {T : EvenTorus}
    (pairing : FKMedialLoopPairing T) (d : FKMedialDart T)
    (c : Int × Int) : Int × Int :=
  ((fkRectRefinedBoundaryCenterAfter pairing d c
      (orderOf (fkMedialBoundaryStep pairing))).1 - c.1,
    (fkRectRefinedBoundaryCenterAfter pairing d c
      (orderOf (fkMedialBoundaryStep pairing))).2 - c.2)



theorem fkRectRefinedBoundaryOrbit_exists_squareCoverCycleWitness
    (R : FKRectTorus)
    (pairing : FKMedialLoopPairing R.medialTorus)
    (d : FKMedialDart R.medialTorus) (c : Int × Int) :
    Nonempty (FKRectSquareCoverCycleWitness R
      (fkRectRefinedBoundaryOrbitTranslation pairing d c)) := by
  let n := orderOf (fkMedialBoundaryStep pairing)
  let c' := fkRectRefinedBoundaryCenterAfter pairing d c n
  let u := fkRectRefinedBoundaryOrbitTranslation pairing d c
  have hpath := fkRectRefinedBoundaryOrbitDarts_path pairing d c
  change FKRectIntegralSquareDartPath
      (fkRectRefinedDartPoint c d.2)
      (fkRectRefinedDartPoint c' d.2)
      (fkRectRefinedBoundaryDarts pairing d c n) at hpath
  have hend : fkRectRefinedDartPoint c' d.2 =
      ((fkRectRefinedDartPoint c d.2).1 + u.1,
        (fkRectRefinedDartPoint c d.2).2 + u.2) := by
    unfold fkRectRefinedDartPoint u
      fkRectRefinedBoundaryOrbitTranslation c' n
    apply Prod.ext <;> simp <;> ring
  rw [hend] at hpath
  exact hpath.exists_squareCoverCycleWitness R



theorem fkRectRefinedBoundaryOrbit_exists_largeCoverCycleWitness
    (R : FKRectTorus)
    (pairing : FKMedialLoopPairing R.medialTorus)
    (d : FKMedialDart R.medialTorus) (c : Int × Int) :
    Nonempty (FKRectSquareCoverCycleWitness (fkRectRefinedCoverTorus R)
      (fkRectRefinedBoundaryOrbitTranslation pairing d c)) := by
  let n := orderOf (fkMedialBoundaryStep pairing)
  let c' := fkRectRefinedBoundaryCenterAfter pairing d c n
  let u := fkRectRefinedBoundaryOrbitTranslation pairing d c
  have hpath := fkRectRefinedBoundaryOrbitDarts_path pairing d c
  change FKRectIntegralSquareDartPath
      (fkRectRefinedDartPoint c d.2)
      (fkRectRefinedDartPoint c' d.2)
      (fkRectRefinedBoundaryDarts pairing d c n) at hpath
  have hend : fkRectRefinedDartPoint c' d.2 =
      ((fkRectRefinedDartPoint c d.2).1 + u.1,
        (fkRectRefinedDartPoint c d.2).2 + u.2) := by
    unfold fkRectRefinedDartPoint u
      fkRectRefinedBoundaryOrbitTranslation c' n
    apply Prod.ext <;> simp <;> ring
  rw [hend] at hpath
  exact hpath.exists_squareCoverCycleWitness (fkRectRefinedCoverTorus R)



theorem fkRectMedialBoundaryPrimalOrbitWalk_winding
    (R : FKRectTorus) (omega : R.Configuration)
    (d : FKMedialDart R.medialTorus) :
    fkRectWalkWinding R
        (fkRectMedialBoundaryPrimalOrbitWalk R omega d) =
      fkRectMedialBoundaryPrimalSeamTrace R
        (fkRectConfigurationToMedialPairing R omega) d
        (orderOf (fkMedialBoundaryStep
          (fkRectConfigurationToMedialPairing R omega))) := by
  unfold fkRectMedialBoundaryPrimalOrbitWalk
  rw [fkRectWalkWinding_copy]
  exact fkRectMedialBoundaryPrimalTrace_winding R omega d _




theorem fkRectRefinedBoundaryOrbitTranslation_eq_four_deck_winding
    (R : FKRectTorus) (omega : R.Configuration)
    (d : FKMedialDart R.medialTorus) :
    fkRectRefinedBoundaryOrbitTranslation
        (fkRectConfigurationToMedialPairing R omega) d
        (fkRectRefinedBoundaryCanonicalCenter R d) =
      (4 * (fkRectSquareDeckTranslation R
        (fkRectWalkWinding R
          (fkRectMedialBoundaryPrimalOrbitWalk R omega d))).1,
       4 * (fkRectSquareDeckTranslation R
        (fkRectWalkWinding R
          (fkRectMedialBoundaryPrimalOrbitWalk R omega d))).2) := by
  let pairing := fkRectConfigurationToMedialPairing R omega
  let n := orderOf (fkMedialBoundaryStep pairing)
  have hc := fkRectRefinedBoundaryCenterAfter_eq_canonical_add_deck
    R pairing d (0, 0) n
  simp only [add_zero] at hc
  have hpow : (fkMedialBoundaryStep pairing) ^ n = 1 :=
    pow_orderOf_eq_one _
  have hret : (fkMedialBoundaryStep pairing)^[n] d = d := by
    rw [← Equiv.Perm.coe_pow]
    simpa [hpow]
  rw [hret] at hc
  have hw : fkRectWalkWinding R
      (fkRectMedialBoundaryPrimalOrbitWalk R omega d) =
        fkRectMedialBoundaryPrimalSeamTrace R pairing d n := by
    dsimp [pairing, n]
    exact fkRectMedialBoundaryPrimalOrbitWalk_winding R omega d
  rw [hw]
  unfold fkRectRefinedBoundaryOrbitTranslation
  dsimp [pairing, n] at hc ⊢
  have hc1 := congrArg Prod.fst hc
  have hc2 := congrArg Prod.snd hc
  apply Prod.ext
  · simp only [Prod.fst, Prod.snd] at hc1 ⊢
    rw [hc1]
    ring
  · simp only [Prod.fst, Prod.snd] at hc2 ⊢
    rw [hc2]
    ring




theorem fkRectRefinedBoundaryOrbit_exists_canonicalWindingWitness
    (R : FKRectTorus) (omega : R.Configuration)
    (d : FKMedialDart R.medialTorus) :
    Nonempty (FKRectSquareCoverCycleWitness R
      (4 * (fkRectSquareDeckTranslation R
        (fkRectWalkWinding R
          (fkRectMedialBoundaryPrimalOrbitWalk R omega d))).1,
       4 * (fkRectSquareDeckTranslation R
        (fkRectWalkWinding R
          (fkRectMedialBoundaryPrimalOrbitWalk R omega d))).2)) := by
  rw [← fkRectRefinedBoundaryOrbitTranslation_eq_four_deck_winding]
  exact fkRectRefinedBoundaryOrbit_exists_squareCoverCycleWitness R
    (fkRectConfigurationToMedialPairing R omega) d
    (fkRectRefinedBoundaryCanonicalCenter R d)


theorem fkRectRefinedBoundaryOrbit_exists_largeCanonicalWindingWitness
    (R : FKRectTorus) (omega : R.Configuration)
    (d : FKMedialDart R.medialTorus) :
    Nonempty (FKRectSquareCoverCycleWitness (fkRectRefinedCoverTorus R)
      (4 * (fkRectSquareDeckTranslation R
        (fkRectWalkWinding R
          (fkRectMedialBoundaryPrimalOrbitWalk R omega d))).1,
       4 * (fkRectSquareDeckTranslation R
        (fkRectWalkWinding R
          (fkRectMedialBoundaryPrimalOrbitWalk R omega d))).2)) := by
  rw [← fkRectRefinedBoundaryOrbitTranslation_eq_four_deck_winding]
  exact fkRectRefinedBoundaryOrbit_exists_largeCoverCycleWitness R
    (fkRectConfigurationToMedialPairing R omega) d
    (fkRectRefinedBoundaryCanonicalCenter R d)




theorem fkRectMedialBoundaryPrimalOrbitWalk_windingIndependent_of_intersection
    (R : FKRectTorus) (omega : R.Configuration)
    (d : FKMedialDart R.medialTorus)
    {G : SimpleGraph R.Vertex} {x : R.Vertex}
    {w : G.Walk x x} {p q : Int × Int}
    (hw : FKRectSquareWalkLift R w p q)
    (C : FKRectSquareCoverCycleWitness R
      (fkRectRefinedBoundaryOrbitTranslation
        (fkRectConfigurationToMedialPairing R omega) d
        (fkRectRefinedBoundaryCanonicalCenter R d)))
    (D : FKRectSquareCoverCycleWitness R
      (4 * (fkRectSquareDevelopPoint q -
          fkRectSquareDevelopPoint p).1,
        4 * (fkRectSquareDevelopPoint q -
          fkRectSquareDevelopPoint p).2))
    (hne : C.cycle.intersection D.cycle ≠ 0) :
    FKRectWindingIndependent
      (fkRectWalkWinding R
        (fkRectMedialBoundaryPrimalOrbitWalk R omega d))
      (fkRectWalkWinding R w) := by
  have hscaled := C.windingIndependent_of_intersection_ne_zero D hne
  rw [fkRectRefinedBoundaryOrbitTranslation_eq_four_deck_winding,
    hw.closed_develop_sub_eq_deck_winding R] at hscaled
  exact (fkRectWindingIndependent_four_squareDeck_iff R _ _).mp hscaled


theorem fkRectMedialBoundaryPrimalOrbitWalk_windingIndependent_of_largeIntersection
    (R : FKRectTorus) (omega : R.Configuration)
    (d : FKMedialDart R.medialTorus)
    {G : SimpleGraph R.Vertex} {x : R.Vertex}
    {w : G.Walk x x} {p q : Int × Int}
    (hw : FKRectSquareWalkLift R w p q)
    (C : FKRectSquareCoverCycleWitness (fkRectRefinedCoverTorus R)
      (fkRectRefinedBoundaryOrbitTranslation
        (fkRectConfigurationToMedialPairing R omega) d
        (fkRectRefinedBoundaryCanonicalCenter R d)))
    (D : FKRectSquareCoverCycleWitness (fkRectRefinedCoverTorus R)
      (4 * (fkRectSquareDevelopPoint q -
          fkRectSquareDevelopPoint p).1,
        4 * (fkRectSquareDevelopPoint q -
          fkRectSquareDevelopPoint p).2))
    (hne : C.cycle.intersection D.cycle ≠ 0) :
    FKRectWindingIndependent
      (fkRectWalkWinding R
        (fkRectMedialBoundaryPrimalOrbitWalk R omega d))
      (fkRectWalkWinding R w) := by
  have hscaled := C.windingIndependent_of_intersection_ne_zero D hne
  rw [fkRectRefinedBoundaryOrbitTranslation_eq_four_deck_winding,
    hw.closed_develop_sub_eq_deck_winding R] at hscaled
  exact (fkRectWindingIndependent_four_squareDeck_iff R _ _).mp hscaled

end

end StatMech.FrontierD
