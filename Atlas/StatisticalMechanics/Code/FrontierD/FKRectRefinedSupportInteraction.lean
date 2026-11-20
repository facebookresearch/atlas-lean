/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/




import Code.FrontierD.FKRectRefinedInteractionCore
import Code.FrontierD.FKRectRefinedIntersection
import Code.FrontierD.FKRectTorusDisjointWinding









open Finset

namespace StatMech.FrontierD

open IntegralSquareTorusCycle

noncomputable section

variable {L : Nat} [Fact (8 < L)]

local instance : Fact (2 < L) :=
  ⟨lt_trans (by omega) (Fact.out : 8 < L)⟩



theorem fkRectRefinedRawInteraction_eq_zero_of_endpointDisjoint
    (v w : List (StatMech.Onsager.ons_Dart L))
    (hdisj : ∀ p, FKRectDartListUsesPoint v p →
      ¬ FKRectDartListUsesPoint w p) :
    fkRectRefinedRawInteraction v w = 0 := by
  classical
  unfold fkRectRefinedRawInteraction
  apply Finset.sum_eq_zero
  intro p hp
  by_cases hv :
      (v.map (fun d => dartHorizontal d p)).sum = 0 ∧
        (v.map (fun d => dartVertical d p)).sum = 0
  · rw [hv.1, hv.2]
    ring
  · have hwest :
        (w.map (fun d => dartHorizontal d (p.1 - 1, p.2))).sum = 0 := by
      by_contra hne
      have hvUses : FKRectDartListUsesPoint v p := by
        rcases not_and_or.mp hv with hh | hh
        · exact FKRectDartListUsesPoint.of_horizontal_ne_zero hh
        · exact FKRectDartListUsesPoint.of_vertical_ne_zero hh
      have hwUses := FKRectDartListUsesPoint.of_horizontal_ne_zero_east
        (l := w) hne
      apply hdisj p hvUses
      simpa using hwUses
    have hsouth :
        (w.map (fun d => dartVertical d (p.1, p.2 - 1))).sum = 0 := by
      by_contra hne
      have hvUses : FKRectDartListUsesPoint v p := by
        rcases not_and_or.mp hv with hh | hh
        · exact FKRectDartListUsesPoint.of_horizontal_ne_zero hh
        · exact FKRectDartListUsesPoint.of_vertical_ne_zero hh
      have hwUses := FKRectDartListUsesPoint.of_vertical_ne_zero_north
        (l := w) hne
      apply hdisj p hvUses
      simpa using hwUses
    rw [hwest, hsouth]
    ring

end

private theorem fkRectIntCast_four_mul_add_ne_four_mul
    {L : Nat} [NeZero L] (hL : (4 : Int) ∣ (L : Int))
    (x a k : Int) (hk : ¬ (4 : Int) ∣ k) :
    ((4 * x + k : Int) : ZMod L) ≠ ((4 * a : Int) : ZMod L) := by
  intro h
  have hd : (L : Int) ∣ (4 * a) - (4 * x + k) :=
    (ZMod.intCast_eq_intCast_iff_dvd_sub _ _ L).mp h
  obtain ⟨m, hm⟩ := hd
  obtain ⟨n, hn⟩ := hL
  apply hk
  refine ⟨a - x - n * m, ?_⟩
  rw [hn] at hm
  linarith

private theorem fkRectPointMass_west_normalized
    {L : Nat} [Fact (2 < L)]
    (a p : ZMod L × ZMod L) :
    pointMass a (-1 + p.1, p.2) =
      pointMass (a.1 + 1, a.2) p := by
  convert pointMass_west a p using 1 <;> ring

private theorem fkRectPointMass_south_normalized
    {L : Nat} [Fact (2 < L)]
    (a p : ZMod L × ZMod L) :
    pointMass a (p.1, -1 + p.2) =
      pointMass (a.1, a.2 + 1) p := by
  convert pointMass_south a p using 1 <;> ring

@[simp] theorem fkRectIntegralSquareDartMod_dir
    (L : Nat) (d : FKRectIntegralSquareDart) :
    (fkRectIntegralSquareDartMod L d).2 = d.2 :=
  rfl




def FKRectRefinedEdgeCenterNormal (horizontal : Bool)
    (c : Int × Int) : Prop :=
  if horizontal then
    ∃ x y : Int, c = (4 * x - 2, 4 * y)
  else
    ∃ x y : Int, c = (4 * x, 4 * y + 2)



theorem fkRectRefinedPrimalEdgeCenter_normal
    (R : FKRectTorus) (e : R.EdgeIndex) :
    FKRectRefinedEdgeCenterNormal (fkRectClosedPairingAtEdge e)
      (fkRectRefinedPrimalEdgeCenter R e) := by
  let p := fkRectSquareDevelopPoint (fkRectLiftedIndexedEdgeEnds R e).1
  let q := fkRectSquareDevelopPoint (fkRectLiftedIndexedEdgeEnds R e).2
  have hstep := fkRectCanonicalSquareEdgeStep_eq R e
  by_cases h : fkRectClosedPairingAtEdge e
  · simp only [h, if_true] at hstep
    simp only [FKRectRefinedEdgeCenterNormal, h, if_true]
    refine ⟨p.1, p.2, ?_⟩
    unfold fkRectRefinedPrimalEdgeCenter
    have hx := congrArg Prod.fst hstep
    have hy := congrArg Prod.snd hstep
    change q.1 - p.1 = -1 at hx
    change q.2 - p.2 = 0 at hy
    change (2 * (p.1 + q.1), 2 * (p.2 + q.2)) = _
    apply Prod.ext <;> simp only [Prod.fst, Prod.snd] <;> omega
  · simp only [h, if_false] at hstep
    simp only [FKRectRefinedEdgeCenterNormal, h, if_false]
    refine ⟨p.1, p.2, ?_⟩
    unfold fkRectRefinedPrimalEdgeCenter
    have hx := congrArg Prod.fst hstep
    have hy := congrArg Prod.snd hstep
    change q.1 - p.1 = 0 at hx
    change q.2 - p.2 = 1 at hy
    change (2 * (p.1 + q.1), 2 * (p.2 + q.2)) = _
    apply Prod.ext <;> simp only [Prod.fst, Prod.snd] <;> omega


theorem FKRectRefinedEdgeCenterNormal.add_four
    {horizontal : Bool} {c : Int × Int}
    (hc : FKRectRefinedEdgeCenterNormal horizontal c)
    (u v : Int) :
    FKRectRefinedEdgeCenterNormal horizontal
      (c.1 + 4 * u, c.2 + 4 * v) := by
  cases horizontal
  · obtain ⟨x, y, rfl⟩ := hc
    simp only [FKRectRefinedEdgeCenterNormal, if_false, Prod.fst, Prod.snd]
    exact ⟨x + u, y + v, by apply Prod.ext <;> simp <;> ring⟩
  · obtain ⟨x, y, rfl⟩ := hc
    simp only [FKRectRefinedEdgeCenterNormal, if_true, Prod.fst, Prod.snd]
    exact ⟨x + u, y + v, by apply Prod.ext <;> simp <;> ring⟩



theorem fkRectRefinedBoundaryCanonicalCenter_normal
    (R : FKRectTorus) (d : FKMedialDart R.medialTorus) :
    FKRectRefinedEdgeCenterNormal
      (fkRectClosedPairingAtEdge (fkRectTorusMedialEdgeEquiv R d.1))
      (fkRectRefinedBoundaryCanonicalCenter R d) := by
  exact fkRectRefinedPrimalEdgeCenter_normal R
    (fkRectTorusMedialEdgeEquiv R d.1)



theorem fkRectRefinedBoundaryCenterAfter_normal
    (R : FKRectTorus)
    (pairing : FKMedialLoopPairing R.medialTorus)
    (d : FKMedialDart R.medialTorus) (n : Nat) :
    FKRectRefinedEdgeCenterNormal
      (fkRectClosedPairingAtEdge (fkRectTorusMedialEdgeEquiv R
        (((fkMedialBoundaryStep pairing)^[n] d).1)))
      (fkRectRefinedBoundaryCenterAfter pairing d
        (fkRectRefinedBoundaryCanonicalCenter R d) n) := by
  let d' := (fkMedialBoundaryStep pairing)^[n] d
  let A := fkRectSquareDeckTranslation R
    (fkRectMedialBoundaryPrimalSeamTrace R pairing d n)
  let pd := fkRectSquareDevelopPoint (fkRectRefinedBoundaryPrimalLift R d)
  let ad := fkRectVertexSquarePoint R (fkRectMedialDartPrimalLabel R d)
  let pd' := fkRectSquareDevelopPoint (fkRectRefinedBoundaryPrimalLift R d')
  let ad' := fkRectVertexSquarePoint R (fkRectMedialDartPrimalLabel R d')
  have hcenter := fkRectRefinedBoundaryCenterAfter_eq_canonical_add_deck
    R pairing d (0, 0) n
  simp only [add_zero] at hcenter
  rw [hcenter]
  have hnormal := fkRectRefinedBoundaryCanonicalCenter_normal R d'
  have hadd := hnormal.add_four
    (A.1 + (pd.1 - ad.1) - (pd'.1 - ad'.1))
    (A.2 + (pd.2 - ad.2) - (pd'.2 - ad'.2))
  change FKRectRefinedEdgeCenterNormal
    (fkRectClosedPairingAtEdge (fkRectTorusMedialEdgeEquiv R d'.1))
    ((fkRectRefinedBoundaryCanonicalCenter R d').1 + 4 * A.1 +
        4 * (pd.1 - ad.1) - 4 * (pd'.1 - ad'.1),
      (fkRectRefinedBoundaryCanonicalCenter R d').2 + 4 * A.2 +
        4 * (pd.2 - ad.2) - 4 * (pd'.2 - ad'.2))
  convert hadd using 1 <;> ring_nf

set_option maxHeartbeats 2000000 in


theorem fkRectRefinedLocalDarts_open_interaction_of_normalCenters
    (R : FKRectTorus) (closed targetHorizontal : Bool)
    (c z : Int × Int) (side : FKMedialSide)
    (hc : FKRectRefinedEdgeCenterNormal closed c)
    (hz : FKRectRefinedEdgeCenterNormal targetHorizontal z) :
    fkRectRefinedRawInteraction
        ((fkRectRefinedLocalDarts (!closed) c side).map
          (fkRectIntegralSquareDartMod
            (fkRectSquareCoverSide (fkRectRefinedCoverTorus R))))
        ((fkRectRefinedPrimalCenterlineDarts targetHorizontal z).map
          (fkRectIntegralSquareDartMod
            (fkRectSquareCoverSide (fkRectRefinedCoverTorus R)))) = 0 := by
  let L := fkRectSquareCoverSide (fkRectRefinedCoverTorus R)
  have hL : (4 : Int) ∣ (L : Int) := by
    refine ⟨(fkRectSquareCoverSide R : Int), ?_⟩
    simp [L]
  have hne (u v k : Int) (hk : ¬ (4 : Int) ∣ k) :
      ((4 * u + k : Int) : ZMod L) ≠
        ((4 * v : Int) : ZMod L) :=
    fkRectIntCast_four_mul_add_ne_four_mul hL u v k hk
  cases closed <;> cases targetHorizontal
  all_goals simp only [FKRectRefinedEdgeCenterNormal,
    Bool.false_eq_true, Bool.not_false, Bool.not_true, if_false, if_true] at hc hz
  all_goals obtain ⟨x, y, rfl⟩ := hc
  all_goals obtain ⟨a, b, rfl⟩ := hz
  · cases side <;>
      simp [fkRectRefinedRawInteraction, fkRectRefinedLocalDarts,
        fkRectRefinedDartPoint, fkRectRefinedSideOffset,
        fkRectRefinedPrimalCenterlineDarts, fkRectIntegralSquareDartMod,
        dartHorizontal, dartVertical]
  · have hy1 := hne y b 1 (by norm_num)
    have hy2 := hne y b 2 (by norm_num)
    have hy3 := hne y b 3 (by norm_num)
    have hy1r := Ne.symm hy1
    have hy2r := Ne.symm hy2
    have hy3r := Ne.symm hy3
    have hyStep1 : (-1 : ZMod L) + (2 + (y : ZMod L) * 4) =
        1 + (y : ZMod L) * 4 := by ring
    have hyStep2 : (-1 : ZMod L) + (3 + (y : ZMod L) * 4) =
        2 + (y : ZMod L) * 4 := by ring
    cases side <;>
      simp only [fkRectRefinedRawInteraction, fkRectRefinedLocalDarts,
        fkRectRefinedDartPoint, fkRectRefinedSideOffset,
        fkRectRefinedPrimalCenterlineDarts, fkRectIntegralSquareDartMod,
        dartHorizontal, dartVertical, List.map_cons, List.map_nil,
        List.sum_cons, List.sum_nil, Fin.isValue, Fin.reduceEq,
        Bool.not_false, Bool.not_true,
        ite_true, ite_false, add_zero, zero_add, zero_mul, mul_zero,
        neg_zero, zero_sub]
    all_goals ring_nf
    all_goals simp_rw [fkRectPointMass_west_normalized]
    all_goals apply Finset.sum_eq_zero
    all_goals intro p hp
    all_goals by_cases hp2 : p.2 = ((4 * b : Int) : ZMod L)
    all_goals simp only [pointMass, Prod.ext_iff]
    all_goals ring_nf at *
    all_goals simp_all [
      show (-1 : ZMod L) + (2 + (y : ZMod L) * 4) =
        1 + (y : ZMod L) * 4 by ring,
      show (-1 : ZMod L) + (3 + (y : ZMod L) * 4) =
        2 + (y : ZMod L) * 4 by ring]
  · have hx3 := hne x a (-3) (by norm_num)
    have hx2 := hne x a (-2) (by norm_num)
    have hx1 := hne x a (-1) (by norm_num)
    have hx3r := Ne.symm hx3
    have hx2r := Ne.symm hx2
    have hx1r := Ne.symm hx1
    have hxStep2 : (-1 : ZMod L) + (-1 + (x : ZMod L) * 4) =
        -2 + (x : ZMod L) * 4 := by ring
    have hxStep3 : (-1 : ZMod L) + (-2 + (x : ZMod L) * 4) =
        -3 + (x : ZMod L) * 4 := by ring
    cases side <;>
      simp only [fkRectRefinedRawInteraction, fkRectRefinedLocalDarts,
        fkRectRefinedDartPoint, fkRectRefinedSideOffset,
        fkRectRefinedPrimalCenterlineDarts, fkRectIntegralSquareDartMod,
        dartHorizontal, dartVertical, List.map_cons, List.map_nil,
        List.sum_cons, List.sum_nil, Fin.isValue, Fin.reduceEq,
        Bool.not_false, Bool.not_true,
        ite_true, ite_false, add_zero, zero_add, zero_mul, mul_zero,
        neg_zero, zero_sub]
    all_goals ring_nf
    all_goals simp_rw [fkRectPointMass_south_normalized]
    all_goals apply Finset.sum_eq_zero
    all_goals intro p hp
    all_goals by_cases hp1 : p.1 = ((4 * a : Int) : ZMod L)
    all_goals simp only [pointMass, Prod.ext_iff]
    all_goals ring_nf at *
    all_goals simp_all [
      show (-1 : ZMod L) + (-1 + (x : ZMod L) * 4) =
        -2 + (x : ZMod L) * 4 by ring,
      show (-1 : ZMod L) + (-2 + (x : ZMod L) * 4) =
        -3 + (x : ZMod L) * 4 by ring]
  · cases side <;>
      simp [fkRectRefinedRawInteraction, fkRectRefinedLocalDarts,
        fkRectRefinedDartPoint, fkRectRefinedSideOffset,
        fkRectRefinedPrimalCenterlineDarts, fkRectIntegralSquareDartMod,
        dartHorizontal, dartVertical]

end StatMech.FrontierD
