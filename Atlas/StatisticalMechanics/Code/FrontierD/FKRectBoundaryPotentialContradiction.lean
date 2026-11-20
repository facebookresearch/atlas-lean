/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/




import Code.FrontierD.IntegralSquareTorusComplementPotential
import Code.FrontierD.FKRectRefinedConnectedInsertionCarrier











namespace StatMech.FrontierD

open IntegralSquareTorusCycle
open Finset SimpleGraph

noncomputable section


def fkRectRepeatDartList {alpha : Type*} : Nat → List alpha → List alpha
  | 0, _ => []
  | n + 1, l => l ++ fkRectRepeatDartList n l

theorem fkRectRepeatDartList_balanced {L : Nat} [Fact (8 < L)]
    (n : Nat) (l : List (StatMech.Onsager.ons_Dart L))
    (hl : DartListBalanced l) :
    DartListBalanced (fkRectRepeatDartList n l) := by
  induction n with
  | zero => simp [fkRectRepeatDartList, DartListBalanced]
  | succ n ih =>
      intro p
      simp only [fkRectRepeatDartList, List.map_append, List.sum_append]
      rw [hl p, ih p]

theorem fkRectRepeatDartList_map_sum {alpha : Type*}
    (n : Nat) (l : List alpha) (f : alpha → Int) :
    ((fkRectRepeatDartList n l).map f).sum =
      (n : Int) * (l.map f).sum := by
  induction n with
  | zero => simp [fkRectRepeatDartList]
  | succ n ih =>
      simp only [fkRectRepeatDartList, List.map_append, List.sum_append, ih,
        Nat.cast_add, Nat.cast_one]
      ring

theorem fkRectRefinedRawInteraction_repeatDartList_left
    {L : Nat} [Fact (8 < L)]
    (n : Nat) (a b : List (StatMech.Onsager.ons_Dart L)) :
    fkRectRefinedRawInteraction (fkRectRepeatDartList n a) b =
      (n : Int) * fkRectRefinedRawInteraction a b := by
  induction n with
  | zero => simp [fkRectRepeatDartList, fkRectRefinedRawInteraction]
  | succ n ih =>
      rw [fkRectRepeatDartList,
        fkRectRefinedRawInteraction_append_left, ih]
      push_cast
      ring



theorem int_natAbs_cross_mul_eq_of_mul_pos (a b : Int)
    (h : 0 < a * b) :
    (b.natAbs : Int) * a = (a.natAbs : Int) * b := by
  by_cases ha : 0 ≤ a
  · have hb : 0 ≤ b := by nlinarith
    rw [Int.natAbs_of_nonneg ha, Int.natAbs_of_nonneg hb]
    ring
  · have ha' : a ≤ 0 := le_of_not_ge ha
    have hb' : b ≤ 0 := by nlinarith
    rw [Int.ofNat_natAbs_of_nonpos ha', Int.ofNat_natAbs_of_nonpos hb']
    ring



theorem fkRectCanonicalRefinedBoundaryOrbitCoverDarts_xWrap_eq
    (R : FKRectTorus) (omega : R.Configuration)
    (d : FKMedialDart R.medialTorus) :
    ((fkRectCanonicalRefinedBoundaryOrbitCoverDarts R omega d).map
      StatMech.Onsager.ons_xWrapSign).sum =
      4 * (fkRectSquareDeckTranslation R
        (fkRectWalkWinding R
          (fkRectMedialBoundaryPrimalOrbitWalk R omega d))).1 := by
  unfold fkRectCanonicalRefinedBoundaryOrbitCoverDarts
  rw [fkRectSquareCoverDartList_xWrap_eq
    (fkRectRefinedCoverTorus R)
    (fkRectCanonicalRefinedBoundaryOrbitDarts_path_translation R omega d)]
  rw [fkRectRefinedBoundaryOrbitTranslation_eq_four_deck_winding]


theorem fkRectCanonicalRefinedBoundaryOrbitCoverDarts_yWrap_eq
    (R : FKRectTorus) (omega : R.Configuration)
    (d : FKMedialDart R.medialTorus) :
    ((fkRectCanonicalRefinedBoundaryOrbitCoverDarts R omega d).map
      StatMech.Onsager.ons_yWrapSign).sum =
      4 * (fkRectSquareDeckTranslation R
        (fkRectWalkWinding R
          (fkRectMedialBoundaryPrimalOrbitWalk R omega d))).2 := by
  unfold fkRectCanonicalRefinedBoundaryOrbitCoverDarts
  rw [fkRectSquareCoverDartList_yWrap_eq
    (fkRectRefinedCoverTorus R)
    (fkRectCanonicalRefinedBoundaryOrbitDarts_path_translation R omega d)]
  rw [fkRectRefinedBoundaryOrbitTranslation_eq_four_deck_winding]



theorem fkRectBalancedCarriers_localPotential_contradiction
    {L : Nat} [Fact (8 < L)]
    (A B : List (StatMech.Onsager.ons_Dart L))
    (hAbal : DartListBalanced A) (hBbal : DartListBalanced B)
    {p q : Int × Int} {l m : List FKRectIntegralSquareDart}
    (hl : FKRectIntegralSquareDartPath p q l)
    (hm : FKRectIntegralSquareDartPath p q m)
    (hx : (A.map StatMech.Onsager.ons_xWrapSign).sum =
      (B.map StatMech.Onsager.ons_xWrapSign).sum)
    (hy : (A.map StatMech.Onsager.ons_yWrapSign).sum =
      (B.map StatMech.Onsager.ons_yWrapSign).sum)
    (hAopen : fkRectRefinedRawInteraction A
      (l.map (fkRectIntegralSquareDartMod L)) = 0)
    (hBopen : fkRectRefinedRawInteraction B
      (l.map (fkRectIntegralSquareDartMod L)) = 0)
    (hAlocal : fkRectRefinedRawInteraction A
      (m.map (fkRectIntegralSquareDartMod L)) ≠ 0)
    (hBlocal : fkRectRefinedRawInteraction B
      (m.map (fkRectIntegralSquareDartMod L)) = 0) :
    False := by
  have hx' : (ofDartList A hAbal).xFlux (-1) =
      (ofDartList B hBbal).xFlux (-1) := by
    simpa only [ofDartList_xFlux] using hx
  have hy' : (ofDartList A hAbal).yFlux (-1) =
      (ofDartList B hBbal).yFlux (-1) := by
    simpa only [ofDartList_yFlux] using hy
  have heq := fkRectRefinedRawInteraction_sub_eq_of_equalFlux
    A B hAbal hBbal hx' hy' hl hm
  rw [hAopen, hBopen, hBlocal] at heq
  simp only [sub_self, sub_zero] at heq
  exact hAlocal heq.symm



theorem fkRectBalancedCarriers_equalFlux_signed_contradiction
    {L : Nat} [Fact (8 < L)]
    (A B : List (StatMech.Onsager.ons_Dart L))
    (hAbal : DartListBalanced A) (hBbal : DartListBalanced B)
    {p q : Int × Int} {l m : List FKRectIntegralSquareDart}
    (hl : FKRectIntegralSquareDartPath p q l)
    (hm : FKRectIntegralSquareDartPath p q m)
    (hx : (A.map StatMech.Onsager.ons_xWrapSign).sum =
      (B.map StatMech.Onsager.ons_xWrapSign).sum)
    (hy : (A.map StatMech.Onsager.ons_yWrapSign).sum =
      (B.map StatMech.Onsager.ons_yWrapSign).sum)
    (hAopen : fkRectRefinedRawInteraction A
      (l.map (fkRectIntegralSquareDartMod L)) = 0)
    (hBopen : fkRectRefinedRawInteraction B
      (l.map (fkRectIntegralSquareDartMod L)) = 0)
    (hAlocal : 0 < fkRectRefinedRawInteraction A
      (m.map (fkRectIntegralSquareDartMod L)))
    (hBlocal : fkRectRefinedRawInteraction B
      (m.map (fkRectIntegralSquareDartMod L)) ≤ 0) :
    False := by
  have hx' : (ofDartList A hAbal).xFlux (-1) =
      (ofDartList B hBbal).xFlux (-1) := by
    simpa only [ofDartList_xFlux] using hx
  have hy' : (ofDartList A hAbal).yFlux (-1) =
      (ofDartList B hBbal).yFlux (-1) := by
    simpa only [ofDartList_yFlux] using hy
  have heq := fkRectRefinedRawInteraction_sub_eq_of_equalFlux
    A B hAbal hBbal hx' hy' hl hm
  rw [hAopen, hBopen] at heq
  simp only [sub_self] at heq
  linarith




theorem fkRectBalancedCarriers_sameSignHorizontal_signed_contradiction
    {L : Nat} [Fact (8 < L)]
    (A B : List (StatMech.Onsager.ons_Dart L))
    (hAbal : DartListBalanced A) (hBbal : DartListBalanced B)
    {p q : Int × Int} {l m : List FKRectIntegralSquareDart}
    (hl : FKRectIntegralSquareDartPath p q l)
    (hm : FKRectIntegralSquareDartPath p q m)
    (hxsign : 0 < (A.map StatMech.Onsager.ons_xWrapSign).sum *
      (B.map StatMech.Onsager.ons_xWrapSign).sum)
    (hyA : (A.map StatMech.Onsager.ons_yWrapSign).sum = 0)
    (hyB : (B.map StatMech.Onsager.ons_yWrapSign).sum = 0)
    (hAopen : fkRectRefinedRawInteraction A
      (l.map (fkRectIntegralSquareDartMod L)) = 0)
    (hBopen : fkRectRefinedRawInteraction B
      (l.map (fkRectIntegralSquareDartMod L)) = 0)
    (hAlocal : 0 < fkRectRefinedRawInteraction A
      (m.map (fkRectIntegralSquareDartMod L)))
    (hBlocal : fkRectRefinedRawInteraction B
      (m.map (fkRectIntegralSquareDartMod L)) ≤ 0) :
    False := by
  let xA := (A.map StatMech.Onsager.ons_xWrapSign).sum
  let xB := (B.map StatMech.Onsager.ons_xWrapSign).sum
  let kA := xB.natAbs
  let kB := xA.natAbs
  let AA := fkRectRepeatDartList kA A
  let BB := fkRectRepeatDartList kB B
  have hxsign' : 0 < xA * xB := hxsign
  have hxAne : xA ≠ 0 := by
    intro h
    rw [h, zero_mul] at hxsign'
    exact (lt_irrefl 0) hxsign'
  have hxBne : xB ≠ 0 := by
    intro h
    rw [h, mul_zero] at hxsign'
    exact (lt_irrefl 0) hxsign'
  have hkApos : (0 : Int) < kA := by
    exact_mod_cast Int.natAbs_pos.mpr hxBne
  have hkBnonneg : (0 : Int) ≤ kB := by positivity
  have hAAbal : DartListBalanced AA :=
    fkRectRepeatDartList_balanced kA A hAbal
  have hBBbal : DartListBalanced BB :=
    fkRectRepeatDartList_balanced kB B hBbal
  have hxscaled :
      (AA.map StatMech.Onsager.ons_xWrapSign).sum =
        (BB.map StatMech.Onsager.ons_xWrapSign).sum := by
    rw [fkRectRepeatDartList_map_sum,
      fkRectRepeatDartList_map_sum]
    exact int_natAbs_cross_mul_eq_of_mul_pos xA xB hxsign'
  have hyscaled :
      (AA.map StatMech.Onsager.ons_yWrapSign).sum =
        (BB.map StatMech.Onsager.ons_yWrapSign).sum := by
    rw [fkRectRepeatDartList_map_sum,
      fkRectRepeatDartList_map_sum, hyA, hyB, mul_zero, mul_zero]
  have hAAopen : fkRectRefinedRawInteraction AA
      (l.map (fkRectIntegralSquareDartMod L)) = 0 := by
    rw [fkRectRefinedRawInteraction_repeatDartList_left, hAopen, mul_zero]
  have hBBopen : fkRectRefinedRawInteraction BB
      (l.map (fkRectIntegralSquareDartMod L)) = 0 := by
    rw [fkRectRefinedRawInteraction_repeatDartList_left, hBopen, mul_zero]
  have hAAlocal : 0 < fkRectRefinedRawInteraction AA
      (m.map (fkRectIntegralSquareDartMod L)) := by
    rw [fkRectRefinedRawInteraction_repeatDartList_left]
    exact mul_pos hkApos hAlocal
  have hBBlocal : fkRectRefinedRawInteraction BB
      (m.map (fkRectIntegralSquareDartMod L)) ≤ 0 := by
    rw [fkRectRefinedRawInteraction_repeatDartList_left]
    exact mul_nonpos_of_nonneg_of_nonpos hkBnonneg hBlocal
  have hx' : (ofDartList AA hAAbal).xFlux (-1) =
      (ofDartList BB hBBbal).xFlux (-1) := by
    simpa only [ofDartList_xFlux] using hxscaled
  have hy' : (ofDartList AA hAAbal).yFlux (-1) =
      (ofDartList BB hBBbal).yFlux (-1) := by
    simpa only [ofDartList_yFlux] using hyscaled
  have heq := fkRectRefinedRawInteraction_sub_eq_of_equalFlux
    AA BB hAAbal hBBbal hx' hy' hl hm
  rw [hAAopen, hBBopen] at heq
  simp only [sub_self] at heq
  linarith




theorem fkRectBalancedCarriers_sameSignDiagonal_signed_contradiction
    {L : Nat} [Fact (8 < L)]
    (A B : List (StatMech.Onsager.ons_Dart L))
    (hAbal : DartListBalanced A) (hBbal : DartListBalanced B)
    {p q : Int × Int} {l m : List FKRectIntegralSquareDart}
    (hl : FKRectIntegralSquareDartPath p q l)
    (hm : FKRectIntegralSquareDartPath p q m)
    (hxsign : 0 < (A.map StatMech.Onsager.ons_xWrapSign).sum *
      (B.map StatMech.Onsager.ons_xWrapSign).sum)
    (hdiagA : (A.map StatMech.Onsager.ons_yWrapSign).sum =
      (A.map StatMech.Onsager.ons_xWrapSign).sum)
    (hdiagB : (B.map StatMech.Onsager.ons_yWrapSign).sum =
      (B.map StatMech.Onsager.ons_xWrapSign).sum)
    (hAopen : fkRectRefinedRawInteraction A
      (l.map (fkRectIntegralSquareDartMod L)) = 0)
    (hBopen : fkRectRefinedRawInteraction B
      (l.map (fkRectIntegralSquareDartMod L)) = 0)
    (hAlocal : 0 < fkRectRefinedRawInteraction A
      (m.map (fkRectIntegralSquareDartMod L)))
    (hBlocal : fkRectRefinedRawInteraction B
      (m.map (fkRectIntegralSquareDartMod L)) ≤ 0) :
    False := by
  let xA := (A.map StatMech.Onsager.ons_xWrapSign).sum
  let xB := (B.map StatMech.Onsager.ons_xWrapSign).sum
  let kA := xB.natAbs
  let kB := xA.natAbs
  let AA := fkRectRepeatDartList kA A
  let BB := fkRectRepeatDartList kB B
  have hxsign' : 0 < xA * xB := hxsign
  have hxAne : xA ≠ 0 := by
    intro h
    rw [h, zero_mul] at hxsign'
    exact (lt_irrefl 0) hxsign'
  have hxBne : xB ≠ 0 := by
    intro h
    rw [h, mul_zero] at hxsign'
    exact (lt_irrefl 0) hxsign'
  have hkApos : (0 : Int) < kA := by
    exact_mod_cast Int.natAbs_pos.mpr hxBne
  have hkBnonneg : (0 : Int) ≤ kB := by positivity
  have hAAbal : DartListBalanced AA :=
    fkRectRepeatDartList_balanced kA A hAbal
  have hBBbal : DartListBalanced BB :=
    fkRectRepeatDartList_balanced kB B hBbal
  have hxscaled :
      (AA.map StatMech.Onsager.ons_xWrapSign).sum =
        (BB.map StatMech.Onsager.ons_xWrapSign).sum := by
    rw [fkRectRepeatDartList_map_sum,
      fkRectRepeatDartList_map_sum]
    exact int_natAbs_cross_mul_eq_of_mul_pos xA xB hxsign'
  have hyscaled :
      (AA.map StatMech.Onsager.ons_yWrapSign).sum =
        (BB.map StatMech.Onsager.ons_yWrapSign).sum := by
    rw [fkRectRepeatDartList_map_sum,
      fkRectRepeatDartList_map_sum, hdiagA, hdiagB]
    exact int_natAbs_cross_mul_eq_of_mul_pos xA xB hxsign'
  have hAAopen : fkRectRefinedRawInteraction AA
      (l.map (fkRectIntegralSquareDartMod L)) = 0 := by
    rw [fkRectRefinedRawInteraction_repeatDartList_left, hAopen, mul_zero]
  have hBBopen : fkRectRefinedRawInteraction BB
      (l.map (fkRectIntegralSquareDartMod L)) = 0 := by
    rw [fkRectRefinedRawInteraction_repeatDartList_left, hBopen, mul_zero]
  have hAAlocal : 0 < fkRectRefinedRawInteraction AA
      (m.map (fkRectIntegralSquareDartMod L)) := by
    rw [fkRectRefinedRawInteraction_repeatDartList_left]
    exact mul_pos hkApos hAlocal
  have hBBlocal : fkRectRefinedRawInteraction BB
      (m.map (fkRectIntegralSquareDartMod L)) ≤ 0 := by
    rw [fkRectRefinedRawInteraction_repeatDartList_left]
    exact mul_nonpos_of_nonneg_of_nonpos hkBnonneg hBlocal
  have hx' : (ofDartList AA hAAbal).xFlux (-1) =
      (ofDartList BB hBBbal).xFlux (-1) := by
    simpa only [ofDartList_xFlux] using hxscaled
  have hy' : (ofDartList AA hAAbal).yFlux (-1) =
      (ofDartList BB hBBbal).yFlux (-1) := by
    simpa only [ofDartList_yFlux] using hyscaled
  have heq := fkRectRefinedRawInteraction_sub_eq_of_equalFlux
    AA BB hAAbal hBBbal hx' hy' hl hm
  rw [hAAopen, hBBopen] at heq
  simp only [sub_self] at heq
  linarith




theorem fkRectBalancedCarriers_sameSignHorizontal_target_contradiction
    {L : Nat} [Fact (8 < L)]
    (A B C : List (StatMech.Onsager.ons_Dart L))
    (hAbal : DartListBalanced A) (hBbal : DartListBalanced B)
    (hCbal : DartListBalanced C)
    (hxsign : 0 < (A.map StatMech.Onsager.ons_xWrapSign).sum *
      (B.map StatMech.Onsager.ons_xWrapSign).sum)
    (hyA : (A.map StatMech.Onsager.ons_yWrapSign).sum = 0)
    (hyB : (B.map StatMech.Onsager.ons_yWrapSign).sum = 0)
    (hAC : 0 < fkRectRefinedRawInteraction A C)
    (hBC : fkRectRefinedRawInteraction B C ≤ 0) :
    False := by
  rw [fkRectRefinedRawInteraction_eq_wrap_det A C hAbal hCbal,
    hyA, zero_mul, sub_zero] at hAC
  rw [fkRectRefinedRawInteraction_eq_wrap_det B C hBbal hCbal,
    hyB, zero_mul, sub_zero] at hBC
  rcases (mul_pos_iff.mp hxsign) with hab | hab <;>
    rcases (mul_pos_iff.mp hAC) with hac | hac <;> nlinarith



theorem fkRectBalancedCarriers_sameSignDiagonal_target_contradiction
    {L : Nat} [Fact (8 < L)]
    (A B C : List (StatMech.Onsager.ons_Dart L))
    (hAbal : DartListBalanced A) (hBbal : DartListBalanced B)
    (hCbal : DartListBalanced C)
    (hxsign : 0 < (A.map StatMech.Onsager.ons_xWrapSign).sum *
      (B.map StatMech.Onsager.ons_xWrapSign).sum)
    (hdiagA : (A.map StatMech.Onsager.ons_yWrapSign).sum =
      (A.map StatMech.Onsager.ons_xWrapSign).sum)
    (hdiagB : (B.map StatMech.Onsager.ons_yWrapSign).sum =
      (B.map StatMech.Onsager.ons_xWrapSign).sum)
    (hAC : 0 < fkRectRefinedRawInteraction A C)
    (hBC : fkRectRefinedRawInteraction B C ≤ 0) :
    False := by
  rw [fkRectRefinedRawInteraction_eq_wrap_det A C hAbal hCbal,
    hdiagA] at hAC
  rw [fkRectRefinedRawInteraction_eq_wrap_det B C hBbal hCbal,
    hdiagB] at hBC
  rcases (mul_pos_iff.mp hxsign) with hab | hab <;>
    nlinarith


theorem fkRectBalancedCarriers_sameSignDiagonal_target_contradiction_neg
    {L : Nat} [Fact (8 < L)]
    (A B C : List (StatMech.Onsager.ons_Dart L))
    (hAbal : DartListBalanced A) (hBbal : DartListBalanced B)
    (hCbal : DartListBalanced C)
    (hxsign : 0 < (A.map StatMech.Onsager.ons_xWrapSign).sum *
      (B.map StatMech.Onsager.ons_xWrapSign).sum)
    (hdiagA : (A.map StatMech.Onsager.ons_yWrapSign).sum =
      (A.map StatMech.Onsager.ons_xWrapSign).sum)
    (hdiagB : (B.map StatMech.Onsager.ons_yWrapSign).sum =
      (B.map StatMech.Onsager.ons_xWrapSign).sum)
    (hAC : fkRectRefinedRawInteraction A C < 0)
    (hBC : 0 ≤ fkRectRefinedRawInteraction B C) :
    False := by
  rw [fkRectRefinedRawInteraction_eq_wrap_det A C hAbal hCbal,
    hdiagA] at hAC
  rw [fkRectRefinedRawInteraction_eq_wrap_det B C hBbal hCbal,
    hdiagB] at hBC
  rcases (mul_pos_iff.mp hxsign) with hab | hab <;>
    nlinarith




theorem fkRectCanonicalBoundaryCarriers_repeatedInsertionTarget_contradiction
    (R : FKRectTorus) (F : Finset R.EdgeIndex) (e : R.EdgeIndex)
    (heF : e ∉ F)
    (hsep : ¬ (fkMedialLoopGraph R.medialTorus
      (fkRectConfigurationToMedialPairing R
        (fkRectConfigurationOfEdges R F))).Reachable
          (fkMedialWestDart (fkRectMedialVertexOfEdge R e))
          (fkMedialEastDart (fkRectMedialVertexOfEdge R e)))
    (dB : FKMedialDart R.medialTorus)
    (hcolor : fkMedialCheckerColor dB =
      fkMedialCheckerColor
        (fkMedialWestDart (fkRectMedialVertexOfEdge R e)))
    (hBsep : ¬ (fkMedialLoopGraph R.medialTorus
      (fkRectConfigurationToMedialPairing R
        (fkRectConfigurationOfEdges R F))).Reachable
          (fkMedialWestDart (fkRectMedialVertexOfEdge R e)) dB)
    {l : List FKRectIntegralSquareDart}
    (hblocks : FKRectRefinedOpenEdgeBlocks R F l) (z : Int × Int)
    (hTbal : let L := fkRectSquareCoverSide (fkRectRefinedCoverTorus R)
      let V : Int × Int :=
        (4 * (fkRectSquareDeckTranslation R z).1,
          4 * (fkRectSquareDeckTranslation R z).2)
      DartListBalanced
        ((fkRectRepeatTranslatedDartPath
          (fkRectRefinedPrimalEdgeDarts R e ++ l) V L).map
            (fkRectIntegralSquareDartMod L)))
    (hxsign : let omega := fkRectConfigurationOfEdges R F
      let dA := fkMedialWestDart (fkRectMedialVertexOfEdge R e)
      let A := fkRectCanonicalRefinedBoundaryOrbitCoverDarts R omega dA
      let B := fkRectCanonicalRefinedBoundaryOrbitCoverDarts R omega dB
      0 < (A.map StatMech.Onsager.ons_xWrapSign).sum *
        (B.map StatMech.Onsager.ons_xWrapSign).sum)
    (hyA : let omega := fkRectConfigurationOfEdges R F
      let dA := fkMedialWestDart (fkRectMedialVertexOfEdge R e)
      let A := fkRectCanonicalRefinedBoundaryOrbitCoverDarts R omega dA
      (A.map StatMech.Onsager.ons_yWrapSign).sum = 0)
    (hyB : let omega := fkRectConfigurationOfEdges R F
      let B := fkRectCanonicalRefinedBoundaryOrbitCoverDarts R omega dB
      (B.map StatMech.Onsager.ons_yWrapSign).sum = 0) :
    False := by
  classical
  let omega := fkRectConfigurationOfEdges R F
  let pairing := fkRectConfigurationToMedialPairing R omega
  let dA := fkMedialWestDart (fkRectMedialVertexOfEdge R e)
  let A := fkRectCanonicalRefinedBoundaryOrbitCoverDarts R omega dA
  let B := fkRectCanonicalRefinedBoundaryOrbitCoverDarts R omega dB
  let wA := fkRectWalkWinding R
    (fkRectMedialBoundaryPrimalOrbitWalk R omega dA)
  let wB := fkRectWalkWinding R
    (fkRectMedialBoundaryPrimalOrbitWalk R omega dB)
  let n := orderOf (fkMedialBoundaryStep pairing)
  let L := fkRectSquareCoverSide (fkRectRefinedCoverTorus R)
  let V : Int × Int :=
    (4 * (fkRectSquareDeckTranslation R z).1,
      4 * (fkRectSquareDeckTranslation R z).2)
  let T := ((fkRectRepeatTranslatedDartPath
    (fkRectRefinedPrimalEdgeDarts R e ++ l) V L).map
      (fkRectIntegralSquareDartMod L))
  have hAbal : DartListBalanced A := by
    apply fkRectSquareCoverDartList_balanced
    exact fkRectCanonicalRefinedBoundaryOrbitDarts_path_translation
      R omega dA
  have hBbal : DartListBalanced B := by
    apply fkRectSquareCoverDartList_balanced
    exact fkRectCanonicalRefinedBoundaryOrbitDarts_path_translation
      R omega dB
  have hAedge : 0 < fkRectRefinedRawInteraction A
      ((fkRectRepeatTranslatedDartPath
        (fkRectRefinedPrimalEdgeDarts R e) V L).map
          (fkRectIntegralSquareDartMod L)) := by
    have h :=
      fkRectRefinedRawInteraction_repeated_west_boundary_edge_pos
        R F e heF wA z hsep
    change 0 < fkRectRefinedRawInteraction A
      ((fkRectRepeatTranslatedDartPath
        (fkRectRefinedPrimalEdgeDarts R e) V L).map
          (fkRectIntegralSquareDartMod L))
    simpa [A, fkRectCanonicalRefinedBoundaryOrbitCoverDarts,
      fkRectCanonicalRefinedBoundaryOrbitDarts,
      fkRectSquareCoverDartList, pairing, n, L, V, wA, omega,
      fkRectRefinedBoundaryOrbitTranslation_eq_four_deck_winding] using h
  have havoidB : ∀ k : Nat,
      (fkMedialBoundaryStep pairing)^[k] dB ≠ dA := by
    intro k hk
    apply hBsep
    have hr := fkMedialBoundaryStep_iterate_reachable pairing dB k
    rw [hk] at hr
    exact hr.symm
  have hBedge : fkRectRefinedRawInteraction B
      ((fkRectRepeatTranslatedDartPath
        (fkRectRefinedPrimalEdgeDarts R e) V L).map
          (fkRectIntegralSquareDartMod L)) ≤ 0 := by
    have h :=
      fkRectRefinedRawInteraction_repeated_boundary_edge_nonpos_of_avoid_west
        R F e heF dB wB z hcolor havoidB
    change fkRectRefinedRawInteraction B
      ((fkRectRepeatTranslatedDartPath
        (fkRectRefinedPrimalEdgeDarts R e) V L).map
          (fkRectIntegralSquareDartMod L)) ≤ 0
    simpa [B, fkRectCanonicalRefinedBoundaryOrbitCoverDarts,
      fkRectCanonicalRefinedBoundaryOrbitDarts,
      fkRectSquareCoverDartList, pairing, n, L, V, wB, omega,
      fkRectRefinedBoundaryOrbitTranslation_eq_four_deck_winding] using h
  have hAopen : fkRectRefinedRawInteraction A
      ((fkRectRepeatTranslatedDartPath l V L).map
        (fkRectIntegralSquareDartMod L)) = 0 := by
    have h := hblocks.repeated_boundary_interaction_eq_zero
      R F dA n wA z
    change fkRectRefinedRawInteraction A
      ((fkRectRepeatTranslatedDartPath l V L).map
        (fkRectIntegralSquareDartMod L)) = 0
    simpa [A, fkRectCanonicalRefinedBoundaryOrbitCoverDarts,
      fkRectCanonicalRefinedBoundaryOrbitDarts,
      fkRectSquareCoverDartList, pairing, n, L, V, wA, omega,
      fkRectRefinedBoundaryOrbitTranslation_eq_four_deck_winding] using h
  have hBopen : fkRectRefinedRawInteraction B
      ((fkRectRepeatTranslatedDartPath l V L).map
        (fkRectIntegralSquareDartMod L)) = 0 := by
    have h := hblocks.repeated_boundary_interaction_eq_zero
      R F dB n wB z
    change fkRectRefinedRawInteraction B
      ((fkRectRepeatTranslatedDartPath l V L).map
        (fkRectIntegralSquareDartMod L)) = 0
    simpa [B, fkRectCanonicalRefinedBoundaryOrbitCoverDarts,
      fkRectCanonicalRefinedBoundaryOrbitDarts,
      fkRectSquareCoverDartList, pairing, n, L, V, wB, omega,
      fkRectRefinedBoundaryOrbitTranslation_eq_four_deck_winding] using h
  have hAT : 0 < fkRectRefinedRawInteraction A T := by
    change 0 < fkRectRefinedRawInteraction A
      ((fkRectRepeatTranslatedDartPath
        (fkRectRefinedPrimalEdgeDarts R e ++ l) V L).map
          (fkRectIntegralSquareDartMod L))
    rw [fkRectRefinedRawInteraction_repeatTranslated_append_right,
      hAopen, add_zero]
    exact hAedge
  have hBT : fkRectRefinedRawInteraction B T ≤ 0 := by
    change fkRectRefinedRawInteraction B
      ((fkRectRepeatTranslatedDartPath
        (fkRectRefinedPrimalEdgeDarts R e ++ l) V L).map
          (fkRectIntegralSquareDartMod L)) ≤ 0
    rw [fkRectRefinedRawInteraction_repeatTranslated_append_right,
      hBopen, add_zero]
    exact hBedge
  exact fkRectBalancedCarriers_sameSignHorizontal_target_contradiction
    A B T hAbal hBbal hTbal hxsign hyA hyB hAT hBT



theorem
    fkRectCanonicalBoundaryCarriers_repeatedInsertionTarget_diagonal_contradiction
    (R : FKRectTorus) (F : Finset R.EdgeIndex) (e : R.EdgeIndex)
    (heF : e ∉ F)
    (hsep : ¬ (fkMedialLoopGraph R.medialTorus
      (fkRectConfigurationToMedialPairing R
        (fkRectConfigurationOfEdges R F))).Reachable
          (fkMedialWestDart (fkRectMedialVertexOfEdge R e))
          (fkMedialEastDart (fkRectMedialVertexOfEdge R e)))
    (dB : FKMedialDart R.medialTorus)
    (hcolor : fkMedialCheckerColor dB =
      fkMedialCheckerColor
        (fkMedialWestDart (fkRectMedialVertexOfEdge R e)))
    (hBsep : ¬ (fkMedialLoopGraph R.medialTorus
      (fkRectConfigurationToMedialPairing R
        (fkRectConfigurationOfEdges R F))).Reachable
          (fkMedialWestDart (fkRectMedialVertexOfEdge R e)) dB)
    {l : List FKRectIntegralSquareDart}
    (hblocks : FKRectRefinedOpenEdgeBlocks R F l) (z : Int × Int)
    (hTbal : let L := fkRectSquareCoverSide (fkRectRefinedCoverTorus R)
      let V : Int × Int :=
        (4 * (fkRectSquareDeckTranslation R z).1,
          4 * (fkRectSquareDeckTranslation R z).2)
      DartListBalanced
        ((fkRectRepeatTranslatedDartPath
          (fkRectRefinedPrimalEdgeDarts R e ++ l) V L).map
            (fkRectIntegralSquareDartMod L)))
    (hxsign : let omega := fkRectConfigurationOfEdges R F
      let dA := fkMedialWestDart (fkRectMedialVertexOfEdge R e)
      let A := fkRectCanonicalRefinedBoundaryOrbitCoverDarts R omega dA
      let B := fkRectCanonicalRefinedBoundaryOrbitCoverDarts R omega dB
      0 < (A.map StatMech.Onsager.ons_xWrapSign).sum *
        (B.map StatMech.Onsager.ons_xWrapSign).sum)
    (hdiagA : let omega := fkRectConfigurationOfEdges R F
      let dA := fkMedialWestDart (fkRectMedialVertexOfEdge R e)
      let A := fkRectCanonicalRefinedBoundaryOrbitCoverDarts R omega dA
      (A.map StatMech.Onsager.ons_yWrapSign).sum =
        (A.map StatMech.Onsager.ons_xWrapSign).sum)
    (hdiagB : let omega := fkRectConfigurationOfEdges R F
      let B := fkRectCanonicalRefinedBoundaryOrbitCoverDarts R omega dB
      (B.map StatMech.Onsager.ons_yWrapSign).sum =
        (B.map StatMech.Onsager.ons_xWrapSign).sum) :
    False := by
  classical
  let omega := fkRectConfigurationOfEdges R F
  let pairing := fkRectConfigurationToMedialPairing R omega
  let dA := fkMedialWestDart (fkRectMedialVertexOfEdge R e)
  let A := fkRectCanonicalRefinedBoundaryOrbitCoverDarts R omega dA
  let B := fkRectCanonicalRefinedBoundaryOrbitCoverDarts R omega dB
  let wA := fkRectWalkWinding R
    (fkRectMedialBoundaryPrimalOrbitWalk R omega dA)
  let wB := fkRectWalkWinding R
    (fkRectMedialBoundaryPrimalOrbitWalk R omega dB)
  let n := orderOf (fkMedialBoundaryStep pairing)
  let L := fkRectSquareCoverSide (fkRectRefinedCoverTorus R)
  let V : Int × Int :=
    (4 * (fkRectSquareDeckTranslation R z).1,
      4 * (fkRectSquareDeckTranslation R z).2)
  let T := ((fkRectRepeatTranslatedDartPath
    (fkRectRefinedPrimalEdgeDarts R e ++ l) V L).map
      (fkRectIntegralSquareDartMod L))
  have hAbal : DartListBalanced A := by
    apply fkRectSquareCoverDartList_balanced
    exact fkRectCanonicalRefinedBoundaryOrbitDarts_path_translation
      R omega dA
  have hBbal : DartListBalanced B := by
    apply fkRectSquareCoverDartList_balanced
    exact fkRectCanonicalRefinedBoundaryOrbitDarts_path_translation
      R omega dB
  have hAedge : 0 < fkRectRefinedRawInteraction A
      ((fkRectRepeatTranslatedDartPath
        (fkRectRefinedPrimalEdgeDarts R e) V L).map
          (fkRectIntegralSquareDartMod L)) := by
    have h :=
      fkRectRefinedRawInteraction_repeated_west_boundary_edge_pos
        R F e heF wA z hsep
    change 0 < fkRectRefinedRawInteraction A
      ((fkRectRepeatTranslatedDartPath
        (fkRectRefinedPrimalEdgeDarts R e) V L).map
          (fkRectIntegralSquareDartMod L))
    simpa [A, fkRectCanonicalRefinedBoundaryOrbitCoverDarts,
      fkRectCanonicalRefinedBoundaryOrbitDarts,
      fkRectSquareCoverDartList, pairing, n, L, V, wA, omega,
      fkRectRefinedBoundaryOrbitTranslation_eq_four_deck_winding] using h
  have havoidB : ∀ k : Nat,
      (fkMedialBoundaryStep pairing)^[k] dB ≠ dA := by
    intro k hk
    apply hBsep
    have hr := fkMedialBoundaryStep_iterate_reachable pairing dB k
    rw [hk] at hr
    exact hr.symm
  have hBedge : fkRectRefinedRawInteraction B
      ((fkRectRepeatTranslatedDartPath
        (fkRectRefinedPrimalEdgeDarts R e) V L).map
          (fkRectIntegralSquareDartMod L)) ≤ 0 := by
    have h :=
      fkRectRefinedRawInteraction_repeated_boundary_edge_nonpos_of_avoid_west
        R F e heF dB wB z hcolor havoidB
    change fkRectRefinedRawInteraction B
      ((fkRectRepeatTranslatedDartPath
        (fkRectRefinedPrimalEdgeDarts R e) V L).map
          (fkRectIntegralSquareDartMod L)) ≤ 0
    simpa [B, fkRectCanonicalRefinedBoundaryOrbitCoverDarts,
      fkRectCanonicalRefinedBoundaryOrbitDarts,
      fkRectSquareCoverDartList, pairing, n, L, V, wB, omega,
      fkRectRefinedBoundaryOrbitTranslation_eq_four_deck_winding] using h
  have hAopen : fkRectRefinedRawInteraction A
      ((fkRectRepeatTranslatedDartPath l V L).map
        (fkRectIntegralSquareDartMod L)) = 0 := by
    have h := hblocks.repeated_boundary_interaction_eq_zero
      R F dA n wA z
    change fkRectRefinedRawInteraction A
      ((fkRectRepeatTranslatedDartPath l V L).map
        (fkRectIntegralSquareDartMod L)) = 0
    simpa [A, fkRectCanonicalRefinedBoundaryOrbitCoverDarts,
      fkRectCanonicalRefinedBoundaryOrbitDarts,
      fkRectSquareCoverDartList, pairing, n, L, V, wA, omega,
      fkRectRefinedBoundaryOrbitTranslation_eq_four_deck_winding] using h
  have hBopen : fkRectRefinedRawInteraction B
      ((fkRectRepeatTranslatedDartPath l V L).map
        (fkRectIntegralSquareDartMod L)) = 0 := by
    have h := hblocks.repeated_boundary_interaction_eq_zero
      R F dB n wB z
    change fkRectRefinedRawInteraction B
      ((fkRectRepeatTranslatedDartPath l V L).map
        (fkRectIntegralSquareDartMod L)) = 0
    simpa [B, fkRectCanonicalRefinedBoundaryOrbitCoverDarts,
      fkRectCanonicalRefinedBoundaryOrbitDarts,
      fkRectSquareCoverDartList, pairing, n, L, V, wB, omega,
      fkRectRefinedBoundaryOrbitTranslation_eq_four_deck_winding] using h
  have hAT : 0 < fkRectRefinedRawInteraction A T := by
    change 0 < fkRectRefinedRawInteraction A
      ((fkRectRepeatTranslatedDartPath
        (fkRectRefinedPrimalEdgeDarts R e ++ l) V L).map
          (fkRectIntegralSquareDartMod L))
    rw [fkRectRefinedRawInteraction_repeatTranslated_append_right,
      hAopen, add_zero]
    exact hAedge
  have hBT : fkRectRefinedRawInteraction B T ≤ 0 := by
    change fkRectRefinedRawInteraction B
      ((fkRectRepeatTranslatedDartPath
        (fkRectRefinedPrimalEdgeDarts R e ++ l) V L).map
          (fkRectIntegralSquareDartMod L)) ≤ 0
    rw [fkRectRefinedRawInteraction_repeatTranslated_append_right,
      hBopen, add_zero]
    exact hBedge
  exact fkRectBalancedCarriers_sameSignDiagonal_target_contradiction
    A B T hAbal hBbal hTbal hxsign hdiagA hdiagB hAT hBT



theorem
    fkRectCanonicalBoundaryCarriers_repeatedInsertionTarget_diagonal_contradiction_east
    (R : FKRectTorus) (F : Finset R.EdgeIndex) (e : R.EdgeIndex)
    (heF : e ∉ F)
    (hsep : ¬ (fkMedialLoopGraph R.medialTorus
      (fkRectConfigurationToMedialPairing R
        (fkRectConfigurationOfEdges R F))).Reachable
          (fkMedialWestDart (fkRectMedialVertexOfEdge R e))
          (fkMedialEastDart (fkRectMedialVertexOfEdge R e)))
    (dB : FKMedialDart R.medialTorus)
    (hcolor : fkMedialCheckerColor dB =
      fkMedialCheckerColor
        (fkMedialEastDart (fkRectMedialVertexOfEdge R e)))
    (hBsep : ¬ (fkMedialLoopGraph R.medialTorus
      (fkRectConfigurationToMedialPairing R
        (fkRectConfigurationOfEdges R F))).Reachable
          (fkMedialEastDart (fkRectMedialVertexOfEdge R e)) dB)
    {l : List FKRectIntegralSquareDart}
    (hblocks : FKRectRefinedOpenEdgeBlocks R F l) (z : Int × Int)
    (hTbal : let L := fkRectSquareCoverSide (fkRectRefinedCoverTorus R)
      let V : Int × Int :=
        (4 * (fkRectSquareDeckTranslation R z).1,
          4 * (fkRectSquareDeckTranslation R z).2)
      DartListBalanced
        ((fkRectRepeatTranslatedDartPath
          (fkRectRefinedPrimalEdgeDarts R e ++ l) V L).map
            (fkRectIntegralSquareDartMod L)))
    (hxsign : let omega := fkRectConfigurationOfEdges R F
      let dA := fkMedialEastDart (fkRectMedialVertexOfEdge R e)
      let A := fkRectCanonicalRefinedBoundaryOrbitCoverDarts R omega dA
      let B := fkRectCanonicalRefinedBoundaryOrbitCoverDarts R omega dB
      0 < (A.map StatMech.Onsager.ons_xWrapSign).sum *
        (B.map StatMech.Onsager.ons_xWrapSign).sum)
    (hdiagA : let omega := fkRectConfigurationOfEdges R F
      let dA := fkMedialEastDart (fkRectMedialVertexOfEdge R e)
      let A := fkRectCanonicalRefinedBoundaryOrbitCoverDarts R omega dA
      (A.map StatMech.Onsager.ons_yWrapSign).sum =
        (A.map StatMech.Onsager.ons_xWrapSign).sum)
    (hdiagB : let omega := fkRectConfigurationOfEdges R F
      let B := fkRectCanonicalRefinedBoundaryOrbitCoverDarts R omega dB
      (B.map StatMech.Onsager.ons_yWrapSign).sum =
        (B.map StatMech.Onsager.ons_xWrapSign).sum) :
    False := by
  classical
  let omega := fkRectConfigurationOfEdges R F
  let pairing := fkRectConfigurationToMedialPairing R omega
  let dA := fkMedialEastDart (fkRectMedialVertexOfEdge R e)
  let A := fkRectCanonicalRefinedBoundaryOrbitCoverDarts R omega dA
  let B := fkRectCanonicalRefinedBoundaryOrbitCoverDarts R omega dB
  let wA := fkRectWalkWinding R
    (fkRectMedialBoundaryPrimalOrbitWalk R omega dA)
  let wB := fkRectWalkWinding R
    (fkRectMedialBoundaryPrimalOrbitWalk R omega dB)
  let n := orderOf (fkMedialBoundaryStep pairing)
  let L := fkRectSquareCoverSide (fkRectRefinedCoverTorus R)
  let V : Int × Int :=
    (4 * (fkRectSquareDeckTranslation R z).1,
      4 * (fkRectSquareDeckTranslation R z).2)
  let T := ((fkRectRepeatTranslatedDartPath
    (fkRectRefinedPrimalEdgeDarts R e ++ l) V L).map
      (fkRectIntegralSquareDartMod L))
  have hAbal : DartListBalanced A := by
    apply fkRectSquareCoverDartList_balanced
    exact fkRectCanonicalRefinedBoundaryOrbitDarts_path_translation
      R omega dA
  have hBbal : DartListBalanced B := by
    apply fkRectSquareCoverDartList_balanced
    exact fkRectCanonicalRefinedBoundaryOrbitDarts_path_translation
      R omega dB
  have hAedge : fkRectRefinedRawInteraction A
      ((fkRectRepeatTranslatedDartPath
        (fkRectRefinedPrimalEdgeDarts R e) V L).map
          (fkRectIntegralSquareDartMod L)) < 0 := by
    have h :=
      fkRectRefinedRawInteraction_repeated_east_boundary_edge_neg
        R F e heF wA z hsep
    change fkRectRefinedRawInteraction A
      ((fkRectRepeatTranslatedDartPath
        (fkRectRefinedPrimalEdgeDarts R e) V L).map
          (fkRectIntegralSquareDartMod L)) < 0
    simpa [A, fkRectCanonicalRefinedBoundaryOrbitCoverDarts,
      fkRectCanonicalRefinedBoundaryOrbitDarts,
      fkRectSquareCoverDartList, pairing, n, L, V, wA, omega,
      fkRectRefinedBoundaryOrbitTranslation_eq_four_deck_winding] using h
  have havoidB : ∀ k : Nat,
      (fkMedialBoundaryStep pairing)^[k] dB ≠ dA := by
    intro k hk
    apply hBsep
    have hr := fkMedialBoundaryStep_iterate_reachable pairing dB k
    rw [hk] at hr
    exact hr.symm
  have hBedge : 0 ≤ fkRectRefinedRawInteraction B
      ((fkRectRepeatTranslatedDartPath
        (fkRectRefinedPrimalEdgeDarts R e) V L).map
          (fkRectIntegralSquareDartMod L)) := by
    have h :=
      fkRectRefinedRawInteraction_repeated_boundary_edge_nonneg_of_avoid_east
        R F e heF dB wB z hcolor havoidB
    change 0 ≤ fkRectRefinedRawInteraction B
      ((fkRectRepeatTranslatedDartPath
        (fkRectRefinedPrimalEdgeDarts R e) V L).map
          (fkRectIntegralSquareDartMod L))
    simpa [B, fkRectCanonicalRefinedBoundaryOrbitCoverDarts,
      fkRectCanonicalRefinedBoundaryOrbitDarts,
      fkRectSquareCoverDartList, pairing, n, L, V, wB, omega,
      fkRectRefinedBoundaryOrbitTranslation_eq_four_deck_winding] using h
  have hAopen : fkRectRefinedRawInteraction A
      ((fkRectRepeatTranslatedDartPath l V L).map
        (fkRectIntegralSquareDartMod L)) = 0 := by
    have h := hblocks.repeated_boundary_interaction_eq_zero
      R F dA n wA z
    change fkRectRefinedRawInteraction A
      ((fkRectRepeatTranslatedDartPath l V L).map
        (fkRectIntegralSquareDartMod L)) = 0
    simpa [A, fkRectCanonicalRefinedBoundaryOrbitCoverDarts,
      fkRectCanonicalRefinedBoundaryOrbitDarts,
      fkRectSquareCoverDartList, pairing, n, L, V, wA, omega,
      fkRectRefinedBoundaryOrbitTranslation_eq_four_deck_winding] using h
  have hBopen : fkRectRefinedRawInteraction B
      ((fkRectRepeatTranslatedDartPath l V L).map
        (fkRectIntegralSquareDartMod L)) = 0 := by
    have h := hblocks.repeated_boundary_interaction_eq_zero
      R F dB n wB z
    change fkRectRefinedRawInteraction B
      ((fkRectRepeatTranslatedDartPath l V L).map
        (fkRectIntegralSquareDartMod L)) = 0
    simpa [B, fkRectCanonicalRefinedBoundaryOrbitCoverDarts,
      fkRectCanonicalRefinedBoundaryOrbitDarts,
      fkRectSquareCoverDartList, pairing, n, L, V, wB, omega,
      fkRectRefinedBoundaryOrbitTranslation_eq_four_deck_winding] using h
  have hAT : fkRectRefinedRawInteraction A T < 0 := by
    change fkRectRefinedRawInteraction A
      ((fkRectRepeatTranslatedDartPath
        (fkRectRefinedPrimalEdgeDarts R e ++ l) V L).map
          (fkRectIntegralSquareDartMod L)) < 0
    rw [fkRectRefinedRawInteraction_repeatTranslated_append_right,
      hAopen, add_zero]
    exact hAedge
  have hBT : 0 ≤ fkRectRefinedRawInteraction B T := by
    change 0 ≤ fkRectRefinedRawInteraction B
      ((fkRectRepeatTranslatedDartPath
        (fkRectRefinedPrimalEdgeDarts R e ++ l) V L).map
          (fkRectIntegralSquareDartMod L))
    rw [fkRectRefinedRawInteraction_repeatTranslated_append_right,
      hBopen, add_zero]
    exact hBedge
  exact fkRectBalancedCarriers_sameSignDiagonal_target_contradiction_neg
    A B T hAbal hBbal hTbal hxsign hdiagA hdiagB hAT hBT




theorem fkRectConnectedInsertion_distinct_sameSignHorizontal_contradiction
    (R : FKRectTorus) (F : Finset R.EdgeIndex) (e : R.EdgeIndex)
    (r : (fkRectOpenGraph R
      (fkRectConfigurationOfEdges R F)).Walk
        (fkRectMedialWestPrimal R e) (fkRectMedialEastPrimal R e))
    (heF : e ∉ F)
    (hsep : ¬ (fkMedialLoopGraph R.medialTorus
      (fkRectConfigurationToMedialPairing R
        (fkRectConfigurationOfEdges R F))).Reachable
          (fkMedialWestDart (fkRectMedialVertexOfEdge R e))
          (fkMedialEastDart (fkRectMedialVertexOfEdge R e)))
    (dB : FKMedialDart R.medialTorus)
    (hcolor : fkMedialCheckerColor dB =
      fkMedialCheckerColor
        (fkMedialWestDart (fkRectMedialVertexOfEdge R e)))
    (hBsep : ¬ (fkMedialLoopGraph R.medialTorus
      (fkRectConfigurationToMedialPairing R
        (fkRectConfigurationOfEdges R F))).Reachable
          (fkMedialWestDart (fkRectMedialVertexOfEdge R e)) dB)
    (hxsign : let omega := fkRectConfigurationOfEdges R F
      let dA := fkMedialWestDart (fkRectMedialVertexOfEdge R e)
      let A := fkRectCanonicalRefinedBoundaryOrbitCoverDarts R omega dA
      let B := fkRectCanonicalRefinedBoundaryOrbitCoverDarts R omega dB
      0 < (A.map StatMech.Onsager.ons_xWrapSign).sum *
        (B.map StatMech.Onsager.ons_xWrapSign).sum)
    (hyA : let omega := fkRectConfigurationOfEdges R F
      let dA := fkMedialWestDart (fkRectMedialVertexOfEdge R e)
      let A := fkRectCanonicalRefinedBoundaryOrbitCoverDarts R omega dA
      (A.map StatMech.Onsager.ons_yWrapSign).sum = 0)
    (hyB : let omega := fkRectConfigurationOfEdges R F
      let B := fkRectCanonicalRefinedBoundaryOrbitCoverDarts R omega dB
      (B.map StatMech.Onsager.ons_yWrapSign).sum = 0) :
    False := by
  classical
  let omega := fkRectConfigurationOfEdges R F
  let G := fkRectOpenGraph R omega
  let G' := fkRectOpenGraph R
    (fkRectConfigurationOfEdges R (insert e F))
  let a := (fkRectLiftedIndexedEdgeEnds R e).1
  let b := (fkRectLiftedIndexedEdgeEnds R e).2
  let hGG' : G ≤ G' := fkRectOpenGraph_le_insert R F e
  have horient := fkRectLiftedIndexedEdgeEnds_medialPrimal_orientation R e
  have hedgeAxis : FKRectSquareAxisStep
      (fkRectSquareDevelopPoint a) (fkRectSquareDevelopPoint b) := by
    unfold FKRectSquareAxisStep
    exact (fkRectLiftedIndexedEdgeEnds_squareStep R e).elim
      Or.inl (fun h => Or.inr (Or.inl h))
  by_cases hp : fkRectClosedPairingAtEdge e = true
  · have horient' :
        fkRectLiftedVertex R a = fkRectMedialEastPrimal R e ∧
        fkRectLiftedVertex R b = fkRectMedialWestPrimal R e := by
      simpa [a, b, hp] using horient
    have ha := horient'.1
    have hb := horient'.2
    obtain ⟨q, l, hq, hrlift, hlpath, hlblocks⟩ :=
      exists_fkRectRefinedOpenWalkCarrier R F r b hb
    let z : G'.Walk (fkRectMedialEastPrimal R e)
        (fkRectMedialEastPrimal R e) :=
      .cons (fkRectOpenGraph_insert_adj_medialPrimals R F e)
        (r.mapLe hGG')
    have hedgeDisp : b - a = fkRectDevelopedStep R
        (fkRectMedialEastPrimal R e) (fkRectMedialWestPrimal R e) := by
      have h := fkRectLiftedIndexedEdgeEnds_developedStep R e
      rw [ha, hb] at h
      exact h.symm
    have hzlift : FKRectSquareWalkLift R z a q := by
      exact FKRectSquareWalkLift.cons ha hb hedgeDisp hedgeAxis
        (hrlift.mapLe R hGG')
    let C : FKRectRefinedWalkCarrier R hzlift :=
      ⟨fkRectRefinedPrimalEdgeDarts R e ++ l,
        (fkRectRefinedPrimalEdgeDarts_path R e).append hlpath⟩
    have htranslation : C.translation =
        (4 * (fkRectSquareDeckTranslation R
          (fkRectWalkWinding R z)).1,
          4 * (fkRectSquareDeckTranslation R
          (fkRectWalkWinding R z)).2) := by
      unfold FKRectRefinedWalkCarrier.translation
      rw [hzlift.closed_develop_sub_eq_deck_winding R]
    have hCbal : DartListBalanced C.coverDarts := by
      apply fkRectSquareCoverDartList_balanced
      exact C.path_translation
    have hTbal :
        let L := fkRectSquareCoverSide (fkRectRefinedCoverTorus R)
        let V : Int × Int :=
          (4 * (fkRectSquareDeckTranslation R
            (fkRectWalkWinding R z)).1,
            4 * (fkRectSquareDeckTranslation R
            (fkRectWalkWinding R z)).2)
        DartListBalanced
          ((fkRectRepeatTranslatedDartPath
            (fkRectRefinedPrimalEdgeDarts R e ++ l) V L).map
              (fkRectIntegralSquareDartMod L)) := by
      dsimp only
      change DartListBalanced
        (fkRectSquareCoverDartList (fkRectRefinedCoverTorus R)
          (fkRectRefinedPrimalEdgeDarts R e ++ l)
          (4 * (fkRectSquareDeckTranslation R
            (fkRectWalkWinding R z)).1,
            4 * (fkRectSquareDeckTranslation R
            (fkRectWalkWinding R z)).2))
      rw [← htranslation]
      exact hCbal
    exact
      fkRectCanonicalBoundaryCarriers_repeatedInsertionTarget_contradiction
        R F e heF hsep dB hcolor hBsep hlblocks
          (fkRectWalkWinding R z) hTbal hxsign hyA hyB
  · have hp' : fkRectClosedPairingAtEdge e = false :=
      Bool.eq_false_of_not_eq_true hp
    have horient' :
        fkRectLiftedVertex R a = fkRectMedialWestPrimal R e ∧
        fkRectLiftedVertex R b = fkRectMedialEastPrimal R e := by
      simpa [a, b, hp, hp'] using horient
    have ha := horient'.1
    have hb := horient'.2
    obtain ⟨q, l, hq, hrlift, hlpath, hlblocks⟩ :=
      exists_fkRectRefinedOpenWalkCarrier R F r.reverse b hb
    let z : G'.Walk (fkRectMedialWestPrimal R e)
        (fkRectMedialWestPrimal R e) :=
      .cons (fkRectOpenGraph_insert_adj_medialPrimals R F e).symm
        (r.reverse.mapLe hGG')
    have hedgeDisp : b - a = fkRectDevelopedStep R
        (fkRectMedialWestPrimal R e) (fkRectMedialEastPrimal R e) := by
      have h := fkRectLiftedIndexedEdgeEnds_developedStep R e
      rw [ha, hb] at h
      exact h.symm
    have hzlift : FKRectSquareWalkLift R z a q := by
      exact FKRectSquareWalkLift.cons ha hb hedgeDisp hedgeAxis
        (hrlift.mapLe R hGG')
    let C : FKRectRefinedWalkCarrier R hzlift :=
      ⟨fkRectRefinedPrimalEdgeDarts R e ++ l,
        (fkRectRefinedPrimalEdgeDarts_path R e).append hlpath⟩
    have htranslation : C.translation =
        (4 * (fkRectSquareDeckTranslation R
          (fkRectWalkWinding R z)).1,
          4 * (fkRectSquareDeckTranslation R
          (fkRectWalkWinding R z)).2) := by
      unfold FKRectRefinedWalkCarrier.translation
      rw [hzlift.closed_develop_sub_eq_deck_winding R]
    have hCbal : DartListBalanced C.coverDarts := by
      apply fkRectSquareCoverDartList_balanced
      exact C.path_translation
    have hTbal :
        let L := fkRectSquareCoverSide (fkRectRefinedCoverTorus R)
        let V : Int × Int :=
          (4 * (fkRectSquareDeckTranslation R
            (fkRectWalkWinding R z)).1,
            4 * (fkRectSquareDeckTranslation R
            (fkRectWalkWinding R z)).2)
        DartListBalanced
          ((fkRectRepeatTranslatedDartPath
            (fkRectRefinedPrimalEdgeDarts R e ++ l) V L).map
              (fkRectIntegralSquareDartMod L)) := by
      dsimp only
      change DartListBalanced
        (fkRectSquareCoverDartList (fkRectRefinedCoverTorus R)
          (fkRectRefinedPrimalEdgeDarts R e ++ l)
          (4 * (fkRectSquareDeckTranslation R
            (fkRectWalkWinding R z)).1,
            4 * (fkRectSquareDeckTranslation R
            (fkRectWalkWinding R z)).2))
      rw [← htranslation]
      exact hCbal
    exact
      fkRectCanonicalBoundaryCarriers_repeatedInsertionTarget_contradiction
        R F e heF hsep dB hcolor hBsep hlblocks
          (fkRectWalkWinding R z) hTbal hxsign hyA hyB




theorem fkRectConnectedInsertion_distinct_sameSignDiagonal_contradiction
    (R : FKRectTorus) (F : Finset R.EdgeIndex) (e : R.EdgeIndex)
    (r : (fkRectOpenGraph R
      (fkRectConfigurationOfEdges R F)).Walk
        (fkRectMedialWestPrimal R e) (fkRectMedialEastPrimal R e))
    (heF : e ∉ F)
    (hsep : ¬ (fkMedialLoopGraph R.medialTorus
      (fkRectConfigurationToMedialPairing R
        (fkRectConfigurationOfEdges R F))).Reachable
          (fkMedialWestDart (fkRectMedialVertexOfEdge R e))
          (fkMedialEastDart (fkRectMedialVertexOfEdge R e)))
    (dB : FKMedialDart R.medialTorus)
    (hcolor : fkMedialCheckerColor dB =
      fkMedialCheckerColor
        (fkMedialWestDart (fkRectMedialVertexOfEdge R e)))
    (hBsep : ¬ (fkMedialLoopGraph R.medialTorus
      (fkRectConfigurationToMedialPairing R
        (fkRectConfigurationOfEdges R F))).Reachable
          (fkMedialWestDart (fkRectMedialVertexOfEdge R e)) dB)
    (hxsign : let omega := fkRectConfigurationOfEdges R F
      let dA := fkMedialWestDart (fkRectMedialVertexOfEdge R e)
      let A := fkRectCanonicalRefinedBoundaryOrbitCoverDarts R omega dA
      let B := fkRectCanonicalRefinedBoundaryOrbitCoverDarts R omega dB
      0 < (A.map StatMech.Onsager.ons_xWrapSign).sum *
        (B.map StatMech.Onsager.ons_xWrapSign).sum)
    (hdiagA : let omega := fkRectConfigurationOfEdges R F
      let dA := fkMedialWestDart (fkRectMedialVertexOfEdge R e)
      let A := fkRectCanonicalRefinedBoundaryOrbitCoverDarts R omega dA
      (A.map StatMech.Onsager.ons_yWrapSign).sum =
        (A.map StatMech.Onsager.ons_xWrapSign).sum)
    (hdiagB : let omega := fkRectConfigurationOfEdges R F
      let B := fkRectCanonicalRefinedBoundaryOrbitCoverDarts R omega dB
      (B.map StatMech.Onsager.ons_yWrapSign).sum =
        (B.map StatMech.Onsager.ons_xWrapSign).sum) :
    False := by
  classical
  let omega := fkRectConfigurationOfEdges R F
  let G := fkRectOpenGraph R omega
  let G' := fkRectOpenGraph R
    (fkRectConfigurationOfEdges R (insert e F))
  let a := (fkRectLiftedIndexedEdgeEnds R e).1
  let b := (fkRectLiftedIndexedEdgeEnds R e).2
  let hGG' : G ≤ G' := fkRectOpenGraph_le_insert R F e
  have horient := fkRectLiftedIndexedEdgeEnds_medialPrimal_orientation R e
  have hedgeAxis : FKRectSquareAxisStep
      (fkRectSquareDevelopPoint a) (fkRectSquareDevelopPoint b) := by
    unfold FKRectSquareAxisStep
    exact (fkRectLiftedIndexedEdgeEnds_squareStep R e).elim
      Or.inl (fun h => Or.inr (Or.inl h))
  by_cases hp : fkRectClosedPairingAtEdge e = true
  · have horient' :
        fkRectLiftedVertex R a = fkRectMedialEastPrimal R e ∧
        fkRectLiftedVertex R b = fkRectMedialWestPrimal R e := by
      simpa [a, b, hp] using horient
    have ha := horient'.1
    have hb := horient'.2
    obtain ⟨q, l, hq, hrlift, hlpath, hlblocks⟩ :=
      exists_fkRectRefinedOpenWalkCarrier R F r b hb
    let z : G'.Walk (fkRectMedialEastPrimal R e)
        (fkRectMedialEastPrimal R e) :=
      .cons (fkRectOpenGraph_insert_adj_medialPrimals R F e)
        (r.mapLe hGG')
    have hedgeDisp : b - a = fkRectDevelopedStep R
        (fkRectMedialEastPrimal R e) (fkRectMedialWestPrimal R e) := by
      have h := fkRectLiftedIndexedEdgeEnds_developedStep R e
      rw [ha, hb] at h
      exact h.symm
    have hzlift : FKRectSquareWalkLift R z a q := by
      exact FKRectSquareWalkLift.cons ha hb hedgeDisp hedgeAxis
        (hrlift.mapLe R hGG')
    let C : FKRectRefinedWalkCarrier R hzlift :=
      ⟨fkRectRefinedPrimalEdgeDarts R e ++ l,
        (fkRectRefinedPrimalEdgeDarts_path R e).append hlpath⟩
    have htranslation : C.translation =
        (4 * (fkRectSquareDeckTranslation R
          (fkRectWalkWinding R z)).1,
          4 * (fkRectSquareDeckTranslation R
          (fkRectWalkWinding R z)).2) := by
      unfold FKRectRefinedWalkCarrier.translation
      rw [hzlift.closed_develop_sub_eq_deck_winding R]
    have hCbal : DartListBalanced C.coverDarts := by
      apply fkRectSquareCoverDartList_balanced
      exact C.path_translation
    have hTbal :
        let L := fkRectSquareCoverSide (fkRectRefinedCoverTorus R)
        let V : Int × Int :=
          (4 * (fkRectSquareDeckTranslation R
            (fkRectWalkWinding R z)).1,
            4 * (fkRectSquareDeckTranslation R
            (fkRectWalkWinding R z)).2)
        DartListBalanced
          ((fkRectRepeatTranslatedDartPath
            (fkRectRefinedPrimalEdgeDarts R e ++ l) V L).map
              (fkRectIntegralSquareDartMod L)) := by
      dsimp only
      change DartListBalanced
        (fkRectSquareCoverDartList (fkRectRefinedCoverTorus R)
          (fkRectRefinedPrimalEdgeDarts R e ++ l)
          (4 * (fkRectSquareDeckTranslation R
            (fkRectWalkWinding R z)).1,
            4 * (fkRectSquareDeckTranslation R
            (fkRectWalkWinding R z)).2))
      rw [← htranslation]
      exact hCbal
    exact
      fkRectCanonicalBoundaryCarriers_repeatedInsertionTarget_diagonal_contradiction
        R F e heF hsep dB hcolor hBsep hlblocks
          (fkRectWalkWinding R z) hTbal hxsign hdiagA hdiagB
  · have hp' : fkRectClosedPairingAtEdge e = false :=
      Bool.eq_false_of_not_eq_true hp
    have horient' :
        fkRectLiftedVertex R a = fkRectMedialWestPrimal R e ∧
        fkRectLiftedVertex R b = fkRectMedialEastPrimal R e := by
      simpa [a, b, hp, hp'] using horient
    have ha := horient'.1
    have hb := horient'.2
    obtain ⟨q, l, hq, hrlift, hlpath, hlblocks⟩ :=
      exists_fkRectRefinedOpenWalkCarrier R F r.reverse b hb
    let z : G'.Walk (fkRectMedialWestPrimal R e)
        (fkRectMedialWestPrimal R e) :=
      .cons (fkRectOpenGraph_insert_adj_medialPrimals R F e).symm
        (r.reverse.mapLe hGG')
    have hedgeDisp : b - a = fkRectDevelopedStep R
        (fkRectMedialWestPrimal R e) (fkRectMedialEastPrimal R e) := by
      have h := fkRectLiftedIndexedEdgeEnds_developedStep R e
      rw [ha, hb] at h
      exact h.symm
    have hzlift : FKRectSquareWalkLift R z a q := by
      exact FKRectSquareWalkLift.cons ha hb hedgeDisp hedgeAxis
        (hrlift.mapLe R hGG')
    let C : FKRectRefinedWalkCarrier R hzlift :=
      ⟨fkRectRefinedPrimalEdgeDarts R e ++ l,
        (fkRectRefinedPrimalEdgeDarts_path R e).append hlpath⟩
    have htranslation : C.translation =
        (4 * (fkRectSquareDeckTranslation R
          (fkRectWalkWinding R z)).1,
          4 * (fkRectSquareDeckTranslation R
          (fkRectWalkWinding R z)).2) := by
      unfold FKRectRefinedWalkCarrier.translation
      rw [hzlift.closed_develop_sub_eq_deck_winding R]
    have hCbal : DartListBalanced C.coverDarts := by
      apply fkRectSquareCoverDartList_balanced
      exact C.path_translation
    have hTbal :
        let L := fkRectSquareCoverSide (fkRectRefinedCoverTorus R)
        let V : Int × Int :=
          (4 * (fkRectSquareDeckTranslation R
            (fkRectWalkWinding R z)).1,
            4 * (fkRectSquareDeckTranslation R
            (fkRectWalkWinding R z)).2)
        DartListBalanced
          ((fkRectRepeatTranslatedDartPath
            (fkRectRefinedPrimalEdgeDarts R e ++ l) V L).map
              (fkRectIntegralSquareDartMod L)) := by
      dsimp only
      change DartListBalanced
        (fkRectSquareCoverDartList (fkRectRefinedCoverTorus R)
          (fkRectRefinedPrimalEdgeDarts R e ++ l)
          (4 * (fkRectSquareDeckTranslation R
            (fkRectWalkWinding R z)).1,
            4 * (fkRectSquareDeckTranslation R
            (fkRectWalkWinding R z)).2))
      rw [← htranslation]
      exact hCbal
    exact
      fkRectCanonicalBoundaryCarriers_repeatedInsertionTarget_diagonal_contradiction
        R F e heF hsep dB hcolor hBsep hlblocks
          (fkRectWalkWinding R z) hTbal hxsign hdiagA hdiagB



theorem fkRectConnectedInsertion_distinct_sameSignDiagonal_contradiction_east
    (R : FKRectTorus) (F : Finset R.EdgeIndex) (e : R.EdgeIndex)
    (r : (fkRectOpenGraph R
      (fkRectConfigurationOfEdges R F)).Walk
        (fkRectMedialWestPrimal R e) (fkRectMedialEastPrimal R e))
    (heF : e ∉ F)
    (hsep : ¬ (fkMedialLoopGraph R.medialTorus
      (fkRectConfigurationToMedialPairing R
        (fkRectConfigurationOfEdges R F))).Reachable
          (fkMedialWestDart (fkRectMedialVertexOfEdge R e))
          (fkMedialEastDart (fkRectMedialVertexOfEdge R e)))
    (dB : FKMedialDart R.medialTorus)
    (hcolor : fkMedialCheckerColor dB =
      fkMedialCheckerColor
        (fkMedialEastDart (fkRectMedialVertexOfEdge R e)))
    (hBsep : ¬ (fkMedialLoopGraph R.medialTorus
      (fkRectConfigurationToMedialPairing R
        (fkRectConfigurationOfEdges R F))).Reachable
          (fkMedialEastDart (fkRectMedialVertexOfEdge R e)) dB)
    (hxsign : let omega := fkRectConfigurationOfEdges R F
      let dA := fkMedialEastDart (fkRectMedialVertexOfEdge R e)
      let A := fkRectCanonicalRefinedBoundaryOrbitCoverDarts R omega dA
      let B := fkRectCanonicalRefinedBoundaryOrbitCoverDarts R omega dB
      0 < (A.map StatMech.Onsager.ons_xWrapSign).sum *
        (B.map StatMech.Onsager.ons_xWrapSign).sum)
    (hdiagA : let omega := fkRectConfigurationOfEdges R F
      let dA := fkMedialEastDart (fkRectMedialVertexOfEdge R e)
      let A := fkRectCanonicalRefinedBoundaryOrbitCoverDarts R omega dA
      (A.map StatMech.Onsager.ons_yWrapSign).sum =
        (A.map StatMech.Onsager.ons_xWrapSign).sum)
    (hdiagB : let omega := fkRectConfigurationOfEdges R F
      let B := fkRectCanonicalRefinedBoundaryOrbitCoverDarts R omega dB
      (B.map StatMech.Onsager.ons_yWrapSign).sum =
        (B.map StatMech.Onsager.ons_xWrapSign).sum) :
    False := by
  classical
  let omega := fkRectConfigurationOfEdges R F
  let G := fkRectOpenGraph R omega
  let G' := fkRectOpenGraph R
    (fkRectConfigurationOfEdges R (insert e F))
  let a := (fkRectLiftedIndexedEdgeEnds R e).1
  let b := (fkRectLiftedIndexedEdgeEnds R e).2
  let hGG' : G ≤ G' := fkRectOpenGraph_le_insert R F e
  have horient := fkRectLiftedIndexedEdgeEnds_medialPrimal_orientation R e
  have hedgeAxis : FKRectSquareAxisStep
      (fkRectSquareDevelopPoint a) (fkRectSquareDevelopPoint b) := by
    unfold FKRectSquareAxisStep
    exact (fkRectLiftedIndexedEdgeEnds_squareStep R e).elim
      Or.inl (fun h => Or.inr (Or.inl h))
  by_cases hp : fkRectClosedPairingAtEdge e = true
  · have horient' :
        fkRectLiftedVertex R a = fkRectMedialEastPrimal R e ∧
        fkRectLiftedVertex R b = fkRectMedialWestPrimal R e := by
      simpa [a, b, hp] using horient
    have ha := horient'.1
    have hb := horient'.2
    obtain ⟨q, l, hq, hrlift, hlpath, hlblocks⟩ :=
      exists_fkRectRefinedOpenWalkCarrier R F r b hb
    let z : G'.Walk (fkRectMedialEastPrimal R e)
        (fkRectMedialEastPrimal R e) :=
      .cons (fkRectOpenGraph_insert_adj_medialPrimals R F e)
        (r.mapLe hGG')
    have hedgeDisp : b - a = fkRectDevelopedStep R
        (fkRectMedialEastPrimal R e) (fkRectMedialWestPrimal R e) := by
      have h := fkRectLiftedIndexedEdgeEnds_developedStep R e
      rw [ha, hb] at h
      exact h.symm
    have hzlift : FKRectSquareWalkLift R z a q := by
      exact FKRectSquareWalkLift.cons ha hb hedgeDisp hedgeAxis
        (hrlift.mapLe R hGG')
    let C : FKRectRefinedWalkCarrier R hzlift :=
      ⟨fkRectRefinedPrimalEdgeDarts R e ++ l,
        (fkRectRefinedPrimalEdgeDarts_path R e).append hlpath⟩
    have htranslation : C.translation =
        (4 * (fkRectSquareDeckTranslation R
          (fkRectWalkWinding R z)).1,
          4 * (fkRectSquareDeckTranslation R
          (fkRectWalkWinding R z)).2) := by
      unfold FKRectRefinedWalkCarrier.translation
      rw [hzlift.closed_develop_sub_eq_deck_winding R]
    have hCbal : DartListBalanced C.coverDarts := by
      apply fkRectSquareCoverDartList_balanced
      exact C.path_translation
    have hTbal :
        let L := fkRectSquareCoverSide (fkRectRefinedCoverTorus R)
        let V : Int × Int :=
          (4 * (fkRectSquareDeckTranslation R
            (fkRectWalkWinding R z)).1,
            4 * (fkRectSquareDeckTranslation R
            (fkRectWalkWinding R z)).2)
        DartListBalanced
          ((fkRectRepeatTranslatedDartPath
            (fkRectRefinedPrimalEdgeDarts R e ++ l) V L).map
              (fkRectIntegralSquareDartMod L)) := by
      dsimp only
      change DartListBalanced
        (fkRectSquareCoverDartList (fkRectRefinedCoverTorus R)
          (fkRectRefinedPrimalEdgeDarts R e ++ l)
          (4 * (fkRectSquareDeckTranslation R
            (fkRectWalkWinding R z)).1,
            4 * (fkRectSquareDeckTranslation R
            (fkRectWalkWinding R z)).2))
      rw [← htranslation]
      exact hCbal
    exact
      fkRectCanonicalBoundaryCarriers_repeatedInsertionTarget_diagonal_contradiction_east
        R F e heF hsep dB hcolor hBsep hlblocks
          (fkRectWalkWinding R z) hTbal hxsign hdiagA hdiagB
  · have hp' : fkRectClosedPairingAtEdge e = false :=
      Bool.eq_false_of_not_eq_true hp
    have horient' :
        fkRectLiftedVertex R a = fkRectMedialWestPrimal R e ∧
        fkRectLiftedVertex R b = fkRectMedialEastPrimal R e := by
      simpa [a, b, hp, hp'] using horient
    have ha := horient'.1
    have hb := horient'.2
    obtain ⟨q, l, hq, hrlift, hlpath, hlblocks⟩ :=
      exists_fkRectRefinedOpenWalkCarrier R F r.reverse b hb
    let z : G'.Walk (fkRectMedialWestPrimal R e)
        (fkRectMedialWestPrimal R e) :=
      .cons (fkRectOpenGraph_insert_adj_medialPrimals R F e).symm
        (r.reverse.mapLe hGG')
    have hedgeDisp : b - a = fkRectDevelopedStep R
        (fkRectMedialWestPrimal R e) (fkRectMedialEastPrimal R e) := by
      have h := fkRectLiftedIndexedEdgeEnds_developedStep R e
      rw [ha, hb] at h
      exact h.symm
    have hzlift : FKRectSquareWalkLift R z a q := by
      exact FKRectSquareWalkLift.cons ha hb hedgeDisp hedgeAxis
        (hrlift.mapLe R hGG')
    let C : FKRectRefinedWalkCarrier R hzlift :=
      ⟨fkRectRefinedPrimalEdgeDarts R e ++ l,
        (fkRectRefinedPrimalEdgeDarts_path R e).append hlpath⟩
    have htranslation : C.translation =
        (4 * (fkRectSquareDeckTranslation R
          (fkRectWalkWinding R z)).1,
          4 * (fkRectSquareDeckTranslation R
          (fkRectWalkWinding R z)).2) := by
      unfold FKRectRefinedWalkCarrier.translation
      rw [hzlift.closed_develop_sub_eq_deck_winding R]
    have hCbal : DartListBalanced C.coverDarts := by
      apply fkRectSquareCoverDartList_balanced
      exact C.path_translation
    have hTbal :
        let L := fkRectSquareCoverSide (fkRectRefinedCoverTorus R)
        let V : Int × Int :=
          (4 * (fkRectSquareDeckTranslation R
            (fkRectWalkWinding R z)).1,
            4 * (fkRectSquareDeckTranslation R
            (fkRectWalkWinding R z)).2)
        DartListBalanced
          ((fkRectRepeatTranslatedDartPath
            (fkRectRefinedPrimalEdgeDarts R e ++ l) V L).map
              (fkRectIntegralSquareDartMod L)) := by
      dsimp only
      change DartListBalanced
        (fkRectSquareCoverDartList (fkRectRefinedCoverTorus R)
          (fkRectRefinedPrimalEdgeDarts R e ++ l)
          (4 * (fkRectSquareDeckTranslation R
            (fkRectWalkWinding R z)).1,
            4 * (fkRectSquareDeckTranslation R
            (fkRectWalkWinding R z)).2))
      rw [← htranslation]
      exact hCbal
    exact
      fkRectCanonicalBoundaryCarriers_repeatedInsertionTarget_diagonal_contradiction_east
        R F e heF hsep dB hcolor hBsep hlblocks
          (fkRectWalkWinding R z) hTbal hxsign hdiagA hdiagB


theorem
    fkRectConnectedInsertion_distinct_sameSignFKHorizontal_contradiction
    (R : FKRectTorus) (F : Finset R.EdgeIndex) (e : R.EdgeIndex)
    (r : (fkRectOpenGraph R
      (fkRectConfigurationOfEdges R F)).Walk
        (fkRectMedialWestPrimal R e) (fkRectMedialEastPrimal R e))
    (heF : e ∉ F)
    (hsep : ¬ (fkMedialLoopGraph R.medialTorus
      (fkRectConfigurationToMedialPairing R
        (fkRectConfigurationOfEdges R F))).Reachable
          (fkMedialWestDart (fkRectMedialVertexOfEdge R e))
          (fkMedialEastDart (fkRectMedialVertexOfEdge R e)))
    (dB : FKMedialDart R.medialTorus)
    (hcolor : fkMedialCheckerColor dB =
      fkMedialCheckerColor
        (fkMedialWestDart (fkRectMedialVertexOfEdge R e)))
    (hBsep : ¬ (fkMedialLoopGraph R.medialTorus
      (fkRectConfigurationToMedialPairing R
        (fkRectConfigurationOfEdges R F))).Reachable
          (fkMedialWestDart (fkRectMedialVertexOfEdge R e)) dB)
    (hxsign : let omega := fkRectConfigurationOfEdges R F
      let dA := fkMedialWestDart (fkRectMedialVertexOfEdge R e)
      0 < (fkRectWalkWinding R
          (fkRectMedialBoundaryPrimalOrbitWalk R omega dA)).1 *
        (fkRectWalkWinding R
          (fkRectMedialBoundaryPrimalOrbitWalk R omega dB)).1)
    (hyA : let omega := fkRectConfigurationOfEdges R F
      let dA := fkMedialWestDart (fkRectMedialVertexOfEdge R e)
      (fkRectWalkWinding R
        (fkRectMedialBoundaryPrimalOrbitWalk R omega dA)).2 = 0)
    (hyB : let omega := fkRectConfigurationOfEdges R F
      (fkRectWalkWinding R
        (fkRectMedialBoundaryPrimalOrbitWalk R omega dB)).2 = 0) :
    False := by
  dsimp only at hxsign hyA hyB
  apply fkRectConnectedInsertion_distinct_sameSignDiagonal_contradiction
    R F e r heF hsep dB hcolor hBsep
  · dsimp only
    rw [fkRectCanonicalRefinedBoundaryOrbitCoverDarts_xWrap_eq,
      fkRectCanonicalRefinedBoundaryOrbitCoverDarts_xWrap_eq]
    simp only [fkRectSquareDeckTranslation, hyA, hyB, mul_zero, add_zero]
    have hwidth : (0 : Int) < R.width := by exact_mod_cast R.width_pos
    have hscale : (0 : Int) < 16 * (R.width : Int) ^ 2 := by positivity
    nlinarith [mul_pos hscale hxsign]
  · dsimp only
    rw [fkRectCanonicalRefinedBoundaryOrbitCoverDarts_xWrap_eq,
      fkRectCanonicalRefinedBoundaryOrbitCoverDarts_yWrap_eq]
    simp [fkRectSquareDeckTranslation, hyA]
  · dsimp only
    rw [fkRectCanonicalRefinedBoundaryOrbitCoverDarts_xWrap_eq,
      fkRectCanonicalRefinedBoundaryOrbitCoverDarts_yWrap_eq]
    simp [fkRectSquareDeckTranslation, hyB]



theorem
    fkRectConnectedInsertion_distinct_sameSignFKHorizontal_contradiction_east
    (R : FKRectTorus) (F : Finset R.EdgeIndex) (e : R.EdgeIndex)
    (r : (fkRectOpenGraph R
      (fkRectConfigurationOfEdges R F)).Walk
        (fkRectMedialWestPrimal R e) (fkRectMedialEastPrimal R e))
    (heF : e ∉ F)
    (hsep : ¬ (fkMedialLoopGraph R.medialTorus
      (fkRectConfigurationToMedialPairing R
        (fkRectConfigurationOfEdges R F))).Reachable
          (fkMedialWestDart (fkRectMedialVertexOfEdge R e))
          (fkMedialEastDart (fkRectMedialVertexOfEdge R e)))
    (dB : FKMedialDart R.medialTorus)
    (hcolor : fkMedialCheckerColor dB =
      fkMedialCheckerColor
        (fkMedialEastDart (fkRectMedialVertexOfEdge R e)))
    (hBsep : ¬ (fkMedialLoopGraph R.medialTorus
      (fkRectConfigurationToMedialPairing R
        (fkRectConfigurationOfEdges R F))).Reachable
          (fkMedialEastDart (fkRectMedialVertexOfEdge R e)) dB)
    (hxsign : let omega := fkRectConfigurationOfEdges R F
      let dA := fkMedialEastDart (fkRectMedialVertexOfEdge R e)
      0 < (fkRectWalkWinding R
          (fkRectMedialBoundaryPrimalOrbitWalk R omega dA)).1 *
        (fkRectWalkWinding R
          (fkRectMedialBoundaryPrimalOrbitWalk R omega dB)).1)
    (hyA : let omega := fkRectConfigurationOfEdges R F
      let dA := fkMedialEastDart (fkRectMedialVertexOfEdge R e)
      (fkRectWalkWinding R
        (fkRectMedialBoundaryPrimalOrbitWalk R omega dA)).2 = 0)
    (hyB : let omega := fkRectConfigurationOfEdges R F
      (fkRectWalkWinding R
        (fkRectMedialBoundaryPrimalOrbitWalk R omega dB)).2 = 0) :
    False := by
  dsimp only at hxsign hyA hyB
  apply fkRectConnectedInsertion_distinct_sameSignDiagonal_contradiction_east
    R F e r heF hsep dB hcolor hBsep
  · dsimp only
    rw [fkRectCanonicalRefinedBoundaryOrbitCoverDarts_xWrap_eq,
      fkRectCanonicalRefinedBoundaryOrbitCoverDarts_xWrap_eq]
    simp only [fkRectSquareDeckTranslation, hyA, hyB, mul_zero, add_zero]
    have hwidth : (0 : Int) < R.width := by exact_mod_cast R.width_pos
    have hscale : (0 : Int) < 16 * (R.width : Int) ^ 2 := by positivity
    nlinarith [mul_pos hscale hxsign]
  · dsimp only
    rw [fkRectCanonicalRefinedBoundaryOrbitCoverDarts_xWrap_eq,
      fkRectCanonicalRefinedBoundaryOrbitCoverDarts_yWrap_eq]
    simp [fkRectSquareDeckTranslation, hyA]
  · dsimp only
    rw [fkRectCanonicalRefinedBoundaryOrbitCoverDarts_xWrap_eq,
      fkRectCanonicalRefinedBoundaryOrbitCoverDarts_yWrap_eq]
    simp [fkRectSquareDeckTranslation, hyB]





theorem fkRectCanonicalBoundaryCarrier_localPotential_contradiction
    (R : FKRectTorus) (F : Finset R.EdgeIndex) (e : R.EdgeIndex)
    (heF : e ∉ F)
    (hsep : ¬ (fkMedialLoopGraph R.medialTorus
      (fkRectConfigurationToMedialPairing R
        (fkRectConfigurationOfEdges R F))).Reachable
          (fkMedialWestDart (fkRectMedialVertexOfEdge R e))
          (fkMedialEastDart (fkRectMedialVertexOfEdge R e)))
    (dB : FKMedialDart R.medialTorus)
    {l : List FKRectIntegralSquareDart}
    (hl : FKRectIntegralSquareDartPath
      (fkRectRefinedPrimalEdgeStart R e)
      (fkRectRefinedPrimalEdgeEnd R e) l)
    (hblocks : FKRectRefinedOpenEdgeBlocks R F l)
    (hx : let omega := fkRectConfigurationOfEdges R F
      let dA := fkMedialWestDart (fkRectMedialVertexOfEdge R e)
      let A := fkRectCanonicalRefinedBoundaryOrbitCoverDarts R omega dA
      let B := fkRectCanonicalRefinedBoundaryOrbitCoverDarts R omega dB
      (A.map StatMech.Onsager.ons_xWrapSign).sum =
        (B.map StatMech.Onsager.ons_xWrapSign).sum)
    (hy : let omega := fkRectConfigurationOfEdges R F
      let dA := fkMedialWestDart (fkRectMedialVertexOfEdge R e)
      let A := fkRectCanonicalRefinedBoundaryOrbitCoverDarts R omega dA
      let B := fkRectCanonicalRefinedBoundaryOrbitCoverDarts R omega dB
      (A.map StatMech.Onsager.ons_yWrapSign).sum =
        (B.map StatMech.Onsager.ons_yWrapSign).sum)
    (hBedge : let omega := fkRectConfigurationOfEdges R F
      let B := fkRectCanonicalRefinedBoundaryOrbitCoverDarts R omega dB
      fkRectRefinedRawInteraction B
        ((fkRectRefinedPrimalEdgeDarts R e).map
          (fkRectIntegralSquareDartMod
            (fkRectSquareCoverSide (fkRectRefinedCoverTorus R)))) = 0) :
    False := by
  classical
  let omega := fkRectConfigurationOfEdges R F
  let dA := fkMedialWestDart (fkRectMedialVertexOfEdge R e)
  let A := fkRectCanonicalRefinedBoundaryOrbitCoverDarts R omega dA
  let B := fkRectCanonicalRefinedBoundaryOrbitCoverDarts R omega dB
  let wA := fkRectWalkWinding R
    (fkRectMedialBoundaryPrimalOrbitWalk R omega dA)
  let wB := fkRectWalkWinding R
    (fkRectMedialBoundaryPrimalOrbitWalk R omega dB)
  let n := orderOf (fkMedialBoundaryStep
    (fkRectConfigurationToMedialPairing R omega))
  let L := fkRectSquareCoverSide (fkRectRefinedCoverTorus R)
  have hAbal : DartListBalanced A := by
    apply fkRectSquareCoverDartList_balanced
    exact fkRectCanonicalRefinedBoundaryOrbitDarts_path_translation
      R omega dA
  have hBbal : DartListBalanced B := by
    apply fkRectSquareCoverDartList_balanced
    exact fkRectCanonicalRefinedBoundaryOrbitDarts_path_translation
      R omega dB
  have hx' : (ofDartList A hAbal).xFlux (-1) =
      (ofDartList B hBbal).xFlux (-1) := by
    rw [ofDartList_xFlux, ofDartList_xFlux]
    exact hx
  have hy' : (ofDartList A hAbal).yFlux (-1) =
      (ofDartList B hBbal).yFlux (-1) := by
    rw [ofDartList_yFlux, ofDartList_yFlux]
    exact hy
  have hAopen : fkRectRefinedRawInteraction A
      (l.map (fkRectIntegralSquareDartMod L)) = 0 := by
    have h := hblocks.boundary_interaction_eq_zero
      R F dA n wA
    change fkRectRefinedRawInteraction A
      (l.map (fkRectIntegralSquareDartMod L)) = 0
    simpa [A, fkRectCanonicalRefinedBoundaryOrbitCoverDarts,
      fkRectCanonicalRefinedBoundaryOrbitDarts,
      fkRectSquareCoverDartList, n, L, wA, omega,
      fkRectRefinedBoundaryOrbitTranslation_eq_four_deck_winding] using h
  have hBopen : fkRectRefinedRawInteraction B
      (l.map (fkRectIntegralSquareDartMod L)) = 0 := by
    have h := hblocks.boundary_interaction_eq_zero
      R F dB n wB
    change fkRectRefinedRawInteraction B
      (l.map (fkRectIntegralSquareDartMod L)) = 0
    simpa [B, fkRectCanonicalRefinedBoundaryOrbitCoverDarts,
      fkRectCanonicalRefinedBoundaryOrbitDarts,
      fkRectSquareCoverDartList, n, L, wB, omega,
      fkRectRefinedBoundaryOrbitTranslation_eq_four_deck_winding] using h
  have hAlocal : fkRectRefinedRawInteraction A
      ((fkRectRefinedPrimalEdgeDarts R e).map
        (fkRectIntegralSquareDartMod L)) ≠ 0 := by
    have h :=
      fkRectRefinedRawInteraction_repeated_boundary_edgeOnce_ne_zero
        R F e heF wA hsep
    change fkRectRefinedRawInteraction A
      ((fkRectRefinedPrimalEdgeDarts R e).map
        (fkRectIntegralSquareDartMod L)) ≠ 0
    simpa [A, fkRectCanonicalRefinedBoundaryOrbitCoverDarts,
      fkRectCanonicalRefinedBoundaryOrbitDarts,
      fkRectSquareCoverDartList, n, L, wA, omega,
      fkRectRefinedBoundaryOrbitTranslation_eq_four_deck_winding] using h
  have heq := fkRectRefinedRawInteraction_sub_eq_of_equalFlux
    A B hAbal hBbal hx' hy' hl
      (fkRectRefinedPrimalEdgeDarts_path R e)
  change fkRectRefinedRawInteraction A
        (l.map (fkRectIntegralSquareDartMod L)) -
      fkRectRefinedRawInteraction B
        (l.map (fkRectIntegralSquareDartMod L)) =
    fkRectRefinedRawInteraction A
        ((fkRectRefinedPrimalEdgeDarts R e).map
          (fkRectIntegralSquareDartMod L)) -
      fkRectRefinedRawInteraction B
        ((fkRectRefinedPrimalEdgeDarts R e).map
          (fkRectIntegralSquareDartMod L)) at heq
  dsimp only at hBedge
  rw [hAopen, hBopen, hBedge] at heq
  simp only [sub_self, sub_zero] at heq
  exact hAlocal heq.symm





theorem
    fkRectCanonicalBoundaryCarrier_sameSignHorizontal_localPotential_contradiction
    (R : FKRectTorus) (F : Finset R.EdgeIndex) (e : R.EdgeIndex)
    (heF : e ∉ F)
    (hsep : ¬ (fkMedialLoopGraph R.medialTorus
      (fkRectConfigurationToMedialPairing R
        (fkRectConfigurationOfEdges R F))).Reachable
          (fkMedialWestDart (fkRectMedialVertexOfEdge R e))
          (fkMedialEastDart (fkRectMedialVertexOfEdge R e)))
    (dB : FKMedialDart R.medialTorus)
    {l : List FKRectIntegralSquareDart}
    (hl : FKRectIntegralSquareDartPath
      (fkRectRefinedPrimalEdgeStart R e)
      (fkRectRefinedPrimalEdgeEnd R e) l)
    (hblocks : FKRectRefinedOpenEdgeBlocks R F l)
    (hxsign : let omega := fkRectConfigurationOfEdges R F
      let dA := fkMedialWestDart (fkRectMedialVertexOfEdge R e)
      let A := fkRectCanonicalRefinedBoundaryOrbitCoverDarts R omega dA
      let B := fkRectCanonicalRefinedBoundaryOrbitCoverDarts R omega dB
      0 < (A.map StatMech.Onsager.ons_xWrapSign).sum *
        (B.map StatMech.Onsager.ons_xWrapSign).sum)
    (hyA : let omega := fkRectConfigurationOfEdges R F
      let dA := fkMedialWestDart (fkRectMedialVertexOfEdge R e)
      let A := fkRectCanonicalRefinedBoundaryOrbitCoverDarts R omega dA
      (A.map StatMech.Onsager.ons_yWrapSign).sum = 0)
    (hyB : let omega := fkRectConfigurationOfEdges R F
      let B := fkRectCanonicalRefinedBoundaryOrbitCoverDarts R omega dB
      (B.map StatMech.Onsager.ons_yWrapSign).sum = 0)
    (hBedge : let omega := fkRectConfigurationOfEdges R F
      let B := fkRectCanonicalRefinedBoundaryOrbitCoverDarts R omega dB
      fkRectRefinedRawInteraction B
        ((fkRectRefinedPrimalEdgeDarts R e).map
          (fkRectIntegralSquareDartMod
            (fkRectSquareCoverSide (fkRectRefinedCoverTorus R)))) = 0) :
    False := by
  classical
  let omega := fkRectConfigurationOfEdges R F
  let dA := fkMedialWestDart (fkRectMedialVertexOfEdge R e)
  let A := fkRectCanonicalRefinedBoundaryOrbitCoverDarts R omega dA
  let B := fkRectCanonicalRefinedBoundaryOrbitCoverDarts R omega dB
  let xA := (A.map StatMech.Onsager.ons_xWrapSign).sum
  let xB := (B.map StatMech.Onsager.ons_xWrapSign).sum
  let kA := xB.natAbs
  let kB := xA.natAbs
  let AA := fkRectRepeatDartList kA A
  let BB := fkRectRepeatDartList kB B
  let wA := fkRectWalkWinding R
    (fkRectMedialBoundaryPrimalOrbitWalk R omega dA)
  let wB := fkRectWalkWinding R
    (fkRectMedialBoundaryPrimalOrbitWalk R omega dB)
  let n := orderOf (fkMedialBoundaryStep
    (fkRectConfigurationToMedialPairing R omega))
  let L := fkRectSquareCoverSide (fkRectRefinedCoverTorus R)
  have hxsign' : 0 < xA * xB := hxsign
  have hxAne : xA ≠ 0 := by
    intro h
    rw [h, zero_mul] at hxsign'
    exact (lt_irrefl 0) hxsign'
  have hxBne : xB ≠ 0 := by
    intro h
    rw [h, mul_zero] at hxsign'
    exact (lt_irrefl 0) hxsign'
  have hkA : (kA : Int) ≠ 0 := by
    exact_mod_cast (Int.natAbs_pos.mpr hxBne).ne'
  have hAbal : DartListBalanced A := by
    apply fkRectSquareCoverDartList_balanced
    exact fkRectCanonicalRefinedBoundaryOrbitDarts_path_translation
      R omega dA
  have hBbal : DartListBalanced B := by
    apply fkRectSquareCoverDartList_balanced
    exact fkRectCanonicalRefinedBoundaryOrbitDarts_path_translation
      R omega dB
  have hAAbal : DartListBalanced AA :=
    fkRectRepeatDartList_balanced kA A hAbal
  have hBBbal : DartListBalanced BB :=
    fkRectRepeatDartList_balanced kB B hBbal
  have hxscaled :
      (AA.map StatMech.Onsager.ons_xWrapSign).sum =
        (BB.map StatMech.Onsager.ons_xWrapSign).sum := by
    rw [fkRectRepeatDartList_map_sum,
      fkRectRepeatDartList_map_sum]
    exact int_natAbs_cross_mul_eq_of_mul_pos xA xB hxsign'
  have hyscaled :
      (AA.map StatMech.Onsager.ons_yWrapSign).sum =
        (BB.map StatMech.Onsager.ons_yWrapSign).sum := by
    rw [fkRectRepeatDartList_map_sum,
      fkRectRepeatDartList_map_sum]
    rw [hyA, hyB, mul_zero, mul_zero]
  have hAopen : fkRectRefinedRawInteraction A
      (l.map (fkRectIntegralSquareDartMod L)) = 0 := by
    have h := hblocks.boundary_interaction_eq_zero R F dA n wA
    change fkRectRefinedRawInteraction A
      (l.map (fkRectIntegralSquareDartMod L)) = 0
    simpa [A, fkRectCanonicalRefinedBoundaryOrbitCoverDarts,
      fkRectCanonicalRefinedBoundaryOrbitDarts,
      fkRectSquareCoverDartList, n, L, wA, omega,
      fkRectRefinedBoundaryOrbitTranslation_eq_four_deck_winding] using h
  have hBopen : fkRectRefinedRawInteraction B
      (l.map (fkRectIntegralSquareDartMod L)) = 0 := by
    have h := hblocks.boundary_interaction_eq_zero R F dB n wB
    change fkRectRefinedRawInteraction B
      (l.map (fkRectIntegralSquareDartMod L)) = 0
    simpa [B, fkRectCanonicalRefinedBoundaryOrbitCoverDarts,
      fkRectCanonicalRefinedBoundaryOrbitDarts,
      fkRectSquareCoverDartList, n, L, wB, omega,
      fkRectRefinedBoundaryOrbitTranslation_eq_four_deck_winding] using h
  have hAlocal : fkRectRefinedRawInteraction A
      ((fkRectRefinedPrimalEdgeDarts R e).map
        (fkRectIntegralSquareDartMod L)) ≠ 0 := by
    have h :=
      fkRectRefinedRawInteraction_repeated_boundary_edgeOnce_ne_zero
        R F e heF wA hsep
    change fkRectRefinedRawInteraction A
      ((fkRectRefinedPrimalEdgeDarts R e).map
        (fkRectIntegralSquareDartMod L)) ≠ 0
    simpa [A, fkRectCanonicalRefinedBoundaryOrbitCoverDarts,
      fkRectCanonicalRefinedBoundaryOrbitDarts,
      fkRectSquareCoverDartList, n, L, wA, omega,
      fkRectRefinedBoundaryOrbitTranslation_eq_four_deck_winding] using h
  have hAAopen : fkRectRefinedRawInteraction AA
      (l.map (fkRectIntegralSquareDartMod L)) = 0 := by
    rw [fkRectRefinedRawInteraction_repeatDartList_left, hAopen, mul_zero]
  have hBBopen : fkRectRefinedRawInteraction BB
      (l.map (fkRectIntegralSquareDartMod L)) = 0 := by
    rw [fkRectRefinedRawInteraction_repeatDartList_left, hBopen, mul_zero]
  have hAAlocal : fkRectRefinedRawInteraction AA
      ((fkRectRefinedPrimalEdgeDarts R e).map
        (fkRectIntegralSquareDartMod L)) ≠ 0 := by
    rw [fkRectRefinedRawInteraction_repeatDartList_left]
    exact mul_ne_zero hkA hAlocal
  have hBBlocal : fkRectRefinedRawInteraction BB
      ((fkRectRefinedPrimalEdgeDarts R e).map
        (fkRectIntegralSquareDartMod L)) = 0 := by
    rw [fkRectRefinedRawInteraction_repeatDartList_left, hBedge, mul_zero]
  exact fkRectBalancedCarriers_localPotential_contradiction
    AA BB hAAbal hBBbal hl (fkRectRefinedPrimalEdgeDarts_path R e)
      hxscaled hyscaled hAAopen hBBopen hAAlocal hBBlocal





theorem
    fkRectCanonicalBoundaryCarrier_distinct_sameSignHorizontal_contradiction
    (R : FKRectTorus) (F : Finset R.EdgeIndex) (e : R.EdgeIndex)
    (heF : e ∉ F)
    (hsep : ¬ (fkMedialLoopGraph R.medialTorus
      (fkRectConfigurationToMedialPairing R
        (fkRectConfigurationOfEdges R F))).Reachable
          (fkMedialWestDart (fkRectMedialVertexOfEdge R e))
          (fkMedialEastDart (fkRectMedialVertexOfEdge R e)))
    (dB : FKMedialDart R.medialTorus)
    (hcolor : fkMedialCheckerColor dB =
      fkMedialCheckerColor
        (fkMedialWestDart (fkRectMedialVertexOfEdge R e)))
    (hBsep : ¬ (fkMedialLoopGraph R.medialTorus
      (fkRectConfigurationToMedialPairing R
        (fkRectConfigurationOfEdges R F))).Reachable
          (fkMedialWestDart (fkRectMedialVertexOfEdge R e)) dB)
    {l : List FKRectIntegralSquareDart}
    (hl : FKRectIntegralSquareDartPath
      (fkRectRefinedPrimalEdgeStart R e)
      (fkRectRefinedPrimalEdgeEnd R e) l)
    (hblocks : FKRectRefinedOpenEdgeBlocks R F l)
    (hxsign : let omega := fkRectConfigurationOfEdges R F
      let dA := fkMedialWestDart (fkRectMedialVertexOfEdge R e)
      let A := fkRectCanonicalRefinedBoundaryOrbitCoverDarts R omega dA
      let B := fkRectCanonicalRefinedBoundaryOrbitCoverDarts R omega dB
      0 < (A.map StatMech.Onsager.ons_xWrapSign).sum *
        (B.map StatMech.Onsager.ons_xWrapSign).sum)
    (hyA : let omega := fkRectConfigurationOfEdges R F
      let dA := fkMedialWestDart (fkRectMedialVertexOfEdge R e)
      let A := fkRectCanonicalRefinedBoundaryOrbitCoverDarts R omega dA
      (A.map StatMech.Onsager.ons_yWrapSign).sum = 0)
    (hyB : let omega := fkRectConfigurationOfEdges R F
      let B := fkRectCanonicalRefinedBoundaryOrbitCoverDarts R omega dB
      (B.map StatMech.Onsager.ons_yWrapSign).sum = 0) :
    False := by
  classical
  let omega := fkRectConfigurationOfEdges R F
  let pairing := fkRectConfigurationToMedialPairing R omega
  let dA := fkMedialWestDart (fkRectMedialVertexOfEdge R e)
  let A := fkRectCanonicalRefinedBoundaryOrbitCoverDarts R omega dA
  let B := fkRectCanonicalRefinedBoundaryOrbitCoverDarts R omega dB
  let wA := fkRectWalkWinding R
    (fkRectMedialBoundaryPrimalOrbitWalk R omega dA)
  let wB := fkRectWalkWinding R
    (fkRectMedialBoundaryPrimalOrbitWalk R omega dB)
  let n := orderOf (fkMedialBoundaryStep pairing)
  let L := fkRectSquareCoverSide (fkRectRefinedCoverTorus R)
  have hAbal : DartListBalanced A := by
    apply fkRectSquareCoverDartList_balanced
    exact fkRectCanonicalRefinedBoundaryOrbitDarts_path_translation
      R omega dA
  have hBbal : DartListBalanced B := by
    apply fkRectSquareCoverDartList_balanced
    exact fkRectCanonicalRefinedBoundaryOrbitDarts_path_translation
      R omega dB
  have hAopen : fkRectRefinedRawInteraction A
      (l.map (fkRectIntegralSquareDartMod L)) = 0 := by
    have h := hblocks.boundary_interaction_eq_zero R F dA n wA
    change fkRectRefinedRawInteraction A
      (l.map (fkRectIntegralSquareDartMod L)) = 0
    simpa [A, fkRectCanonicalRefinedBoundaryOrbitCoverDarts,
      fkRectCanonicalRefinedBoundaryOrbitDarts,
      fkRectSquareCoverDartList, pairing, n, L, wA, omega,
      fkRectRefinedBoundaryOrbitTranslation_eq_four_deck_winding] using h
  have hBopen : fkRectRefinedRawInteraction B
      (l.map (fkRectIntegralSquareDartMod L)) = 0 := by
    have h := hblocks.boundary_interaction_eq_zero R F dB n wB
    change fkRectRefinedRawInteraction B
      (l.map (fkRectIntegralSquareDartMod L)) = 0
    simpa [B, fkRectCanonicalRefinedBoundaryOrbitCoverDarts,
      fkRectCanonicalRefinedBoundaryOrbitDarts,
      fkRectSquareCoverDartList, pairing, n, L, wB, omega,
      fkRectRefinedBoundaryOrbitTranslation_eq_four_deck_winding] using h
  have hAlocal : 0 < fkRectRefinedRawInteraction A
      ((fkRectRefinedPrimalEdgeDarts R e).map
        (fkRectIntegralSquareDartMod L)) := by
    have h :=
      fkRectRefinedRawInteraction_repeated_west_boundary_edgeOnce_pos
        R F e heF wA hsep
    change 0 < fkRectRefinedRawInteraction A
      ((fkRectRefinedPrimalEdgeDarts R e).map
        (fkRectIntegralSquareDartMod L))
    simpa [A, fkRectCanonicalRefinedBoundaryOrbitCoverDarts,
      fkRectCanonicalRefinedBoundaryOrbitDarts,
      fkRectSquareCoverDartList, pairing, n, L, wA, omega,
      fkRectRefinedBoundaryOrbitTranslation_eq_four_deck_winding] using h
  have havoidB : ∀ k : Nat,
      (fkMedialBoundaryStep pairing)^[k] dB ≠ dA := by
    intro k hk
    apply hBsep
    have hr := fkMedialBoundaryStep_iterate_reachable pairing dB k
    rw [hk] at hr
    exact hr.symm
  have hBlocal : fkRectRefinedRawInteraction B
      ((fkRectRefinedPrimalEdgeDarts R e).map
        (fkRectIntegralSquareDartMod L)) ≤ 0 := by
    have h :=
      fkRectRefinedRawInteraction_repeated_boundary_edgeOnce_nonpos_of_avoid_west
        R F e heF dB wB hcolor havoidB
    change fkRectRefinedRawInteraction B
      ((fkRectRefinedPrimalEdgeDarts R e).map
        (fkRectIntegralSquareDartMod L)) ≤ 0
    simpa [B, fkRectCanonicalRefinedBoundaryOrbitCoverDarts,
      fkRectCanonicalRefinedBoundaryOrbitDarts,
      fkRectSquareCoverDartList, pairing, n, L, wB, omega,
      fkRectRefinedBoundaryOrbitTranslation_eq_four_deck_winding] using h
  exact fkRectBalancedCarriers_sameSignHorizontal_signed_contradiction
    A B hAbal hBbal hl (fkRectRefinedPrimalEdgeDarts_path R e)
      hxsign hyA hyB hAopen hBopen hAlocal hBlocal



theorem
    fkRectCanonicalBoundaryCarrier_distinct_sameSignDiagonal_contradiction
    (R : FKRectTorus) (F : Finset R.EdgeIndex) (e : R.EdgeIndex)
    (heF : e ∉ F)
    (hsep : ¬ (fkMedialLoopGraph R.medialTorus
      (fkRectConfigurationToMedialPairing R
        (fkRectConfigurationOfEdges R F))).Reachable
          (fkMedialWestDart (fkRectMedialVertexOfEdge R e))
          (fkMedialEastDart (fkRectMedialVertexOfEdge R e)))
    (dB : FKMedialDart R.medialTorus)
    (hcolor : fkMedialCheckerColor dB =
      fkMedialCheckerColor
        (fkMedialWestDart (fkRectMedialVertexOfEdge R e)))
    (hBsep : ¬ (fkMedialLoopGraph R.medialTorus
      (fkRectConfigurationToMedialPairing R
        (fkRectConfigurationOfEdges R F))).Reachable
          (fkMedialWestDart (fkRectMedialVertexOfEdge R e)) dB)
    {l : List FKRectIntegralSquareDart}
    (hl : FKRectIntegralSquareDartPath
      (fkRectRefinedPrimalEdgeStart R e)
      (fkRectRefinedPrimalEdgeEnd R e) l)
    (hblocks : FKRectRefinedOpenEdgeBlocks R F l)
    (hxsign : let omega := fkRectConfigurationOfEdges R F
      let dA := fkMedialWestDart (fkRectMedialVertexOfEdge R e)
      let A := fkRectCanonicalRefinedBoundaryOrbitCoverDarts R omega dA
      let B := fkRectCanonicalRefinedBoundaryOrbitCoverDarts R omega dB
      0 < (A.map StatMech.Onsager.ons_xWrapSign).sum *
        (B.map StatMech.Onsager.ons_xWrapSign).sum)
    (hdiagA : let omega := fkRectConfigurationOfEdges R F
      let dA := fkMedialWestDart (fkRectMedialVertexOfEdge R e)
      let A := fkRectCanonicalRefinedBoundaryOrbitCoverDarts R omega dA
      (A.map StatMech.Onsager.ons_yWrapSign).sum =
        (A.map StatMech.Onsager.ons_xWrapSign).sum)
    (hdiagB : let omega := fkRectConfigurationOfEdges R F
      let B := fkRectCanonicalRefinedBoundaryOrbitCoverDarts R omega dB
      (B.map StatMech.Onsager.ons_yWrapSign).sum =
        (B.map StatMech.Onsager.ons_xWrapSign).sum) :
    False := by
  classical
  let omega := fkRectConfigurationOfEdges R F
  let pairing := fkRectConfigurationToMedialPairing R omega
  let dA := fkMedialWestDart (fkRectMedialVertexOfEdge R e)
  let A := fkRectCanonicalRefinedBoundaryOrbitCoverDarts R omega dA
  let B := fkRectCanonicalRefinedBoundaryOrbitCoverDarts R omega dB
  let wA := fkRectWalkWinding R
    (fkRectMedialBoundaryPrimalOrbitWalk R omega dA)
  let wB := fkRectWalkWinding R
    (fkRectMedialBoundaryPrimalOrbitWalk R omega dB)
  let n := orderOf (fkMedialBoundaryStep pairing)
  let L := fkRectSquareCoverSide (fkRectRefinedCoverTorus R)
  have hAbal : DartListBalanced A := by
    apply fkRectSquareCoverDartList_balanced
    exact fkRectCanonicalRefinedBoundaryOrbitDarts_path_translation
      R omega dA
  have hBbal : DartListBalanced B := by
    apply fkRectSquareCoverDartList_balanced
    exact fkRectCanonicalRefinedBoundaryOrbitDarts_path_translation
      R omega dB
  have hAopen : fkRectRefinedRawInteraction A
      (l.map (fkRectIntegralSquareDartMod L)) = 0 := by
    have h := hblocks.boundary_interaction_eq_zero R F dA n wA
    change fkRectRefinedRawInteraction A
      (l.map (fkRectIntegralSquareDartMod L)) = 0
    simpa [A, fkRectCanonicalRefinedBoundaryOrbitCoverDarts,
      fkRectCanonicalRefinedBoundaryOrbitDarts,
      fkRectSquareCoverDartList, pairing, n, L, wA, omega,
      fkRectRefinedBoundaryOrbitTranslation_eq_four_deck_winding] using h
  have hBopen : fkRectRefinedRawInteraction B
      (l.map (fkRectIntegralSquareDartMod L)) = 0 := by
    have h := hblocks.boundary_interaction_eq_zero R F dB n wB
    change fkRectRefinedRawInteraction B
      (l.map (fkRectIntegralSquareDartMod L)) = 0
    simpa [B, fkRectCanonicalRefinedBoundaryOrbitCoverDarts,
      fkRectCanonicalRefinedBoundaryOrbitDarts,
      fkRectSquareCoverDartList, pairing, n, L, wB, omega,
      fkRectRefinedBoundaryOrbitTranslation_eq_four_deck_winding] using h
  have hAlocal : 0 < fkRectRefinedRawInteraction A
      ((fkRectRefinedPrimalEdgeDarts R e).map
        (fkRectIntegralSquareDartMod L)) := by
    have h :=
      fkRectRefinedRawInteraction_repeated_west_boundary_edgeOnce_pos
        R F e heF wA hsep
    change 0 < fkRectRefinedRawInteraction A
      ((fkRectRefinedPrimalEdgeDarts R e).map
        (fkRectIntegralSquareDartMod L))
    simpa [A, fkRectCanonicalRefinedBoundaryOrbitCoverDarts,
      fkRectCanonicalRefinedBoundaryOrbitDarts,
      fkRectSquareCoverDartList, pairing, n, L, wA, omega,
      fkRectRefinedBoundaryOrbitTranslation_eq_four_deck_winding] using h
  have havoidB : ∀ k : Nat,
      (fkMedialBoundaryStep pairing)^[k] dB ≠ dA := by
    intro k hk
    apply hBsep
    have hr := fkMedialBoundaryStep_iterate_reachable pairing dB k
    rw [hk] at hr
    exact hr.symm
  have hBlocal : fkRectRefinedRawInteraction B
      ((fkRectRefinedPrimalEdgeDarts R e).map
        (fkRectIntegralSquareDartMod L)) ≤ 0 := by
    have h :=
      fkRectRefinedRawInteraction_repeated_boundary_edgeOnce_nonpos_of_avoid_west
        R F e heF dB wB hcolor havoidB
    change fkRectRefinedRawInteraction B
      ((fkRectRefinedPrimalEdgeDarts R e).map
        (fkRectIntegralSquareDartMod L)) ≤ 0
    simpa [B, fkRectCanonicalRefinedBoundaryOrbitCoverDarts,
      fkRectCanonicalRefinedBoundaryOrbitDarts,
      fkRectSquareCoverDartList, pairing, n, L, wB, omega,
      fkRectRefinedBoundaryOrbitTranslation_eq_four_deck_winding] using h
  exact fkRectBalancedCarriers_sameSignDiagonal_signed_contradiction
    A B hAbal hBbal hl (fkRectRefinedPrimalEdgeDarts_path R e)
      hxsign hdiagA hdiagB hAopen hBopen hAlocal hBlocal




theorem
    fkRectCanonicalBoundaryCarrier_distinct_sameSignFKHorizontal_contradiction
    (R : FKRectTorus) (F : Finset R.EdgeIndex) (e : R.EdgeIndex)
    (heF : e ∉ F)
    (hsep : ¬ (fkMedialLoopGraph R.medialTorus
      (fkRectConfigurationToMedialPairing R
        (fkRectConfigurationOfEdges R F))).Reachable
          (fkMedialWestDart (fkRectMedialVertexOfEdge R e))
          (fkMedialEastDart (fkRectMedialVertexOfEdge R e)))
    (dB : FKMedialDart R.medialTorus)
    (hcolor : fkMedialCheckerColor dB =
      fkMedialCheckerColor
        (fkMedialWestDart (fkRectMedialVertexOfEdge R e)))
    (hBsep : ¬ (fkMedialLoopGraph R.medialTorus
      (fkRectConfigurationToMedialPairing R
        (fkRectConfigurationOfEdges R F))).Reachable
          (fkMedialWestDart (fkRectMedialVertexOfEdge R e)) dB)
    {l : List FKRectIntegralSquareDart}
    (hl : FKRectIntegralSquareDartPath
      (fkRectRefinedPrimalEdgeStart R e)
      (fkRectRefinedPrimalEdgeEnd R e) l)
    (hblocks : FKRectRefinedOpenEdgeBlocks R F l)
    (hxsign : let omega := fkRectConfigurationOfEdges R F
      let dA := fkMedialWestDart (fkRectMedialVertexOfEdge R e)
      0 < (fkRectWalkWinding R
          (fkRectMedialBoundaryPrimalOrbitWalk R omega dA)).1 *
        (fkRectWalkWinding R
          (fkRectMedialBoundaryPrimalOrbitWalk R omega dB)).1)
    (hyA : let omega := fkRectConfigurationOfEdges R F
      let dA := fkMedialWestDart (fkRectMedialVertexOfEdge R e)
      (fkRectWalkWinding R
        (fkRectMedialBoundaryPrimalOrbitWalk R omega dA)).2 = 0)
    (hyB : let omega := fkRectConfigurationOfEdges R F
      (fkRectWalkWinding R
        (fkRectMedialBoundaryPrimalOrbitWalk R omega dB)).2 = 0) :
    False := by
  dsimp only at hxsign hyA hyB
  apply fkRectCanonicalBoundaryCarrier_distinct_sameSignDiagonal_contradiction
    R F e heF hsep dB hcolor hBsep hl hblocks
  · dsimp only
    rw [fkRectCanonicalRefinedBoundaryOrbitCoverDarts_xWrap_eq,
      fkRectCanonicalRefinedBoundaryOrbitCoverDarts_xWrap_eq]
    simp only [fkRectSquareDeckTranslation, hyA, hyB, mul_zero, add_zero]
    have hwidth : (0 : Int) < R.width := by exact_mod_cast R.width_pos
    have hscale : (0 : Int) < 16 * (R.width : Int) ^ 2 := by positivity
    nlinarith [mul_pos hscale hxsign]
  · dsimp only
    rw [fkRectCanonicalRefinedBoundaryOrbitCoverDarts_xWrap_eq,
      fkRectCanonicalRefinedBoundaryOrbitCoverDarts_yWrap_eq]
    simp [fkRectSquareDeckTranslation, hyA]
  · dsimp only
    rw [fkRectCanonicalRefinedBoundaryOrbitCoverDarts_xWrap_eq,
      fkRectCanonicalRefinedBoundaryOrbitCoverDarts_yWrap_eq]
    simp [fkRectSquareDeckTranslation, hyB]




theorem fkRectCanonicalBoundaryCarrier_distinct_equalWinding_contradiction
    (R : FKRectTorus) (F : Finset R.EdgeIndex) (e : R.EdgeIndex)
    (heF : e ∉ F)
    (hsep : ¬ (fkMedialLoopGraph R.medialTorus
      (fkRectConfigurationToMedialPairing R
        (fkRectConfigurationOfEdges R F))).Reachable
          (fkMedialWestDart (fkRectMedialVertexOfEdge R e))
          (fkMedialEastDart (fkRectMedialVertexOfEdge R e)))
    (dB : FKMedialDart R.medialTorus)
    (hcolor : fkMedialCheckerColor dB =
      fkMedialCheckerColor
        (fkMedialWestDart (fkRectMedialVertexOfEdge R e)))
    (hBsep : ¬ (fkMedialLoopGraph R.medialTorus
      (fkRectConfigurationToMedialPairing R
        (fkRectConfigurationOfEdges R F))).Reachable
          (fkMedialWestDart (fkRectMedialVertexOfEdge R e)) dB)
    {l : List FKRectIntegralSquareDart}
    (hl : FKRectIntegralSquareDartPath
      (fkRectRefinedPrimalEdgeStart R e)
      (fkRectRefinedPrimalEdgeEnd R e) l)
    (hblocks : FKRectRefinedOpenEdgeBlocks R F l)
    (hwinding : let omega := fkRectConfigurationOfEdges R F
      let dA := fkMedialWestDart (fkRectMedialVertexOfEdge R e)
      fkRectWalkWinding R
          (fkRectMedialBoundaryPrimalOrbitWalk R omega dA) =
        fkRectWalkWinding R
          (fkRectMedialBoundaryPrimalOrbitWalk R omega dB)) :
    False := by
  classical
  let omega := fkRectConfigurationOfEdges R F
  let pairing := fkRectConfigurationToMedialPairing R omega
  let dA := fkMedialWestDart (fkRectMedialVertexOfEdge R e)
  let A := fkRectCanonicalRefinedBoundaryOrbitCoverDarts R omega dA
  let B := fkRectCanonicalRefinedBoundaryOrbitCoverDarts R omega dB
  let wA := fkRectWalkWinding R
    (fkRectMedialBoundaryPrimalOrbitWalk R omega dA)
  let wB := fkRectWalkWinding R
    (fkRectMedialBoundaryPrimalOrbitWalk R omega dB)
  let n := orderOf (fkMedialBoundaryStep pairing)
  let L := fkRectSquareCoverSide (fkRectRefinedCoverTorus R)
  have hAbal : DartListBalanced A := by
    apply fkRectSquareCoverDartList_balanced
    exact fkRectCanonicalRefinedBoundaryOrbitDarts_path_translation
      R omega dA
  have hBbal : DartListBalanced B := by
    apply fkRectSquareCoverDartList_balanced
    exact fkRectCanonicalRefinedBoundaryOrbitDarts_path_translation
      R omega dB
  have hx : (A.map StatMech.Onsager.ons_xWrapSign).sum =
      (B.map StatMech.Onsager.ons_xWrapSign).sum := by
    rw [fkRectCanonicalRefinedBoundaryOrbitCoverDarts_xWrap_eq,
      fkRectCanonicalRefinedBoundaryOrbitCoverDarts_xWrap_eq,
      hwinding]
  have hy : (A.map StatMech.Onsager.ons_yWrapSign).sum =
      (B.map StatMech.Onsager.ons_yWrapSign).sum := by
    rw [fkRectCanonicalRefinedBoundaryOrbitCoverDarts_yWrap_eq,
      fkRectCanonicalRefinedBoundaryOrbitCoverDarts_yWrap_eq,
      hwinding]
  have hAopen : fkRectRefinedRawInteraction A
      (l.map (fkRectIntegralSquareDartMod L)) = 0 := by
    have h := hblocks.boundary_interaction_eq_zero R F dA n wA
    change fkRectRefinedRawInteraction A
      (l.map (fkRectIntegralSquareDartMod L)) = 0
    simpa [A, fkRectCanonicalRefinedBoundaryOrbitCoverDarts,
      fkRectCanonicalRefinedBoundaryOrbitDarts,
      fkRectSquareCoverDartList, pairing, n, L, wA, omega,
      fkRectRefinedBoundaryOrbitTranslation_eq_four_deck_winding] using h
  have hBopen : fkRectRefinedRawInteraction B
      (l.map (fkRectIntegralSquareDartMod L)) = 0 := by
    have h := hblocks.boundary_interaction_eq_zero R F dB n wB
    change fkRectRefinedRawInteraction B
      (l.map (fkRectIntegralSquareDartMod L)) = 0
    simpa [B, fkRectCanonicalRefinedBoundaryOrbitCoverDarts,
      fkRectCanonicalRefinedBoundaryOrbitDarts,
      fkRectSquareCoverDartList, pairing, n, L, wB, omega,
      fkRectRefinedBoundaryOrbitTranslation_eq_four_deck_winding] using h
  have hAlocal : 0 < fkRectRefinedRawInteraction A
      ((fkRectRefinedPrimalEdgeDarts R e).map
        (fkRectIntegralSquareDartMod L)) := by
    have h :=
      fkRectRefinedRawInteraction_repeated_west_boundary_edgeOnce_pos
        R F e heF wA hsep
    change 0 < fkRectRefinedRawInteraction A
      ((fkRectRefinedPrimalEdgeDarts R e).map
        (fkRectIntegralSquareDartMod L))
    simpa [A, fkRectCanonicalRefinedBoundaryOrbitCoverDarts,
      fkRectCanonicalRefinedBoundaryOrbitDarts,
      fkRectSquareCoverDartList, pairing, n, L, wA, omega,
      fkRectRefinedBoundaryOrbitTranslation_eq_four_deck_winding] using h
  have havoidB : ∀ k : Nat,
      (fkMedialBoundaryStep pairing)^[k] dB ≠ dA := by
    intro k hk
    apply hBsep
    have hr := fkMedialBoundaryStep_iterate_reachable pairing dB k
    rw [hk] at hr
    exact hr.symm
  have hBlocal : fkRectRefinedRawInteraction B
      ((fkRectRefinedPrimalEdgeDarts R e).map
        (fkRectIntegralSquareDartMod L)) ≤ 0 := by
    have h :=
      fkRectRefinedRawInteraction_repeated_boundary_edgeOnce_nonpos_of_avoid_west
        R F e heF dB wB hcolor havoidB
    change fkRectRefinedRawInteraction B
      ((fkRectRefinedPrimalEdgeDarts R e).map
        (fkRectIntegralSquareDartMod L)) ≤ 0
    simpa [B, fkRectCanonicalRefinedBoundaryOrbitCoverDarts,
      fkRectCanonicalRefinedBoundaryOrbitDarts,
      fkRectSquareCoverDartList, pairing, n, L, wB, omega,
      fkRectRefinedBoundaryOrbitTranslation_eq_four_deck_winding] using h
  exact fkRectBalancedCarriers_equalFlux_signed_contradiction
    A B hAbal hBbal hl (fkRectRefinedPrimalEdgeDarts_path R e)
      hx hy hAopen hBopen hAlocal hBlocal

end

end StatMech.FrontierD
