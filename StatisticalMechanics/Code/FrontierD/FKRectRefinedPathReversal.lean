/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/




import Code.FrontierD.FKRectRefinedBoundaryRepeatedVisits



namespace StatMech.FrontierD

open StatMech.Onsager

noncomputable section


def fkRectIntegralSquareDartReverse
    (d : FKRectIntegralSquareDart) : FKRectIntegralSquareDart :=
  (fkRectIntegralSquareDartEnd d, d.2 + 2)


def fkRectIntegralSquareDartListReverse
    (l : List FKRectIntegralSquareDart) : List FKRectIntegralSquareDart :=
  l.reverse.map fkRectIntegralSquareDartReverse

@[simp] theorem fkRectIntegralSquareDartEnd_reverse
    (d : FKRectIntegralSquareDart) :
    fkRectIntegralSquareDartEnd (fkRectIntegralSquareDartReverse d) = d.1 := by
  rcases d with ⟨⟨x, y⟩, mu⟩
  fin_cases mu <;>
    simp [fkRectIntegralSquareDartReverse, fkRectIntegralSquareDartEnd,
      StatMech.Onsager.ons_dirExponentX,
      StatMech.Onsager.ons_dirExponentY]


theorem FKRectIntegralSquareDartPath.reverse
    {p q : Int × Int} {l : List FKRectIntegralSquareDart}
    (h : FKRectIntegralSquareDartPath p q l) :
    FKRectIntegralSquareDartPath q p
      (fkRectIntegralSquareDartListReverse l) := by
  induction h with
  | nil p => simp [fkRectIntegralSquareDartListReverse,
      FKRectIntegralSquareDartPath.nil]
  | @cons d q r l hend tail ih =>
      unfold fkRectIntegralSquareDartListReverse at ih ⊢
      rw [List.reverse_cons, List.map_append]
      have hlast : FKRectIntegralSquareDartPath q d.1
          [fkRectIntegralSquareDartReverse d] := by
        have hstart : (fkRectIntegralSquareDartReverse d).1 = q := by
          exact hend
        rw [← hstart]
        refine FKRectIntegralSquareDartPath.cons
          (fkRectIntegralSquareDartReverse d) ?_
          (FKRectIntegralSquareDartPath.nil d.1)
        exact fkRectIntegralSquareDartEnd_reverse d
      simpa using ih.append hlast

theorem fkRectIntegralSquareDartReverse_translate
    (t : Int × Int) (d : FKRectIntegralSquareDart) :
    fkRectIntegralSquareDartReverse
        (fkRectIntegralSquareDartTranslate t d) =
      fkRectIntegralSquareDartTranslate t
        (fkRectIntegralSquareDartReverse d) := by
  rcases d with ⟨⟨x, y⟩, mu⟩
  fin_cases mu <;>
    simp [fkRectIntegralSquareDartReverse,
      fkRectIntegralSquareDartTranslate,
      fkRectIntegralSquareDartEnd,
      StatMech.Onsager.ons_dirExponentX,
      StatMech.Onsager.ons_dirExponentY] <;> ring

theorem fkRectIntegralSquareDartListReverse_translate
    (t : Int × Int) (l : List FKRectIntegralSquareDart) :
    fkRectIntegralSquareDartListReverse
        (l.map (fkRectIntegralSquareDartTranslate t)) =
      (fkRectIntegralSquareDartListReverse l).map
        (fkRectIntegralSquareDartTranslate t) := by
  simp [fkRectIntegralSquareDartListReverse, List.map_reverse,
    List.map_map, fkRectIntegralSquareDartReverse_translate]

theorem fkRectIntegralSquareDartMod_reverse
    (L : Nat) (d : FKRectIntegralSquareDart) :
    fkRectIntegralSquareDartMod L (fkRectIntegralSquareDartReverse d) =
      ons_dartRev L (fkRectIntegralSquareDartMod L d) := by
  rcases d with ⟨⟨x, y⟩, mu⟩
  fin_cases mu <;>
    simp [fkRectIntegralSquareDartReverse, fkRectIntegralSquareDartEnd,
      fkRectIntegralSquareDartMod, ons_dartRev, ons_dirStep,
      StatMech.Onsager.ons_dirExponentX,
      StatMech.Onsager.ons_dirExponentY] <;> ring

private theorem dartHorizontal_reverse {L : Nat}
    (d : ons_Dart L) (p : ZMod L × ZMod L) :
    IntegralSquareTorusCycle.dartHorizontal (ons_dartRev L d) p =
      -IntegralSquareTorusCycle.dartHorizontal d p := by
  rcases d with ⟨⟨x, y⟩, mu⟩
  fin_cases mu <;>
    simp [ons_dartRev, ons_dirStep,
      IntegralSquareTorusCycle.dartHorizontal] <;> ring

private theorem dartVertical_reverse {L : Nat}
    (d : ons_Dart L) (p : ZMod L × ZMod L) :
    IntegralSquareTorusCycle.dartVertical (ons_dartRev L d) p =
      -IntegralSquareTorusCycle.dartVertical d p := by
  rcases d with ⟨⟨x, y⟩, mu⟩
  fin_cases mu <;>
    simp [ons_dartRev, ons_dirStep,
      IntegralSquareTorusCycle.dartVertical] <;> ring


theorem fkRectRefinedRawInteraction_reverse_right
    {L : Nat} [Fact (8 < L)] (a b : List (ons_Dart L)) :
    fkRectRefinedRawInteraction a (b.reverse.map (ons_dartRev L)) =
      -fkRectRefinedRawInteraction a b := by
  classical
  have hh (p : ZMod L × ZMod L) :
      (((b.reverse.map (ons_dartRev L)).map
        (fun d => IntegralSquareTorusCycle.dartHorizontal d p)).sum) =
        -((b.map (fun d =>
          IntegralSquareTorusCycle.dartHorizontal d p)).sum) := by
    calc
      _ = (b.reverse.map fun d =>
          -IntegralSquareTorusCycle.dartHorizontal d p).sum := by
        congr 1
        simp only [List.map_map, Function.comp_def]
        apply List.map_congr_left
        intro d hd
        exact dartHorizontal_reverse d p
      _ = _ := by
        rw [List.map_reverse, List.sum_reverse, List.sum_neg]
        simp only [List.map_map, Function.comp_def]
  have hv (p : ZMod L × ZMod L) :
      (((b.reverse.map (ons_dartRev L)).map
        (fun d => IntegralSquareTorusCycle.dartVertical d p)).sum) =
        -((b.map (fun d =>
          IntegralSquareTorusCycle.dartVertical d p)).sum) := by
    calc
      _ = (b.reverse.map fun d =>
          -IntegralSquareTorusCycle.dartVertical d p).sum := by
        congr 1
        simp only [List.map_map, Function.comp_def]
        apply List.map_congr_left
        intro d hd
        exact dartVertical_reverse d p
      _ = _ := by
        rw [List.map_reverse, List.sum_reverse, List.sum_neg]
        simp only [List.map_map, Function.comp_def]
  unfold fkRectRefinedRawInteraction
  simp_rw [hh, hv]
  rw [← Finset.sum_neg_distrib]
  apply Finset.sum_congr rfl
  intro p hp
  ring


theorem fkRectRefinedRawInteraction_integralReverse_right
    {L : Nat} [Fact (8 < L)] (a : List (ons_Dart L))
    (b : List FKRectIntegralSquareDart) :
    fkRectRefinedRawInteraction a
        ((fkRectIntegralSquareDartListReverse b).map
          (fkRectIntegralSquareDartMod L)) =
      -fkRectRefinedRawInteraction a
        (b.map (fkRectIntegralSquareDartMod L)) := by
  have hmap :
      (fkRectIntegralSquareDartListReverse b).map
          (fkRectIntegralSquareDartMod L) =
        (b.map (fkRectIntegralSquareDartMod L)).reverse.map
          (ons_dartRev L) := by
    simp [fkRectIntegralSquareDartListReverse, List.map_reverse,
      List.map_map, fkRectIntegralSquareDartMod_reverse]
  rw [hmap]
  exact fkRectRefinedRawInteraction_reverse_right _ _



theorem fkRectRefinedRawInteraction_translated_boundary_openEdgeReverse_eq_zero
    (R : FKRectTorus) (F : Finset R.EdgeIndex) (e : R.EdgeIndex)
    (heF : e ∈ F) (d : FKMedialDart R.medialTorus) (n : Nat)
    (a b u : Int × Int)
    (hrelative : (a.1 - b.1, a.2 - b.2) =
      (4 * (fkRectSquareDeckTranslation R u).1,
        4 * (fkRectSquareDeckTranslation R u).2)) :
    let pairing := fkRectConfigurationToMedialPairing R
      (fkRectConfigurationOfEdges R F)
    let c := fkRectRefinedBoundaryCanonicalCenter R d
    let L := fkRectSquareCoverSide (fkRectRefinedCoverTorus R)
    fkRectRefinedRawInteraction
        (((fkRectRefinedBoundaryDarts pairing d c n).map
          (fkRectIntegralSquareDartTranslate a)).map
            (fkRectIntegralSquareDartMod L))
        (((fkRectIntegralSquareDartListReverse
          (fkRectRefinedPrimalEdgeDarts R e)).map
            (fkRectIntegralSquareDartTranslate b)).map
              (fkRectIntegralSquareDartMod L)) = 0 := by
  dsimp only
  let pairing := fkRectConfigurationToMedialPairing R
    (fkRectConfigurationOfEdges R F)
  let c := fkRectRefinedBoundaryCanonicalCenter R d
  let L := fkRectSquareCoverSide (fkRectRefinedCoverTorus R)
  let A := ((fkRectRefinedBoundaryDarts pairing d c n).map
    (fkRectIntegralSquareDartTranslate a)).map
      (fkRectIntegralSquareDartMod L)
  have hrev := fkRectIntegralSquareDartListReverse_translate b
    (fkRectRefinedPrimalEdgeDarts R e)
  rw [← hrev]
  rw [fkRectRefinedRawInteraction_integralReverse_right]
  rw [fkRectRefinedRawInteraction_translated_boundary_openEdge_eq_zero
    R F e heF d n a b u hrelative]
  simp



theorem fkRectRefinedRawInteraction_repeated_boundary_openEdgeReverse_eq_zero
    (R : FKRectTorus) (F : Finset R.EdgeIndex) (e : R.EdgeIndex)
    (heF : e ∈ F) (d : FKMedialDart R.medialTorus)
    (n : Nat) (w z : Int × Int) :
    let pairing := fkRectConfigurationToMedialPairing R
      (fkRectConfigurationOfEdges R F)
    let c := fkRectRefinedBoundaryCanonicalCenter R d
    let L := fkRectSquareCoverSide (fkRectRefinedCoverTorus R)
    let U : Int × Int :=
      (4 * (fkRectSquareDeckTranslation R w).1,
        4 * (fkRectSquareDeckTranslation R w).2)
    let V : Int × Int :=
      (4 * (fkRectSquareDeckTranslation R z).1,
        4 * (fkRectSquareDeckTranslation R z).2)
    fkRectRefinedRawInteraction
        ((fkRectRepeatTranslatedDartPath
          (fkRectRefinedBoundaryDarts pairing d c n) U L).map
            (fkRectIntegralSquareDartMod L))
        ((fkRectRepeatTranslatedDartPath
          (fkRectIntegralSquareDartListReverse
            (fkRectRefinedPrimalEdgeDarts R e)) V L).map
            (fkRectIntegralSquareDartMod L)) = 0 := by
  classical
  dsimp only
  let pairing := fkRectConfigurationToMedialPairing R
    (fkRectConfigurationOfEdges R F)
  let c := fkRectRefinedBoundaryCanonicalCenter R d
  let L := fkRectSquareCoverSide (fkRectRefinedCoverTorus R)
  let U : Int × Int :=
    (4 * (fkRectSquareDeckTranslation R w).1,
      4 * (fkRectSquareDeckTranslation R w).2)
  let V : Int × Int :=
    (4 * (fkRectSquareDeckTranslation R z).1,
      4 * (fkRectSquareDeckTranslation R z).2)
  change fkRectRefinedRawInteraction
      ((fkRectRepeatTranslatedDartPath
        (fkRectRefinedBoundaryDarts pairing d c n) U L).map
          (fkRectIntegralSquareDartMod L))
      ((fkRectRepeatTranslatedDartPath
        (fkRectIntegralSquareDartListReverse
          (fkRectRefinedPrimalEdgeDarts R e)) V L).map
          (fkRectIntegralSquareDartMod L)) = 0
  rw [fkRectRefinedRawInteraction_repeatTranslated_both]
  apply Finset.sum_eq_zero
  intro i hi
  apply Finset.sum_eq_zero
  intro j hj
  let u : Int × Int :=
    ((i : Int) * w.1 - (j : Int) * z.1,
      (i : Int) * w.2 - (j : Int) * z.2)
  apply fkRectRefinedRawInteraction_translated_boundary_openEdgeReverse_eq_zero
    R F e heF d n (fkRectNatScale i U) (fkRectNatScale j V) u
  apply Prod.ext <;>
    simp [u, U, V, fkRectNatScale, fkRectSquareDeckTranslation] <;> ring

end

end StatMech.FrontierD
