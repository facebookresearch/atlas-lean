/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/




import Code.FrontierD.FKRectRefinedTranslatedLocalSupport
import Code.FrontierD.FKMedialBoundaryPermutation










open Finset

namespace StatMech.FrontierD

noncomputable section

private theorem fkRectRefinedLocalDarts_map_eq_of_center_mod_eq
    {L : Nat} (pairing : Bool) (c z : Int × Int) (side : FKMedialSide)
    (h : (((c.1 : Int) : ZMod L), ((c.2 : Int) : ZMod L)) =
      (((z.1 : Int) : ZMod L), ((z.2 : Int) : ZMod L))) :
    (fkRectRefinedLocalDarts pairing c side).map
        (fkRectIntegralSquareDartMod L) =
      (fkRectRefinedLocalDarts pairing z side).map
        (fkRectIntegralSquareDartMod L) := by
  have hx : ((c.1 : Int) : ZMod L) = ((z.1 : Int) : ZMod L) :=
    congrArg Prod.fst h
  have hy : ((c.2 : Int) : ZMod L) = ((z.2 : Int) : ZMod L) :=
    congrArg Prod.snd h
  have hxadd (k : Int) : (((c.1 + k : Int) : ZMod L)) =
      (((z.1 + k : Int) : ZMod L)) := by
    push_cast
    exact congrArg (fun a : ZMod L => a + (k : ZMod L)) hx
  have hyadd (k : Int) : (((c.2 + k : Int) : ZMod L)) =
      (((z.2 + k : Int) : ZMod L)) := by
    push_cast
    exact congrArg (fun a : ZMod L => a + (k : ZMod L)) hy
  cases pairing <;> cases side <;>
    simp [fkRectRefinedLocalDarts, fkRectRefinedDartPoint,
      fkRectRefinedSideOffset, fkRectIntegralSquareDartMod,
      Prod.ext_iff, hx, hy, hxadd, hyadd]

private theorem fkRectRefinedPrimalCenterline_map_eq_of_center_mod_eq
    {L : Nat} (pairing : Bool) (c z : Int × Int)
    (h : (((c.1 : Int) : ZMod L), ((c.2 : Int) : ZMod L)) =
      (((z.1 : Int) : ZMod L), ((z.2 : Int) : ZMod L))) :
    (fkRectRefinedPrimalCenterlineDarts pairing c).map
        (fkRectIntegralSquareDartMod L) =
      (fkRectRefinedPrimalCenterlineDarts pairing z).map
        (fkRectIntegralSquareDartMod L) := by
  have hx : ((c.1 : Int) : ZMod L) = ((z.1 : Int) : ZMod L) :=
    congrArg Prod.fst h
  have hy : ((c.2 : Int) : ZMod L) = ((z.2 : Int) : ZMod L) :=
    congrArg Prod.snd h
  have hxadd (k : Int) : (((c.1 + k : Int) : ZMod L)) =
      (((z.1 + k : Int) : ZMod L)) := by
    push_cast
    exact congrArg (fun a : ZMod L => a + (k : ZMod L)) hx
  have hyadd (k : Int) : (((c.2 + k : Int) : ZMod L)) =
      (((z.2 + k : Int) : ZMod L)) := by
    push_cast
    exact congrArg (fun a : ZMod L => a + (k : ZMod L)) hy
  cases pairing <;>
    simp [fkRectRefinedPrimalCenterlineDarts,
      fkRectIntegralSquareDartMod, Prod.ext_iff, hx, hy, hxadd, hyadd]



theorem fkMedialDart_eq_west_or_east_of_vertex_eq_of_checkerColor
    {T : EvenTorus} (d : FKMedialDart T) (v : T.Vertex)
    (hvertex : d.1 = v)
    (hcolor : fkMedialCheckerColor d =
      fkMedialCheckerColor (fkMedialWestDart v)) :
    d = fkMedialWestDart v ∨ d = fkMedialEastDart v := by
  rcases d with ⟨w, side⟩
  change w = v at hvertex
  subst w
  cases side <;>
    simp [fkMedialWestDart, fkMedialEastDart,
      fkMedialCheckerColor, fkMedialSideVertical] at hcolor ⊢



theorem fkRectConfigurationOfEdges_pairing_eq_closed_or_open
    (R : FKRectTorus) (F : Finset R.EdgeIndex)
    (d : FKMedialDart R.medialTorus) :
    let f := fkRectTorusMedialEdgeEquiv R d.1
    fkRectConfigurationToMedialPairing R
        (fkRectConfigurationOfEdges R F) d.1 =
      if f ∈ F then !fkRectClosedPairingAtEdge f
      else fkRectClosedPairingAtEdge f := by
  classical
  simp [fkRectConfigurationToMedialPairing_apply,
    fkRectConfigurationOfEdges]
  split <;> rename_i h <;> simp [h]



theorem fkRectRefinedBondCenter_exists_deck
    (R : FKRectTorus)
    (pairing : FKMedialLoopPairing R.medialTorus)
    (d : FKMedialDart R.medialTorus) (c : Int × Int) (u : Int × Int)
    (hcenter : c =
      ((fkRectRefinedBoundaryCanonicalCenter R d).1 +
          4 * (fkRectSquareDeckTranslation R u).1,
        (fkRectRefinedBoundaryCanonicalCenter R d).2 +
          4 * (fkRectSquareDeckTranslation R u).2)) :
    ∃ v : Int × Int,
      fkRectRefinedBondCenter c (fkMedialLocalMate pairing d).2 =
        ((fkRectRefinedBoundaryCanonicalCenter R
            (fkMedialBoundaryStep pairing d)).1 +
              4 * (fkRectSquareDeckTranslation R v).1,
          (fkRectRefinedBoundaryCanonicalCenter R
            (fkMedialBoundaryStep pairing d)).2 +
              4 * (fkRectSquareDeckTranslation R v).2) := by
  obtain ⟨v, hv⟩ :=
    fkRectRefinedBoundaryCenterAfter_exists_deck R pairing d 1
  simp only [fkRectRefinedBoundaryCenterAfter,
    Function.iterate_succ_apply, Function.iterate_zero_apply] at hv
  refine ⟨u + v, ?_⟩
  rw [hcenter]
  have hx := congrArg Prod.fst hv
  have hy := congrArg Prod.snd hv
  apply Prod.ext
  · simp [fkRectRefinedBondCenter, fkRectSquareDeckTranslation] at hx ⊢
    linear_combination hx
  · simp [fkRectRefinedBondCenter, fkRectSquareDeckTranslation] at hy ⊢
    linear_combination hy



def fkRectRefinedBoundaryMatchedVisitTrace
    (R : FKRectTorus) (pairing : FKMedialLoopPairing R.medialTorus)
    (e : R.EdgeIndex) :
    FKMedialDart R.medialTorus -> (Int × Int) -> Nat -> Int
  | _, _, 0 => 0
  | d, c, n + 1 =>
      (if fkRectTorusMedialEdgeEquiv R d.1 = e ∧
          let L := fkRectSquareCoverSide (fkRectRefinedCoverTorus R)
          (((c.1 : Int) : ZMod L), ((c.2 : Int) : ZMod L)) =
            ((((fkRectRefinedPrimalEdgeCenter R e).1 : Int) : ZMod L),
              (((fkRectRefinedPrimalEdgeCenter R e).2 : Int) : ZMod L))
        then if d = fkMedialWestDart (fkRectMedialVertexOfEdge R e)
          then 1 else -1
        else 0) +
      fkRectRefinedBoundaryMatchedVisitTrace R pairing e
        (fkMedialBoundaryStep pairing d)
        (fkRectRefinedBondCenter c (fkMedialLocalMate pairing d).2) n





theorem fkRectRefinedBoundaryLocalInteraction_eq_signedVisit_of_color
    (R : FKRectTorus) (F : Finset R.EdgeIndex) (e : R.EdgeIndex)
    (heF : e ∉ F)
    (d : FKMedialDart R.medialTorus) (c : Int × Int) (u : Int × Int)
    (hcolor : fkMedialCheckerColor d =
      fkMedialCheckerColor
        (fkMedialWestDart (fkRectMedialVertexOfEdge R e)))
    (hcenter : c =
      ((fkRectRefinedBoundaryCanonicalCenter R d).1 +
          4 * (fkRectSquareDeckTranslation R u).1,
        (fkRectRefinedBoundaryCanonicalCenter R d).2 +
          4 * (fkRectSquareDeckTranslation R u).2)) :
    let pairing := fkRectConfigurationToMedialPairing R
      (fkRectConfigurationOfEdges R F)
    let L := fkRectSquareCoverSide (fkRectRefinedCoverTorus R)
    fkRectRefinedBoundaryLocalInteraction R pairing d c e =
      if fkRectTorusMedialEdgeEquiv R d.1 = e ∧
          (((c.1 : Int) : ZMod L), ((c.2 : Int) : ZMod L)) =
            ((((fkRectRefinedPrimalEdgeCenter R e).1 : Int) : ZMod L),
              (((fkRectRefinedPrimalEdgeCenter R e).2 : Int) : ZMod L))
      then if d = fkMedialWestDart (fkRectMedialVertexOfEdge R e)
        then 1 else -1
      else 0 := by
  classical
  dsimp only
  let pairing := fkRectConfigurationToMedialPairing R
    (fkRectConfigurationOfEdges R F)
  let f := fkRectTorusMedialEdgeEquiv R d.1
  let L := fkRectSquareCoverSide (fkRectRefinedCoverTorus R)
  have hpair := fkRectConfigurationOfEdges_pairing_eq_closed_or_open R F d
  dsimp only at hpair
  change pairing d.1 = (if f ∈ F then !fkRectClosedPairingAtEdge f
    else fkRectClosedPairingAtEdge f) at hpair
  by_cases hfe : f = e
  · have hfe' : fkRectTorusMedialEdgeEquiv R d.1 = e := hfe
    have hdv : d.1 = fkRectMedialVertexOfEdge R e := by
      apply (fkRectTorusMedialEdgeEquiv R).injective
      simpa using hfe'
    have hside :=
      fkMedialDart_eq_west_or_east_of_vertex_eq_of_checkerColor
        d (fkRectMedialVertexOfEdge R e) hdv hcolor
    have hepair : pairing d.1 = fkRectClosedPairingAtEdge e := by
      rw [hpair, if_neg]
      · simpa [hfe]
      · simpa [hfe] using heF
    have hcanonical : fkRectRefinedBoundaryCanonicalCenter R d =
        fkRectRefinedPrimalEdgeCenter R e := by
      unfold fkRectRefinedBoundaryCanonicalCenter
      rw [hfe']
    by_cases hmod :
        (((c.1 : Int) : ZMod L), ((c.2 : Int) : ZMod L)) =
          ((((fkRectRefinedPrimalEdgeCenter R e).1 : Int) : ZMod L),
            (((fkRectRefinedPrimalEdgeCenter R e).2 : Int) : ZMod L))
    · rw [if_pos ⟨hfe', hmod⟩]
      unfold fkRectRefinedBoundaryLocalInteraction
      dsimp only
      have hepair' : fkRectConfigurationToMedialPairing R
          (fkRectConfigurationOfEdges R F) d.1 =
          fkRectClosedPairingAtEdge e := by
        simpa [pairing] using hepair
      rw [hepair', fkRectRefinedPrimalEdgeDarts_eq_centerline]
      rw [fkRectRefinedLocalDarts_map_eq_of_center_mod_eq
        (fkRectClosedPairingAtEdge e) c
        (fkRectRefinedPrimalEdgeCenter R e) d.2 hmod]
      rcases hside with rfl | rfl
      · simp only [if_true]
        exact fkRectRefinedLocalDarts_west_interaction _ _
      · rw [if_neg]
        · exact fkRectRefinedLocalDarts_east_interaction _ _
        · intro h
          cases h
    · rw [if_neg (fun h => hmod h.2)]
      apply fkRectRefinedBoundaryLocalInteraction_eq_zero_of_endpointDisjoint
      intro p hp ht
      have hepair' : fkRectConfigurationToMedialPairing R
          (fkRectConfigurationOfEdges R F) d.1 =
          fkRectClosedPairingAtEdge e := by
        simpa [pairing] using hepair
      rw [hepair'] at hp
      rw [fkRectRefinedPrimalEdgeDarts_eq_centerline] at ht
      have hnormal : FKRectRefinedEdgeCenterNormal
          (fkRectClosedPairingAtEdge e) c := by
        rw [hcenter, hcanonical]
        exact (fkRectRefinedPrimalEdgeCenter_normal R e).add_four
          (fkRectSquareDeckTranslation R u).1
          (fkRectSquareDeckTranslation R u).2
      exact hmod <|
        fkRectRefinedCenter_mod_eq_of_closed_local_centerline_commonPoint
          R (fkRectClosedPairingAtEdge e) (fkRectClosedPairingAtEdge e)
          c (fkRectRefinedPrimalEdgeCenter R e) d.2 hnormal
          (fkRectRefinedPrimalEdgeCenter_normal R e) p hp ht
  · change fkRectTorusMedialEdgeEquiv R d.1 ≠ e at hfe
    rw [if_neg (fun h => hfe h.1)]
    by_cases hfF : f ∈ F
    · have hopen : pairing d.1 = !fkRectClosedPairingAtEdge f := by
        simpa [hfF] using hpair
      have hnormal : FKRectRefinedEdgeCenterNormal
          (fkRectClosedPairingAtEdge f) c := by
        rw [hcenter]
        change FKRectRefinedEdgeCenterNormal
          (fkRectClosedPairingAtEdge f)
          ((fkRectRefinedPrimalEdgeCenter R f).1 +
              4 * (fkRectSquareDeckTranslation R u).1,
            (fkRectRefinedPrimalEdgeCenter R f).2 +
              4 * (fkRectSquareDeckTranslation R u).2)
        exact (fkRectRefinedPrimalEdgeCenter_normal R f).add_four
          (fkRectSquareDeckTranslation R u).1
          (fkRectSquareDeckTranslation R u).2
      exact fkRectRefinedBoundaryLocalInteraction_eq_zero_of_open
        R pairing d c e hopen hnormal
    · have hclosed : pairing d.1 = fkRectClosedPairingAtEdge f := by
        simpa [hfF] using hpair
      apply fkRectRefinedBoundaryLocalInteraction_eq_zero_of_closed_ne
        R pairing d c e f u rfl hclosed
      · simpa [fkRectRefinedBoundaryCanonicalCenter, f] using hcenter
      · exact hfe




theorem fkRectRefinedBoundaryLocalInteraction_eq_zero_of_target_mem
    (R : FKRectTorus) (F : Finset R.EdgeIndex) (e : R.EdgeIndex)
    (heF : e ∈ F)
    (d : FKMedialDart R.medialTorus) (c : Int × Int) (u : Int × Int)
    (hcenter : c =
      ((fkRectRefinedBoundaryCanonicalCenter R d).1 +
          4 * (fkRectSquareDeckTranslation R u).1,
        (fkRectRefinedBoundaryCanonicalCenter R d).2 +
          4 * (fkRectSquareDeckTranslation R u).2)) :
    let pairing := fkRectConfigurationToMedialPairing R
      (fkRectConfigurationOfEdges R F)
    fkRectRefinedBoundaryLocalInteraction R pairing d c e = 0 := by
  dsimp only
  let pairing := fkRectConfigurationToMedialPairing R
    (fkRectConfigurationOfEdges R F)
  let f := fkRectTorusMedialEdgeEquiv R d.1
  have hpair := fkRectConfigurationOfEdges_pairing_eq_closed_or_open R F d
  dsimp only at hpair
  change pairing d.1 = (if f ∈ F then !fkRectClosedPairingAtEdge f
    else fkRectClosedPairingAtEdge f) at hpair
  have hnormal : FKRectRefinedEdgeCenterNormal
      (fkRectClosedPairingAtEdge f) c := by
    rw [hcenter]
    change FKRectRefinedEdgeCenterNormal (fkRectClosedPairingAtEdge f)
      ((fkRectRefinedPrimalEdgeCenter R f).1 +
          4 * (fkRectSquareDeckTranslation R u).1,
        (fkRectRefinedPrimalEdgeCenter R f).2 +
          4 * (fkRectSquareDeckTranslation R u).2)
    exact (fkRectRefinedPrimalEdgeCenter_normal R f).add_four
      (fkRectSquareDeckTranslation R u).1
      (fkRectSquareDeckTranslation R u).2
  by_cases hfe : f = e
  · have hfF : f ∈ F := hfe ▸ heF
    have hopen : pairing d.1 = !fkRectClosedPairingAtEdge f := by
      simpa [hfF] using hpair
    exact fkRectRefinedBoundaryLocalInteraction_eq_zero_of_open
      R pairing d c e (by simpa [f] using hopen) (by simpa [f] using hnormal)
  · by_cases hfF : f ∈ F
    · have hopen : pairing d.1 = !fkRectClosedPairingAtEdge f := by
        simpa [hfF] using hpair
      exact fkRectRefinedBoundaryLocalInteraction_eq_zero_of_open
        R pairing d c e hopen hnormal
    · have hclosed : pairing d.1 = fkRectClosedPairingAtEdge f := by
        simpa [hfF] using hpair
      apply fkRectRefinedBoundaryLocalInteraction_eq_zero_of_closed_ne
        R pairing d c e f u rfl hclosed
      · simpa [fkRectRefinedBoundaryCanonicalCenter, f] using hcenter
      · exact hfe



theorem fkRectRefinedBoundaryInteractionTrace_eq_zero_of_target_mem
    (R : FKRectTorus) (F : Finset R.EdgeIndex) (e : R.EdgeIndex)
    (heF : e ∈ F)
    (d : FKMedialDart R.medialTorus) (c : Int × Int) (u : Int × Int)
    (n : Nat)
    (hcenter : c =
      ((fkRectRefinedBoundaryCanonicalCenter R d).1 +
          4 * (fkRectSquareDeckTranslation R u).1,
        (fkRectRefinedBoundaryCanonicalCenter R d).2 +
          4 * (fkRectSquareDeckTranslation R u).2)) :
    let pairing := fkRectConfigurationToMedialPairing R
      (fkRectConfigurationOfEdges R F)
    fkRectRefinedBoundaryInteractionTrace R pairing e d c n = 0 := by
  dsimp only
  let pairing := fkRectConfigurationToMedialPairing R
    (fkRectConfigurationOfEdges R F)
  change fkRectRefinedBoundaryInteractionTrace R pairing e d c n = 0
  induction n generalizing d c u with
  | zero => simp [fkRectRefinedBoundaryInteractionTrace]
  | succ n ih =>
      change fkRectRefinedBoundaryLocalInteraction R pairing d c e +
        fkRectRefinedBoundaryInteractionTrace R pairing e
          (fkMedialBoundaryStep pairing d)
          (fkRectRefinedBondCenter c (fkMedialLocalMate pairing d).2) n = 0
      have hlocal := fkRectRefinedBoundaryLocalInteraction_eq_zero_of_target_mem
        R F e heF d c u hcenter
      dsimp only at hlocal
      change fkRectRefinedBoundaryLocalInteraction R pairing d c e = 0 at hlocal
      rw [hlocal, zero_add]
      obtain ⟨v, hv⟩ := fkRectRefinedBondCenter_exists_deck
        R pairing d c u hcenter
      exact ih _ _ v hv



theorem fkRectRefinedBoundaryInteractionTrace_eq_matchedVisits
    (R : FKRectTorus) (F : Finset R.EdgeIndex) (e : R.EdgeIndex)
    (heF : e ∉ F)
    (d : FKMedialDart R.medialTorus) (c : Int × Int) (u : Int × Int)
    (n : Nat)
    (hcolor : fkMedialCheckerColor d =
      fkMedialCheckerColor
        (fkMedialWestDart (fkRectMedialVertexOfEdge R e)))
    (hcenter : c =
      ((fkRectRefinedBoundaryCanonicalCenter R d).1 +
          4 * (fkRectSquareDeckTranslation R u).1,
        (fkRectRefinedBoundaryCanonicalCenter R d).2 +
          4 * (fkRectSquareDeckTranslation R u).2)) :
    let pairing := fkRectConfigurationToMedialPairing R
      (fkRectConfigurationOfEdges R F)
    fkRectRefinedBoundaryInteractionTrace R pairing e d c n =
      fkRectRefinedBoundaryMatchedVisitTrace R pairing e d c n := by
  dsimp only
  let pairing := fkRectConfigurationToMedialPairing R
    (fkRectConfigurationOfEdges R F)
  change fkRectRefinedBoundaryInteractionTrace R pairing e d c n =
    fkRectRefinedBoundaryMatchedVisitTrace R pairing e d c n
  induction n generalizing d c u with
  | zero =>
      simp [fkRectRefinedBoundaryInteractionTrace,
        fkRectRefinedBoundaryMatchedVisitTrace]
  | succ n ih =>
      change fkRectRefinedBoundaryLocalInteraction R pairing d c e +
          fkRectRefinedBoundaryInteractionTrace R pairing e
            (fkMedialBoundaryStep pairing d)
            (fkRectRefinedBondCenter c (fkMedialLocalMate pairing d).2) n =
        (if fkRectTorusMedialEdgeEquiv R d.1 = e ∧
            let L := fkRectSquareCoverSide (fkRectRefinedCoverTorus R)
            (((c.1 : Int) : ZMod L), ((c.2 : Int) : ZMod L)) =
              ((((fkRectRefinedPrimalEdgeCenter R e).1 : Int) : ZMod L),
                (((fkRectRefinedPrimalEdgeCenter R e).2 : Int) : ZMod L))
          then if d = fkMedialWestDart (fkRectMedialVertexOfEdge R e)
            then 1 else -1
          else 0) +
        fkRectRefinedBoundaryMatchedVisitTrace R pairing e
          (fkMedialBoundaryStep pairing d)
          (fkRectRefinedBondCenter c (fkMedialLocalMate pairing d).2) n
      have hlocal :=
        fkRectRefinedBoundaryLocalInteraction_eq_signedVisit_of_color
          R F e heF d c u hcolor hcenter
      dsimp only at hlocal
      change fkRectRefinedBoundaryLocalInteraction R pairing d c e = _ at hlocal
      rw [hlocal]
      obtain ⟨v, hv⟩ := fkRectRefinedBondCenter_exists_deck
        R pairing d c u hcenter
      rw [ih (fkMedialBoundaryStep pairing d)
        (fkRectRefinedBondCenter c (fkMedialLocalMate pairing d).2) v
        (by rw [fkMedialCheckerColor_boundaryStep]; exact hcolor) hv]

end

end StatMech.FrontierD
