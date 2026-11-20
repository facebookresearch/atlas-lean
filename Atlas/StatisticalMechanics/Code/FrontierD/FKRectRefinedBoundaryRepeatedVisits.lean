/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/




import Code.FrontierD.FKRectRefinedBoundaryVisitSupport
import Code.FrontierD.FKRectRefinedRepeatedInteraction








namespace StatMech.FrontierD

noncomputable section


theorem fkRectRefinedBondCenter_add_center
    (c t : Int × Int) (side : FKMedialSide) :
    fkRectRefinedBondCenter (c.1 + t.1, c.2 + t.2) side =
      ((fkRectRefinedBondCenter c side).1 + t.1,
        (fkRectRefinedBondCenter c side).2 + t.2) := by
  apply Prod.ext <;> simp [fkRectRefinedBondCenter] <;> ring



theorem fkRectRefinedBoundaryDarts_add_center
    {T : EvenTorus} (pairing : FKMedialLoopPairing T)
    (d : FKMedialDart T) (c t : Int × Int) (n : Nat) :
    fkRectRefinedBoundaryDarts pairing d
        (c.1 + t.1, c.2 + t.2) n =
      (fkRectRefinedBoundaryDarts pairing d c n).map
        (fkRectIntegralSquareDartTranslate t) := by
  induction n generalizing d c with
  | zero => simp [fkRectRefinedBoundaryDarts]
  | succ n ih =>
      simp only [fkRectRefinedBoundaryDarts, List.map_append,
        fkRectRefinedLocalDarts_add_center]
      rw [fkRectRefinedBondCenter_add_center, ih]

private theorem fkRectTranslatedMap_comp_sub_add
    (l : List FKRectIntegralSquareDart) (a b : Int × Int) :
    ((l.map (fkRectIntegralSquareDartTranslate
          (a.1 - b.1, a.2 - b.2))).map
        (fkRectIntegralSquareDartTranslate b)) =
      l.map (fkRectIntegralSquareDartTranslate a) := by
  simp only [List.map_map]
  apply List.map_congr_left
  intro d hd
  simp only [Function.comp_apply]
  rw [fkRectIntegralSquareDartTranslate_comp]
  congr 2 <;> simp





theorem fkRectRefinedRawInteraction_translated_boundary_eq_matchedVisits
    (R : FKRectTorus) (F : Finset R.EdgeIndex) (e : R.EdgeIndex)
    (heF : e ∉ F)
    (d : FKMedialDart R.medialTorus) (n : Nat)
    (a b u : Int × Int)
    (hcolor : fkMedialCheckerColor d =
      fkMedialCheckerColor
        (fkMedialWestDart (fkRectMedialVertexOfEdge R e)))
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
        (((fkRectRefinedPrimalEdgeDarts R e).map
          (fkRectIntegralSquareDartTranslate b)).map
            (fkRectIntegralSquareDartMod L)) =
      fkRectRefinedBoundaryMatchedVisitTrace R pairing e d
        (c.1 + (a.1 - b.1), c.2 + (a.2 - b.2)) n := by
  dsimp only
  let pairing := fkRectConfigurationToMedialPairing R
    (fkRectConfigurationOfEdges R F)
  let c := fkRectRefinedBoundaryCanonicalCenter R d
  let L := fkRectSquareCoverSide (fkRectRefinedCoverTorus R)
  let t : Int × Int := (a.1 - b.1, a.2 - b.2)
  have hinv := fkRectRefinedRawInteraction_integralTranslate
    (L := L) b
    ((fkRectRefinedBoundaryDarts pairing d c n).map
      (fkRectIntegralSquareDartTranslate t))
    (fkRectRefinedPrimalEdgeDarts R e)
  rw [fkRectTranslatedMap_comp_sub_add] at hinv
  have hboundary := fkRectRefinedBoundaryDarts_add_center pairing d c t n
  rw [hinv]
  rw [← hboundary]
  rw [fkRectRefinedRawInteraction_boundaryDarts]
  apply fkRectRefinedBoundaryInteractionTrace_eq_matchedVisits
    R F e heF d (c.1 + t.1, c.2 + t.2) u n hcolor
  dsimp [c, t]
  have hx := congrArg Prod.fst hrelative
  have hy := congrArg Prod.snd hrelative
  apply Prod.ext <;> simp at hx hy ⊢ <;> linarith




theorem fkRectRefinedRawInteraction_repeated_boundary_edge_eq_sum_matchedVisits
    (R : FKRectTorus) (F : Finset R.EdgeIndex) (e : R.EdgeIndex)
    (heF : e ∉ F) (w z : Int × Int) :
    let pairing := fkRectConfigurationToMedialPairing R
      (fkRectConfigurationOfEdges R F)
    let d := fkMedialWestDart (fkRectMedialVertexOfEdge R e)
    let c := fkRectRefinedBoundaryCanonicalCenter R d
    let n := orderOf (fkMedialBoundaryStep pairing)
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
          (fkRectRefinedPrimalEdgeDarts R e) V L).map
            (fkRectIntegralSquareDartMod L)) =
      ∑ i ∈ Finset.range L, ∑ j ∈ Finset.range L,
        fkRectRefinedBoundaryMatchedVisitTrace R pairing e d
          (c.1 + ((fkRectNatScale i U).1 - (fkRectNatScale j V).1),
            c.2 + ((fkRectNatScale i U).2 - (fkRectNatScale j V).2)) n := by
  classical
  dsimp only
  let pairing := fkRectConfigurationToMedialPairing R
    (fkRectConfigurationOfEdges R F)
  let d := fkMedialWestDart (fkRectMedialVertexOfEdge R e)
  let c := fkRectRefinedBoundaryCanonicalCenter R d
  let n := orderOf (fkMedialBoundaryStep pairing)
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
        (fkRectRefinedPrimalEdgeDarts R e) V L).map
          (fkRectIntegralSquareDartMod L)) = _
  rw [fkRectRefinedRawInteraction_repeatTranslated_both]
  apply Finset.sum_congr rfl
  intro i hi
  apply Finset.sum_congr rfl
  intro j hj
  let u : Int × Int :=
    ((i : Int) * w.1 - (j : Int) * z.1,
      (i : Int) * w.2 - (j : Int) * z.2)
  apply fkRectRefinedRawInteraction_translated_boundary_eq_matchedVisits
    R F e heF d n (fkRectNatScale i U) (fkRectNatScale j V) u
  · rfl
  · apply Prod.ext <;>
      simp [u, U, V, fkRectNatScale, fkRectSquareDeckTranslation] <;> ring



theorem fkRectRefinedRawInteraction_translated_boundary_openEdge_eq_zero
    (R : FKRectTorus) (F : Finset R.EdgeIndex) (e : R.EdgeIndex)
    (heF : e ∈ F)
    (d : FKMedialDart R.medialTorus) (n : Nat)
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
        (((fkRectRefinedPrimalEdgeDarts R e).map
          (fkRectIntegralSquareDartTranslate b)).map
            (fkRectIntegralSquareDartMod L)) = 0 := by
  dsimp only
  let pairing := fkRectConfigurationToMedialPairing R
    (fkRectConfigurationOfEdges R F)
  let c := fkRectRefinedBoundaryCanonicalCenter R d
  let L := fkRectSquareCoverSide (fkRectRefinedCoverTorus R)
  let t : Int × Int := (a.1 - b.1, a.2 - b.2)
  have hinv := fkRectRefinedRawInteraction_integralTranslate
    (L := L) b
    ((fkRectRefinedBoundaryDarts pairing d c n).map
      (fkRectIntegralSquareDartTranslate t))
    (fkRectRefinedPrimalEdgeDarts R e)
  rw [fkRectTranslatedMap_comp_sub_add] at hinv
  have hboundary := fkRectRefinedBoundaryDarts_add_center pairing d c t n
  rw [hinv, ← hboundary]
  rw [fkRectRefinedRawInteraction_boundaryDarts]
  apply fkRectRefinedBoundaryInteractionTrace_eq_zero_of_target_mem
    R F e heF d (c.1 + t.1, c.2 + t.2) u n
  dsimp [c, t]
  have hx := congrArg Prod.fst hrelative
  have hy := congrArg Prod.snd hrelative
  apply Prod.ext <;> simp at hx hy ⊢ <;> linarith



theorem fkRectRefinedRawInteraction_repeated_boundary_openEdge_eq_zero
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
          (fkRectRefinedPrimalEdgeDarts R e) V L).map
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
        (fkRectRefinedPrimalEdgeDarts R e) V L).map
          (fkRectIntegralSquareDartMod L)) = 0
  rw [fkRectRefinedRawInteraction_repeatTranslated_both]
  apply Finset.sum_eq_zero
  intro i hi
  apply Finset.sum_eq_zero
  intro j hj
  let u : Int × Int :=
    ((i : Int) * w.1 - (j : Int) * z.1,
      (i : Int) * w.2 - (j : Int) * z.2)
  apply fkRectRefinedRawInteraction_translated_boundary_openEdge_eq_zero
    R F e heF d n (fkRectNatScale i U) (fkRectNatScale j V) u
  apply Prod.ext <;>
    simp [u, U, V, fkRectNatScale, fkRectSquareDeckTranslation] <;> ring




theorem fkRectRefinedBoundaryMatchedVisitTrace_nonneg_of_avoid_east
    (R : FKRectTorus) (pairing : FKMedialLoopPairing R.medialTorus)
    (e : R.EdgeIndex) (d : FKMedialDart R.medialTorus)
    (c : Int × Int) (n : Nat)
    (hcolor : fkMedialCheckerColor d =
      fkMedialCheckerColor
        (fkMedialWestDart (fkRectMedialVertexOfEdge R e)))
    (havoid : ∀ k : Nat,
      (fkMedialBoundaryStep pairing)^[k] d ≠
        fkMedialEastDart (fkRectMedialVertexOfEdge R e)) :
    0 ≤ fkRectRefinedBoundaryMatchedVisitTrace R pairing e d c n := by
  induction n generalizing d c with
  | zero => simp [fkRectRefinedBoundaryMatchedVisitTrace]
  | succ n ih =>
      rw [fkRectRefinedBoundaryMatchedVisitTrace]
      have hdne : d ≠ fkMedialEastDart
          (fkRectMedialVertexOfEdge R e) := by
        simpa using havoid 0
      have htailAvoid : ∀ k : Nat,
          (fkMedialBoundaryStep pairing)^[k]
              (fkMedialBoundaryStep pairing d) ≠
            fkMedialEastDart (fkRectMedialVertexOfEdge R e) := by
        intro k
        simpa only [Function.iterate_succ_apply] using havoid (k + 1)
      have htailColor : fkMedialCheckerColor
          (fkMedialBoundaryStep pairing d) =
          fkMedialCheckerColor
            (fkMedialWestDart (fkRectMedialVertexOfEdge R e)) := by
        rw [fkMedialCheckerColor_boundaryStep]
        exact hcolor
      have htail := ih (fkMedialBoundaryStep pairing d)
        (fkRectRefinedBondCenter c (fkMedialLocalMate pairing d).2)
        htailColor htailAvoid
      split
      · rename_i hmatch
        have hdv : d.1 = fkRectMedialVertexOfEdge R e := by
          apply (fkRectTorusMedialEdgeEquiv R).injective
          simpa using hmatch.1
        rcases fkMedialDart_eq_west_or_east_of_vertex_eq_of_checkerColor
            d (fkRectMedialVertexOfEdge R e) hdv hcolor with hwest | heast
        · rw [if_pos hwest]
          exact add_nonneg (by norm_num) htail
        · exact False.elim (hdne heast)
      · exact add_nonneg (by norm_num) htail



theorem fkRectRefinedBoundaryMatchedVisitTrace_eq_zero_of_avoid_west_east
    (R : FKRectTorus) (pairing : FKMedialLoopPairing R.medialTorus)
    (e : R.EdgeIndex) (d : FKMedialDart R.medialTorus)
    (c : Int × Int) (n : Nat)
    (hcolor : fkMedialCheckerColor d =
      fkMedialCheckerColor
        (fkMedialWestDart (fkRectMedialVertexOfEdge R e)))
    (hwest : ∀ k : Nat,
      (fkMedialBoundaryStep pairing)^[k] d ≠
        fkMedialWestDart (fkRectMedialVertexOfEdge R e))
    (heast : ∀ k : Nat,
      (fkMedialBoundaryStep pairing)^[k] d ≠
        fkMedialEastDart (fkRectMedialVertexOfEdge R e)) :
    fkRectRefinedBoundaryMatchedVisitTrace R pairing e d c n = 0 := by
  induction n generalizing d c with
  | zero => simp [fkRectRefinedBoundaryMatchedVisitTrace]
  | succ n ih =>
      rw [fkRectRefinedBoundaryMatchedVisitTrace]
      have htailWest : ∀ k : Nat,
          (fkMedialBoundaryStep pairing)^[k]
              (fkMedialBoundaryStep pairing d) ≠
            fkMedialWestDart (fkRectMedialVertexOfEdge R e) := by
        intro k
        simpa only [Function.iterate_succ_apply] using hwest (k + 1)
      have htailEast : ∀ k : Nat,
          (fkMedialBoundaryStep pairing)^[k]
              (fkMedialBoundaryStep pairing d) ≠
            fkMedialEastDart (fkRectMedialVertexOfEdge R e) := by
        intro k
        simpa only [Function.iterate_succ_apply] using heast (k + 1)
      have htailColor : fkMedialCheckerColor
          (fkMedialBoundaryStep pairing d) =
          fkMedialCheckerColor
            (fkMedialWestDart (fkRectMedialVertexOfEdge R e)) := by
        rw [fkMedialCheckerColor_boundaryStep]
        exact hcolor
      have htail := ih (fkMedialBoundaryStep pairing d)
        (fkRectRefinedBondCenter c (fkMedialLocalMate pairing d).2)
        htailColor htailWest htailEast
      split
      · rename_i hmatch
        have hdv : d.1 = fkRectMedialVertexOfEdge R e := by
          apply (fkRectTorusMedialEdgeEquiv R).injective
          simpa using hmatch.1
        rcases fkMedialDart_eq_west_or_east_of_vertex_eq_of_checkerColor
            d (fkRectMedialVertexOfEdge R e) hdv hcolor with hw | he
        · have hw0 := hwest 0
          simp only [Function.iterate_zero_apply] at hw0
          exact False.elim (hw0 hw)
        · have he0 := heast 0
          simp only [Function.iterate_zero_apply] at he0
          exact False.elim (he0 he)
      · exact (zero_add _).trans htail



theorem fkRectRefinedBoundaryMatchedVisitTrace_canonical_pos_of_avoid_east
    (R : FKRectTorus) (pairing : FKMedialLoopPairing R.medialTorus)
    (e : R.EdgeIndex) (n : Nat) (hn : 0 < n)
    (havoid : ∀ k : Nat,
      (fkMedialBoundaryStep pairing)^[k]
          (fkMedialWestDart (fkRectMedialVertexOfEdge R e)) ≠
        fkMedialEastDart (fkRectMedialVertexOfEdge R e)) :
    0 < fkRectRefinedBoundaryMatchedVisitTrace R pairing e
      (fkMedialWestDart (fkRectMedialVertexOfEdge R e))
      (fkRectRefinedBoundaryCanonicalCenter R
        (fkMedialWestDart (fkRectMedialVertexOfEdge R e))) n := by
  obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hn.ne'
  rw [fkRectRefinedBoundaryMatchedVisitTrace]
  have htailAvoid : ∀ k : Nat,
      (fkMedialBoundaryStep pairing)^[k]
          (fkMedialBoundaryStep pairing
            (fkMedialWestDart (fkRectMedialVertexOfEdge R e))) ≠
        fkMedialEastDart (fkRectMedialVertexOfEdge R e) := by
    intro k
    simpa only [Function.iterate_succ_apply] using havoid (k + 1)
  have htailColor : fkMedialCheckerColor
      (fkMedialBoundaryStep pairing
        (fkMedialWestDart (fkRectMedialVertexOfEdge R e))) =
      fkMedialCheckerColor
        (fkMedialWestDart (fkRectMedialVertexOfEdge R e)) := by
    rw [fkMedialCheckerColor_boundaryStep]
  have htail :=
    fkRectRefinedBoundaryMatchedVisitTrace_nonneg_of_avoid_east
      R pairing e
      (fkMedialBoundaryStep pairing
        (fkMedialWestDart (fkRectMedialVertexOfEdge R e)))
      (fkRectRefinedBondCenter
        (fkRectRefinedBoundaryCanonicalCenter R
          (fkMedialWestDart (fkRectMedialVertexOfEdge R e)))
        (fkMedialLocalMate pairing
          (fkMedialWestDart (fkRectMedialVertexOfEdge R e))).2)
      m htailColor htailAvoid
  have hedge : fkRectTorusMedialEdgeEquiv R
      (fkMedialWestDart (fkRectMedialVertexOfEdge R e)).1 = e := by
    simp [fkMedialWestDart]
  have hcenter :
      let c := fkRectRefinedBoundaryCanonicalCenter R
        (fkMedialWestDart (fkRectMedialVertexOfEdge R e))
      let L := fkRectSquareCoverSide (fkRectRefinedCoverTorus R)
      (((c.1 : Int) : ZMod L), ((c.2 : Int) : ZMod L)) =
        ((((fkRectRefinedPrimalEdgeCenter R e).1 : Int) : ZMod L),
          (((fkRectRefinedPrimalEdgeCenter R e).2 : Int) : ZMod L)) := by
    simp [fkRectRefinedBoundaryCanonicalCenter, hedge]
  rw [if_pos ⟨hedge, hcenter⟩, if_pos rfl]
  exact Int.add_pos_of_pos_of_nonneg (by norm_num) htail





theorem fkRectRefinedRawInteraction_repeated_boundary_edge_ne_zero_of_avoid_east
    (R : FKRectTorus) (F : Finset R.EdgeIndex) (e : R.EdgeIndex)
    (heF : e ∉ F) (w z : Int × Int)
    (havoid : ∀ k : Nat,
      let pairing := fkRectConfigurationToMedialPairing R
        (fkRectConfigurationOfEdges R F)
      (fkMedialBoundaryStep pairing)^[k]
          (fkMedialWestDart (fkRectMedialVertexOfEdge R e)) ≠
        fkMedialEastDart (fkRectMedialVertexOfEdge R e)) :
    let pairing := fkRectConfigurationToMedialPairing R
      (fkRectConfigurationOfEdges R F)
    let d := fkMedialWestDart (fkRectMedialVertexOfEdge R e)
    let c := fkRectRefinedBoundaryCanonicalCenter R d
    let n := orderOf (fkMedialBoundaryStep pairing)
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
          (fkRectRefinedPrimalEdgeDarts R e) V L).map
            (fkRectIntegralSquareDartMod L)) ≠ 0 := by
  classical
  dsimp only at havoid ⊢
  let pairing := fkRectConfigurationToMedialPairing R
    (fkRectConfigurationOfEdges R F)
  let d := fkMedialWestDart (fkRectMedialVertexOfEdge R e)
  let c := fkRectRefinedBoundaryCanonicalCenter R d
  let n := orderOf (fkMedialBoundaryStep pairing)
  let L := fkRectSquareCoverSide (fkRectRefinedCoverTorus R)
  let U : Int × Int :=
    (4 * (fkRectSquareDeckTranslation R w).1,
      4 * (fkRectSquareDeckTranslation R w).2)
  let V : Int × Int :=
    (4 * (fkRectSquareDeckTranslation R z).1,
      4 * (fkRectSquareDeckTranslation R z).2)
  have hsum :=
    fkRectRefinedRawInteraction_repeated_boundary_edge_eq_sum_matchedVisits
      R F e heF w z
  dsimp only at hsum
  rw [hsum]
  apply ne_of_gt
  apply Finset.sum_pos'
  · intro i hi
    apply Finset.sum_nonneg
    intro j hj
    apply fkRectRefinedBoundaryMatchedVisitTrace_nonneg_of_avoid_east
      R pairing e d _ n
    · rfl
    · exact havoid
  · have hL : 0 < L := by
      exact lt_trans (by norm_num)
        (fkRectSquareCoverSide_gt_eight (fkRectRefinedCoverTorus R))
    refine ⟨0, Finset.mem_range.mpr hL, ?_⟩
    apply Finset.sum_pos'
    · intro j hj
      apply fkRectRefinedBoundaryMatchedVisitTrace_nonneg_of_avoid_east
        R pairing e d _ n
      · rfl
      · exact havoid
    · refine ⟨0, Finset.mem_range.mpr hL, ?_⟩
      simpa [c, U, V, fkRectNatScale] using
        (fkRectRefinedBoundaryMatchedVisitTrace_canonical_pos_of_avoid_east
          R pairing e n (orderOf_pos _ ) havoid)



theorem fkRectRefinedRawInteraction_repeated_boundary_edge_ne_zero_of_not_reachable
    (R : FKRectTorus) (F : Finset R.EdgeIndex) (e : R.EdgeIndex)
    (heF : e ∉ F) (w z : Int × Int)
    (hsep : ¬ (fkMedialLoopGraph R.medialTorus
      (fkRectConfigurationToMedialPairing R
        (fkRectConfigurationOfEdges R F))).Reachable
          (fkMedialWestDart (fkRectMedialVertexOfEdge R e))
          (fkMedialEastDart (fkRectMedialVertexOfEdge R e))) :
    let pairing := fkRectConfigurationToMedialPairing R
      (fkRectConfigurationOfEdges R F)
    let d := fkMedialWestDart (fkRectMedialVertexOfEdge R e)
    let c := fkRectRefinedBoundaryCanonicalCenter R d
    let n := orderOf (fkMedialBoundaryStep pairing)
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
          (fkRectRefinedPrimalEdgeDarts R e) V L).map
            (fkRectIntegralSquareDartMod L)) ≠ 0 := by
  apply fkRectRefinedRawInteraction_repeated_boundary_edge_ne_zero_of_avoid_east
    R F e heF w z
  intro k
  dsimp only
  intro hk
  apply hsep
  apply (fkMedial_west_east_reachable_iff_exists_boundary_iterate
    (fkRectConfigurationToMedialPairing R
      (fkRectConfigurationOfEdges R F))
    (fkRectMedialVertexOfEdge R e)).2
  exact ⟨k, hk⟩

end

end StatMech.FrontierD
