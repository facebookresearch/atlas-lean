/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/




import Code.FrontierD.FKRectRefinedOpenWalkCarrier











namespace StatMech.FrontierD

noncomputable section



theorem fkRectRefinedRawInteraction_repeated_boundary_openEdgeOnce_eq_zero
    (R : FKRectTorus) (F : Finset R.EdgeIndex) (e : R.EdgeIndex)
    (heF : e ∈ F) (d : FKMedialDart R.medialTorus) (n : Nat)
    (s w : Int × Int) :
    let pairing := fkRectConfigurationToMedialPairing R
      (fkRectConfigurationOfEdges R F)
    let c := fkRectRefinedBoundaryCanonicalCenter R d
    let L := fkRectSquareCoverSide (fkRectRefinedCoverTorus R)
    let S : Int × Int :=
      (4 * (fkRectSquareDeckTranslation R s).1,
        4 * (fkRectSquareDeckTranslation R s).2)
    let U : Int × Int :=
      (4 * (fkRectSquareDeckTranslation R w).1,
        4 * (fkRectSquareDeckTranslation R w).2)
    fkRectRefinedRawInteraction
        ((fkRectRepeatTranslatedDartPath
          (fkRectRefinedBoundaryDarts pairing d c n) U L).map
            (fkRectIntegralSquareDartMod L))
        (((fkRectRefinedPrimalEdgeDarts R e).map
          (fkRectIntegralSquareDartTranslate S)).map
            (fkRectIntegralSquareDartMod L)) = 0 := by
  classical
  dsimp only
  let pairing := fkRectConfigurationToMedialPairing R
    (fkRectConfigurationOfEdges R F)
  let c := fkRectRefinedBoundaryCanonicalCenter R d
  let L := fkRectSquareCoverSide (fkRectRefinedCoverTorus R)
  let S : Int × Int :=
    (4 * (fkRectSquareDeckTranslation R s).1,
      4 * (fkRectSquareDeckTranslation R s).2)
  let U : Int × Int :=
    (4 * (fkRectSquareDeckTranslation R w).1,
      4 * (fkRectSquareDeckTranslation R w).2)
  change fkRectRefinedRawInteraction
      ((fkRectRepeatTranslatedDartPath
        (fkRectRefinedBoundaryDarts pairing d c n) U L).map
          (fkRectIntegralSquareDartMod L))
      (((fkRectRefinedPrimalEdgeDarts R e).map
        (fkRectIntegralSquareDartTranslate S)).map
          (fkRectIntegralSquareDartMod L)) = 0
  rw [fkRectRefinedRawInteraction_repeatTranslated_left]
  apply Finset.sum_eq_zero
  intro i hi
  let u : Int × Int :=
    ((i : Int) * w.1 - s.1, (i : Int) * w.2 - s.2)
  apply fkRectRefinedRawInteraction_translated_boundary_openEdge_eq_zero
    R F e heF d n (fkRectNatScale i U) S u
  apply Prod.ext <;>
    simp [u, S, U, fkRectNatScale, fkRectSquareDeckTranslation] <;> ring



theorem
    fkRectRefinedRawInteraction_repeated_boundary_openEdgeReverseOnce_eq_zero
    (R : FKRectTorus) (F : Finset R.EdgeIndex) (e : R.EdgeIndex)
    (heF : e ∈ F) (d : FKMedialDart R.medialTorus) (n : Nat)
    (s w : Int × Int) :
    let pairing := fkRectConfigurationToMedialPairing R
      (fkRectConfigurationOfEdges R F)
    let c := fkRectRefinedBoundaryCanonicalCenter R d
    let L := fkRectSquareCoverSide (fkRectRefinedCoverTorus R)
    let S : Int × Int :=
      (4 * (fkRectSquareDeckTranslation R s).1,
        4 * (fkRectSquareDeckTranslation R s).2)
    let U : Int × Int :=
      (4 * (fkRectSquareDeckTranslation R w).1,
        4 * (fkRectSquareDeckTranslation R w).2)
    fkRectRefinedRawInteraction
        ((fkRectRepeatTranslatedDartPath
          (fkRectRefinedBoundaryDarts pairing d c n) U L).map
            (fkRectIntegralSquareDartMod L))
        (((fkRectIntegralSquareDartListReverse
          (fkRectRefinedPrimalEdgeDarts R e)).map
            (fkRectIntegralSquareDartTranslate S)).map
              (fkRectIntegralSquareDartMod L)) = 0 := by
  classical
  dsimp only
  let pairing := fkRectConfigurationToMedialPairing R
    (fkRectConfigurationOfEdges R F)
  let c := fkRectRefinedBoundaryCanonicalCenter R d
  let L := fkRectSquareCoverSide (fkRectRefinedCoverTorus R)
  let S : Int × Int :=
    (4 * (fkRectSquareDeckTranslation R s).1,
      4 * (fkRectSquareDeckTranslation R s).2)
  let U : Int × Int :=
    (4 * (fkRectSquareDeckTranslation R w).1,
      4 * (fkRectSquareDeckTranslation R w).2)
  change fkRectRefinedRawInteraction
      ((fkRectRepeatTranslatedDartPath
        (fkRectRefinedBoundaryDarts pairing d c n) U L).map
          (fkRectIntegralSquareDartMod L))
      (((fkRectIntegralSquareDartListReverse
        (fkRectRefinedPrimalEdgeDarts R e)).map
          (fkRectIntegralSquareDartTranslate S)).map
            (fkRectIntegralSquareDartMod L)) = 0
  rw [fkRectRefinedRawInteraction_repeatTranslated_left]
  apply Finset.sum_eq_zero
  intro i hi
  let u : Int × Int :=
    ((i : Int) * w.1 - s.1, (i : Int) * w.2 - s.2)
  apply
    fkRectRefinedRawInteraction_translated_boundary_openEdgeReverse_eq_zero
      R F e heF d n (fkRectNatScale i U) S u
  apply Prod.ext <;>
    simp [u, S, U, fkRectNatScale, fkRectSquareDeckTranslation] <;> ring




theorem fkRectRefinedRawInteraction_repeated_boundary_edgeOnce_ne_zero
    (R : FKRectTorus) (F : Finset R.EdgeIndex) (e : R.EdgeIndex)
    (heF : e ∉ F) (w : Int × Int)
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
    fkRectRefinedRawInteraction
        ((fkRectRepeatTranslatedDartPath
          (fkRectRefinedBoundaryDarts pairing d c n) U L).map
            (fkRectIntegralSquareDartMod L))
        ((fkRectRefinedPrimalEdgeDarts R e).map
          (fkRectIntegralSquareDartMod L)) ≠ 0 := by
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
  have hrepeated :=
    fkRectRefinedRawInteraction_repeated_boundary_edge_ne_zero_of_not_reachable
      R F e heF w (0, 0) hsep
  dsimp only at hrepeated
  intro hone
  apply hrepeated
  rw [fkRectRefinedRawInteraction_repeatTranslated_right]
  apply Finset.sum_eq_zero
  intro j hj
  have hzero : fkRectNatScale j
      (4 * (fkRectSquareDeckTranslation R (0, 0)).1,
        4 * (fkRectSquareDeckTranslation R (0, 0)).2) = (0, 0) := by
    simp [fkRectNatScale, fkRectSquareDeckTranslation]
  rw [hzero]
  have hmap :
      (((fkRectRefinedPrimalEdgeDarts R e).map
        (fkRectIntegralSquareDartTranslate (0, 0))).map
          (fkRectIntegralSquareDartMod L)) =
        (fkRectRefinedPrimalEdgeDarts R e).map
          (fkRectIntegralSquareDartMod L) := by
    simp only [List.map_map]
    apply List.map_congr_left
    intro a ha
    rcases a with ⟨⟨x, y⟩, mu⟩
    simp [Function.comp_apply, fkRectIntegralSquareDartTranslate,
      fkRectIntegralSquareDartMod]
  rw [hmap]
  exact hone



theorem fkRectRefinedRawInteraction_repeated_west_boundary_edgeOnce_pos
    (R : FKRectTorus) (F : Finset R.EdgeIndex) (e : R.EdgeIndex)
    (heF : e ∉ F) (w : Int × Int)
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
    0 < fkRectRefinedRawInteraction
        ((fkRectRepeatTranslatedDartPath
          (fkRectRefinedBoundaryDarts pairing d c n) U L).map
            (fkRectIntegralSquareDartMod L))
        ((fkRectRefinedPrimalEdgeDarts R e).map
          (fkRectIntegralSquareDartMod L)) := by
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
  have havoid : ∀ k : Nat,
      (fkMedialBoundaryStep pairing)^[k] d ≠
        fkMedialEastDart (fkRectMedialVertexOfEdge R e) := by
    intro k hk
    apply hsep
    have hr := fkMedialBoundaryStep_iterate_reachable pairing d k
    rw [hk] at hr
    exact hr
  have hmapZero :
      (((fkRectRefinedPrimalEdgeDarts R e).map
        (fkRectIntegralSquareDartTranslate (0, 0))).map
          (fkRectIntegralSquareDartMod L)) =
        (fkRectRefinedPrimalEdgeDarts R e).map
          (fkRectIntegralSquareDartMod L) := by
    simp only [List.map_map]
    apply List.map_congr_left
    intro a ha
    rcases a with ⟨⟨x, y⟩, mu⟩
    simp [Function.comp_apply, fkRectIntegralSquareDartTranslate,
      fkRectIntegralSquareDartMod]
  rw [fkRectRefinedRawInteraction_repeatTranslated_left]
  apply Finset.sum_pos'
  · intro i hi
    let u : Int × Int := ((i : Int) * w.1, (i : Int) * w.2)
    rw [← hmapZero]
    rw [fkRectRefinedRawInteraction_translated_boundary_eq_matchedVisits
      R F e heF d n (fkRectNatScale i U) (0, 0) u]
    · apply fkRectRefinedBoundaryMatchedVisitTrace_nonneg_of_avoid_east
        R pairing e d _ n
      · rfl
      · exact havoid
    · rfl
    · apply Prod.ext <;>
        simp [u, U, fkRectNatScale, fkRectSquareDeckTranslation] <;> ring
  · have hL : 0 < L := by
      exact lt_trans (by norm_num)
        (fkRectSquareCoverSide_gt_eight (fkRectRefinedCoverTorus R))
    refine ⟨0, Finset.mem_range.mpr hL, ?_⟩
    let u : Int × Int := (0, 0)
    rw [← hmapZero]
    rw [fkRectRefinedRawInteraction_translated_boundary_eq_matchedVisits
      R F e heF d n (fkRectNatScale 0 U) (0, 0) u]
    · simpa [d, c, u, U, fkRectNatScale] using
        (fkRectRefinedBoundaryMatchedVisitTrace_canonical_pos_of_avoid_east
          R pairing e n (orderOf_pos _) havoid)
    · rfl
    · simp [u, fkRectNatScale, fkRectSquareDeckTranslation]



theorem fkRectRefinedRawInteraction_repeated_west_boundary_edge_pos
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
    0 < fkRectRefinedRawInteraction
        ((fkRectRepeatTranslatedDartPath
          (fkRectRefinedBoundaryDarts pairing d c n) U L).map
            (fkRectIntegralSquareDartMod L))
        ((fkRectRepeatTranslatedDartPath
          (fkRectRefinedPrimalEdgeDarts R e) V L).map
            (fkRectIntegralSquareDartMod L)) := by
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
  have havoid : ∀ k : Nat,
      (fkMedialBoundaryStep pairing)^[k] d ≠
        fkMedialEastDart (fkRectMedialVertexOfEdge R e) := by
    intro k hk
    apply hsep
    have hr := fkMedialBoundaryStep_iterate_reachable pairing d k
    rw [hk] at hr
    exact hr
  have hsum :=
    fkRectRefinedRawInteraction_repeated_boundary_edge_eq_sum_matchedVisits
      R F e heF w z
  dsimp only at hsum
  rw [hsum]
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
          R pairing e n (orderOf_pos _) havoid)



theorem fkRectRefinedBoundaryMatchedVisitTrace_nonpos_of_avoid_west
    (R : FKRectTorus) (pairing : FKMedialLoopPairing R.medialTorus)
    (e : R.EdgeIndex) (d : FKMedialDart R.medialTorus)
    (c : Int × Int) (n : Nat)
    (hcolor : fkMedialCheckerColor d =
      fkMedialCheckerColor
        (fkMedialEastDart (fkRectMedialVertexOfEdge R e)))
    (havoid : ∀ k : Nat,
      (fkMedialBoundaryStep pairing)^[k] d ≠
        fkMedialWestDart (fkRectMedialVertexOfEdge R e)) :
    fkRectRefinedBoundaryMatchedVisitTrace R pairing e d c n ≤ 0 := by
  induction n generalizing d c with
  | zero => simp [fkRectRefinedBoundaryMatchedVisitTrace]
  | succ n ih =>
      rw [fkRectRefinedBoundaryMatchedVisitTrace]
      have hdne : d ≠ fkMedialWestDart
          (fkRectMedialVertexOfEdge R e) := by
        simpa using havoid 0
      have htailAvoid : ∀ k : Nat,
          (fkMedialBoundaryStep pairing)^[k]
              (fkMedialBoundaryStep pairing d) ≠
            fkMedialWestDart (fkRectMedialVertexOfEdge R e) := by
        intro k
        simpa only [Function.iterate_succ_apply] using havoid (k + 1)
      have htailColor : fkMedialCheckerColor
          (fkMedialBoundaryStep pairing d) =
          fkMedialCheckerColor
            (fkMedialEastDart (fkRectMedialVertexOfEdge R e)) := by
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
        have hcolorWest : fkMedialCheckerColor d =
            fkMedialCheckerColor
              (fkMedialWestDart (fkRectMedialVertexOfEdge R e)) := by
          rw [fkMedialCheckerColor_west_eq_east]
          exact hcolor
        rcases fkMedialDart_eq_west_or_east_of_vertex_eq_of_checkerColor
            d (fkRectMedialVertexOfEdge R e) hdv hcolorWest with
          hwest | heast
        · exact False.elim (hdne hwest)
        · exact add_nonpos (by norm_num) htail
      · exact add_nonpos (by norm_num) htail



theorem fkRectRefinedBoundaryMatchedVisitTrace_canonical_neg_of_avoid_west
    (R : FKRectTorus) (pairing : FKMedialLoopPairing R.medialTorus)
    (e : R.EdgeIndex) (n : Nat) (hn : 0 < n)
    (havoid : ∀ k : Nat,
      (fkMedialBoundaryStep pairing)^[k]
          (fkMedialEastDart (fkRectMedialVertexOfEdge R e)) ≠
        fkMedialWestDart (fkRectMedialVertexOfEdge R e)) :
    fkRectRefinedBoundaryMatchedVisitTrace R pairing e
      (fkMedialEastDart (fkRectMedialVertexOfEdge R e))
      (fkRectRefinedBoundaryCanonicalCenter R
        (fkMedialEastDart (fkRectMedialVertexOfEdge R e))) n < 0 := by
  obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hn.ne'
  rw [fkRectRefinedBoundaryMatchedVisitTrace]
  have htailAvoid : ∀ k : Nat,
      (fkMedialBoundaryStep pairing)^[k]
          (fkMedialBoundaryStep pairing
            (fkMedialEastDart (fkRectMedialVertexOfEdge R e))) ≠
        fkMedialWestDart (fkRectMedialVertexOfEdge R e) := by
    intro k
    simpa only [Function.iterate_succ_apply] using havoid (k + 1)
  have htailColor : fkMedialCheckerColor
      (fkMedialBoundaryStep pairing
        (fkMedialEastDart (fkRectMedialVertexOfEdge R e))) =
      fkMedialCheckerColor
        (fkMedialEastDart (fkRectMedialVertexOfEdge R e)) := by
    rw [fkMedialCheckerColor_boundaryStep]
  have htail :=
    fkRectRefinedBoundaryMatchedVisitTrace_nonpos_of_avoid_west
      R pairing e
      (fkMedialBoundaryStep pairing
        (fkMedialEastDart (fkRectMedialVertexOfEdge R e)))
      (fkRectRefinedBondCenter
        (fkRectRefinedBoundaryCanonicalCenter R
          (fkMedialEastDart (fkRectMedialVertexOfEdge R e)))
        (fkMedialLocalMate pairing
          (fkMedialEastDart (fkRectMedialVertexOfEdge R e))).2)
      m htailColor htailAvoid
  have hedge : fkRectTorusMedialEdgeEquiv R
      (fkMedialEastDart (fkRectMedialVertexOfEdge R e)).1 = e := by
    simp [fkMedialEastDart]
  have hcenter :
      let c := fkRectRefinedBoundaryCanonicalCenter R
        (fkMedialEastDart (fkRectMedialVertexOfEdge R e))
      let L := fkRectSquareCoverSide (fkRectRefinedCoverTorus R)
      (((c.1 : Int) : ZMod L), ((c.2 : Int) : ZMod L)) =
        ((((fkRectRefinedPrimalEdgeCenter R e).1 : Int) : ZMod L),
          (((fkRectRefinedPrimalEdgeCenter R e).2 : Int) : ZMod L)) := by
    simp [fkRectRefinedBoundaryCanonicalCenter, hedge]
  have hne : fkMedialEastDart (fkRectMedialVertexOfEdge R e) ≠
      fkMedialWestDart (fkRectMedialVertexOfEdge R e) := by
    simp [fkMedialEastDart, fkMedialWestDart]
  rw [if_pos ⟨hedge, hcenter⟩, if_neg hne]
  exact Int.add_neg_of_neg_of_nonpos (by norm_num) htail




theorem fkRectRefinedRawInteraction_repeated_east_boundary_edgeOnce_neg
    (R : FKRectTorus) (F : Finset R.EdgeIndex) (e : R.EdgeIndex)
    (heF : e ∉ F) (w : Int × Int)
    (hsep : ¬ (fkMedialLoopGraph R.medialTorus
      (fkRectConfigurationToMedialPairing R
        (fkRectConfigurationOfEdges R F))).Reachable
          (fkMedialWestDart (fkRectMedialVertexOfEdge R e))
          (fkMedialEastDart (fkRectMedialVertexOfEdge R e))) :
    let pairing := fkRectConfigurationToMedialPairing R
      (fkRectConfigurationOfEdges R F)
    let d := fkMedialEastDart (fkRectMedialVertexOfEdge R e)
    let c := fkRectRefinedBoundaryCanonicalCenter R d
    let n := orderOf (fkMedialBoundaryStep pairing)
    let L := fkRectSquareCoverSide (fkRectRefinedCoverTorus R)
    let U : Int × Int :=
      (4 * (fkRectSquareDeckTranslation R w).1,
        4 * (fkRectSquareDeckTranslation R w).2)
    fkRectRefinedRawInteraction
        ((fkRectRepeatTranslatedDartPath
          (fkRectRefinedBoundaryDarts pairing d c n) U L).map
            (fkRectIntegralSquareDartMod L))
        ((fkRectRefinedPrimalEdgeDarts R e).map
          (fkRectIntegralSquareDartMod L)) < 0 := by
  classical
  dsimp only
  let pairing := fkRectConfigurationToMedialPairing R
    (fkRectConfigurationOfEdges R F)
  let d := fkMedialEastDart (fkRectMedialVertexOfEdge R e)
  let c := fkRectRefinedBoundaryCanonicalCenter R d
  let n := orderOf (fkMedialBoundaryStep pairing)
  let L := fkRectSquareCoverSide (fkRectRefinedCoverTorus R)
  let U : Int × Int :=
    (4 * (fkRectSquareDeckTranslation R w).1,
      4 * (fkRectSquareDeckTranslation R w).2)
  have havoid : ∀ k : Nat,
      (fkMedialBoundaryStep pairing)^[k] d ≠
        fkMedialWestDart (fkRectMedialVertexOfEdge R e) := by
    intro k hk
    apply hsep
    have hr := fkMedialBoundaryStep_iterate_reachable pairing d k
    rw [hk] at hr
    exact hr.symm
  have hmapZero :
      (((fkRectRefinedPrimalEdgeDarts R e).map
        (fkRectIntegralSquareDartTranslate (0, 0))).map
          (fkRectIntegralSquareDartMod L)) =
        (fkRectRefinedPrimalEdgeDarts R e).map
          (fkRectIntegralSquareDartMod L) := by
    simp only [List.map_map]
    apply List.map_congr_left
    intro a ha
    rcases a with ⟨⟨x, y⟩, mu⟩
    simp [Function.comp_apply, fkRectIntegralSquareDartTranslate,
      fkRectIntegralSquareDartMod]
  rw [fkRectRefinedRawInteraction_repeatTranslated_left]
  apply Finset.sum_neg'
  · intro i hi
    let u : Int × Int := ((i : Int) * w.1, (i : Int) * w.2)
    rw [← hmapZero]
    rw [fkRectRefinedRawInteraction_translated_boundary_eq_matchedVisits
      R F e heF d n (fkRectNatScale i U) (0, 0) u]
    · apply fkRectRefinedBoundaryMatchedVisitTrace_nonpos_of_avoid_west
        R pairing e d _ n
      · rfl
      · exact havoid
    · simp [d]
    · apply Prod.ext <;>
        simp [u, U, fkRectNatScale, fkRectSquareDeckTranslation] <;> ring
  · have hL : 0 < L := by
      exact lt_trans (by norm_num)
        (fkRectSquareCoverSide_gt_eight (fkRectRefinedCoverTorus R))
    refine ⟨0, Finset.mem_range.mpr hL, ?_⟩
    let u : Int × Int := (0, 0)
    rw [← hmapZero]
    rw [fkRectRefinedRawInteraction_translated_boundary_eq_matchedVisits
      R F e heF d n (fkRectNatScale 0 U) (0, 0) u]
    · simpa [d, c, u, U, fkRectNatScale] using
        (fkRectRefinedBoundaryMatchedVisitTrace_canonical_neg_of_avoid_west
          R pairing e n (orderOf_pos _) havoid)
    · simp [d]
    · simp [u, fkRectNatScale, fkRectSquareDeckTranslation]



theorem fkRectRefinedRawInteraction_repeated_east_boundary_edge_neg
    (R : FKRectTorus) (F : Finset R.EdgeIndex) (e : R.EdgeIndex)
    (heF : e ∉ F) (w z : Int × Int)
    (hsep : ¬ (fkMedialLoopGraph R.medialTorus
      (fkRectConfigurationToMedialPairing R
        (fkRectConfigurationOfEdges R F))).Reachable
          (fkMedialWestDart (fkRectMedialVertexOfEdge R e))
          (fkMedialEastDart (fkRectMedialVertexOfEdge R e))) :
    let pairing := fkRectConfigurationToMedialPairing R
      (fkRectConfigurationOfEdges R F)
    let d := fkMedialEastDart (fkRectMedialVertexOfEdge R e)
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
            (fkRectIntegralSquareDartMod L)) < 0 := by
  classical
  dsimp only
  let pairing := fkRectConfigurationToMedialPairing R
    (fkRectConfigurationOfEdges R F)
  let d := fkMedialEastDart (fkRectMedialVertexOfEdge R e)
  let c := fkRectRefinedBoundaryCanonicalCenter R d
  let n := orderOf (fkMedialBoundaryStep pairing)
  let L := fkRectSquareCoverSide (fkRectRefinedCoverTorus R)
  let U : Int × Int :=
    (4 * (fkRectSquareDeckTranslation R w).1,
      4 * (fkRectSquareDeckTranslation R w).2)
  let V : Int × Int :=
    (4 * (fkRectSquareDeckTranslation R z).1,
      4 * (fkRectSquareDeckTranslation R z).2)
  have havoid : ∀ k : Nat,
      (fkMedialBoundaryStep pairing)^[k] d ≠
        fkMedialWestDart (fkRectMedialVertexOfEdge R e) := by
    intro k hk
    apply hsep
    have hr := fkMedialBoundaryStep_iterate_reachable pairing d k
    rw [hk] at hr
    exact hr.symm
  rw [fkRectRefinedRawInteraction_repeatTranslated_both]
  apply Finset.sum_neg'
  · intro i hi
    apply Finset.sum_nonpos
    intro j hj
    let u : Int × Int :=
      ((i : Int) * w.1 - (j : Int) * z.1,
        (i : Int) * w.2 - (j : Int) * z.2)
    rw [fkRectRefinedRawInteraction_translated_boundary_eq_matchedVisits
      R F e heF d n (fkRectNatScale i U) (fkRectNatScale j V) u]
    · apply fkRectRefinedBoundaryMatchedVisitTrace_nonpos_of_avoid_west
        R pairing e d _ n
      · simp [d]
      · exact havoid
    · simp [d]
    · apply Prod.ext <;>
        simp [u, U, V, fkRectNatScale, fkRectSquareDeckTranslation] <;> ring
  · have hL : 0 < L := by
      exact lt_trans (by norm_num)
        (fkRectSquareCoverSide_gt_eight (fkRectRefinedCoverTorus R))
    refine ⟨0, Finset.mem_range.mpr hL, ?_⟩
    apply Finset.sum_neg'
    · intro j hj
      let u : Int × Int :=
        (-(j : Int) * z.1, -(j : Int) * z.2)
      rw [fkRectRefinedRawInteraction_translated_boundary_eq_matchedVisits
        R F e heF d n (fkRectNatScale 0 U) (fkRectNatScale j V) u]
      · apply fkRectRefinedBoundaryMatchedVisitTrace_nonpos_of_avoid_west
          R pairing e d _ n
        · simp [d]
        · exact havoid
      · simp [d]
      · apply Prod.ext <;>
          simp [u, U, V, fkRectNatScale,
            fkRectSquareDeckTranslation] <;> ring
    · refine ⟨0, Finset.mem_range.mpr hL, ?_⟩
      let u : Int × Int := (0, 0)
      rw [fkRectRefinedRawInteraction_translated_boundary_eq_matchedVisits
        R F e heF d n (fkRectNatScale 0 U) (fkRectNatScale 0 V) u]
      · simpa [d, c, u, U, V, fkRectNatScale] using
          (fkRectRefinedBoundaryMatchedVisitTrace_canonical_neg_of_avoid_west
            R pairing e n (orderOf_pos _) havoid)
      · simp [d]
      · simp [u, U, V, fkRectNatScale, fkRectSquareDeckTranslation]



theorem fkRectRefinedRawInteraction_repeated_boundary_edgeOnce_nonpos_of_avoid_west
    (R : FKRectTorus) (F : Finset R.EdgeIndex) (e : R.EdgeIndex)
    (heF : e ∉ F) (d : FKMedialDart R.medialTorus) (w : Int × Int)
    (hcolor : fkMedialCheckerColor d =
      fkMedialCheckerColor
        (fkMedialWestDart (fkRectMedialVertexOfEdge R e)))
    (havoid : ∀ k : Nat,
      let pairing := fkRectConfigurationToMedialPairing R
        (fkRectConfigurationOfEdges R F)
      (fkMedialBoundaryStep pairing)^[k] d ≠
        fkMedialWestDart (fkRectMedialVertexOfEdge R e)) :
    let pairing := fkRectConfigurationToMedialPairing R
      (fkRectConfigurationOfEdges R F)
    let c := fkRectRefinedBoundaryCanonicalCenter R d
    let n := orderOf (fkMedialBoundaryStep pairing)
    let L := fkRectSquareCoverSide (fkRectRefinedCoverTorus R)
    let U : Int × Int :=
      (4 * (fkRectSquareDeckTranslation R w).1,
        4 * (fkRectSquareDeckTranslation R w).2)
    fkRectRefinedRawInteraction
        ((fkRectRepeatTranslatedDartPath
          (fkRectRefinedBoundaryDarts pairing d c n) U L).map
            (fkRectIntegralSquareDartMod L))
        ((fkRectRefinedPrimalEdgeDarts R e).map
          (fkRectIntegralSquareDartMod L)) ≤ 0 := by
  classical
  dsimp only at havoid ⊢
  let pairing := fkRectConfigurationToMedialPairing R
    (fkRectConfigurationOfEdges R F)
  let c := fkRectRefinedBoundaryCanonicalCenter R d
  let n := orderOf (fkMedialBoundaryStep pairing)
  let L := fkRectSquareCoverSide (fkRectRefinedCoverTorus R)
  let U : Int × Int :=
    (4 * (fkRectSquareDeckTranslation R w).1,
      4 * (fkRectSquareDeckTranslation R w).2)
  have hmapZero :
      (((fkRectRefinedPrimalEdgeDarts R e).map
        (fkRectIntegralSquareDartTranslate (0, 0))).map
          (fkRectIntegralSquareDartMod L)) =
        (fkRectRefinedPrimalEdgeDarts R e).map
          (fkRectIntegralSquareDartMod L) := by
    simp only [List.map_map]
    apply List.map_congr_left
    intro a ha
    rcases a with ⟨⟨x, y⟩, mu⟩
    simp [Function.comp_apply, fkRectIntegralSquareDartTranslate,
      fkRectIntegralSquareDartMod]
  rw [fkRectRefinedRawInteraction_repeatTranslated_left]
  apply Finset.sum_nonpos
  intro i hi
  let u : Int × Int := ((i : Int) * w.1, (i : Int) * w.2)
  rw [← hmapZero]
  rw [fkRectRefinedRawInteraction_translated_boundary_eq_matchedVisits
    R F e heF d n (fkRectNatScale i U) (0, 0) u]
  · apply fkRectRefinedBoundaryMatchedVisitTrace_nonpos_of_avoid_west
      R pairing e d _ n hcolor havoid
  · exact hcolor
  · apply Prod.ext <;>
      simp [u, U, fkRectNatScale, fkRectSquareDeckTranslation] <;> ring



theorem
    fkRectRefinedRawInteraction_repeated_boundary_edgeOnce_eq_zero_of_avoid_west_east
    (R : FKRectTorus) (F : Finset R.EdgeIndex) (e : R.EdgeIndex)
    (heF : e ∉ F) (d : FKMedialDart R.medialTorus) (w : Int × Int)
    (hcolor : fkMedialCheckerColor d =
      fkMedialCheckerColor
        (fkMedialWestDart (fkRectMedialVertexOfEdge R e)))
    (hwest : ∀ k : Nat,
      let pairing := fkRectConfigurationToMedialPairing R
        (fkRectConfigurationOfEdges R F)
      (fkMedialBoundaryStep pairing)^[k] d ≠
        fkMedialWestDart (fkRectMedialVertexOfEdge R e))
    (heast : ∀ k : Nat,
      let pairing := fkRectConfigurationToMedialPairing R
        (fkRectConfigurationOfEdges R F)
      (fkMedialBoundaryStep pairing)^[k] d ≠
        fkMedialEastDart (fkRectMedialVertexOfEdge R e)) :
    let pairing := fkRectConfigurationToMedialPairing R
      (fkRectConfigurationOfEdges R F)
    let c := fkRectRefinedBoundaryCanonicalCenter R d
    let n := orderOf (fkMedialBoundaryStep pairing)
    let L := fkRectSquareCoverSide (fkRectRefinedCoverTorus R)
    let U : Int × Int :=
      (4 * (fkRectSquareDeckTranslation R w).1,
        4 * (fkRectSquareDeckTranslation R w).2)
    fkRectRefinedRawInteraction
        ((fkRectRepeatTranslatedDartPath
          (fkRectRefinedBoundaryDarts pairing d c n) U L).map
            (fkRectIntegralSquareDartMod L))
        ((fkRectRefinedPrimalEdgeDarts R e).map
          (fkRectIntegralSquareDartMod L)) = 0 := by
  classical
  dsimp only at hwest heast ⊢
  let pairing := fkRectConfigurationToMedialPairing R
    (fkRectConfigurationOfEdges R F)
  let c := fkRectRefinedBoundaryCanonicalCenter R d
  let n := orderOf (fkMedialBoundaryStep pairing)
  let L := fkRectSquareCoverSide (fkRectRefinedCoverTorus R)
  let U : Int × Int :=
    (4 * (fkRectSquareDeckTranslation R w).1,
      4 * (fkRectSquareDeckTranslation R w).2)
  have hmapZero :
      (((fkRectRefinedPrimalEdgeDarts R e).map
        (fkRectIntegralSquareDartTranslate (0, 0))).map
          (fkRectIntegralSquareDartMod L)) =
        (fkRectRefinedPrimalEdgeDarts R e).map
          (fkRectIntegralSquareDartMod L) := by
    simp only [List.map_map]
    apply List.map_congr_left
    intro a ha
    rcases a with ⟨⟨x, y⟩, mu⟩
    simp [Function.comp_apply, fkRectIntegralSquareDartTranslate,
      fkRectIntegralSquareDartMod]
  rw [fkRectRefinedRawInteraction_repeatTranslated_left]
  apply Finset.sum_eq_zero
  intro i hi
  let u : Int × Int := ((i : Int) * w.1, (i : Int) * w.2)
  rw [← hmapZero]
  rw [fkRectRefinedRawInteraction_translated_boundary_eq_matchedVisits
    R F e heF d n (fkRectNatScale i U) (0, 0) u]
  · exact fkRectRefinedBoundaryMatchedVisitTrace_eq_zero_of_avoid_west_east
      R pairing e d _ n hcolor hwest heast
  · exact hcolor
  · apply Prod.ext <;>
      simp [u, U, fkRectNatScale, fkRectSquareDeckTranslation] <;> ring



theorem fkRectRefinedRawInteraction_repeated_boundary_edge_nonpos_of_avoid_west
    (R : FKRectTorus) (F : Finset R.EdgeIndex) (e : R.EdgeIndex)
    (heF : e ∉ F) (d : FKMedialDart R.medialTorus) (w z : Int × Int)
    (hcolor : fkMedialCheckerColor d =
      fkMedialCheckerColor
        (fkMedialWestDart (fkRectMedialVertexOfEdge R e)))
    (havoid : ∀ k : Nat,
      let pairing := fkRectConfigurationToMedialPairing R
        (fkRectConfigurationOfEdges R F)
      (fkMedialBoundaryStep pairing)^[k] d ≠
        fkMedialWestDart (fkRectMedialVertexOfEdge R e)) :
    let pairing := fkRectConfigurationToMedialPairing R
      (fkRectConfigurationOfEdges R F)
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
            (fkRectIntegralSquareDartMod L)) ≤ 0 := by
  classical
  dsimp only at havoid ⊢
  let pairing := fkRectConfigurationToMedialPairing R
    (fkRectConfigurationOfEdges R F)
  let c := fkRectRefinedBoundaryCanonicalCenter R d
  let n := orderOf (fkMedialBoundaryStep pairing)
  let L := fkRectSquareCoverSide (fkRectRefinedCoverTorus R)
  let U : Int × Int :=
    (4 * (fkRectSquareDeckTranslation R w).1,
      4 * (fkRectSquareDeckTranslation R w).2)
  let V : Int × Int :=
    (4 * (fkRectSquareDeckTranslation R z).1,
      4 * (fkRectSquareDeckTranslation R z).2)
  rw [fkRectRefinedRawInteraction_repeatTranslated_both]
  apply Finset.sum_nonpos
  intro i hi
  apply Finset.sum_nonpos
  intro j hj
  let u : Int × Int :=
    ((i : Int) * w.1 - (j : Int) * z.1,
      (i : Int) * w.2 - (j : Int) * z.2)
  rw [fkRectRefinedRawInteraction_translated_boundary_eq_matchedVisits
    R F e heF d n (fkRectNatScale i U) (fkRectNatScale j V) u]
  · apply fkRectRefinedBoundaryMatchedVisitTrace_nonpos_of_avoid_west
      R pairing e d _ n hcolor havoid
  · exact hcolor
  · apply Prod.ext <;>
      simp [u, U, V, fkRectNatScale, fkRectSquareDeckTranslation] <;> ring



theorem fkRectRefinedRawInteraction_repeated_boundary_edge_nonneg_of_avoid_east
    (R : FKRectTorus) (F : Finset R.EdgeIndex) (e : R.EdgeIndex)
    (heF : e ∉ F) (d : FKMedialDart R.medialTorus) (w z : Int × Int)
    (hcolor : fkMedialCheckerColor d =
      fkMedialCheckerColor
        (fkMedialWestDart (fkRectMedialVertexOfEdge R e)))
    (havoid : ∀ k : Nat,
      let pairing := fkRectConfigurationToMedialPairing R
        (fkRectConfigurationOfEdges R F)
      (fkMedialBoundaryStep pairing)^[k] d ≠
        fkMedialEastDart (fkRectMedialVertexOfEdge R e)) :
    let pairing := fkRectConfigurationToMedialPairing R
      (fkRectConfigurationOfEdges R F)
    let c := fkRectRefinedBoundaryCanonicalCenter R d
    let n := orderOf (fkMedialBoundaryStep pairing)
    let L := fkRectSquareCoverSide (fkRectRefinedCoverTorus R)
    let U : Int × Int :=
      (4 * (fkRectSquareDeckTranslation R w).1,
        4 * (fkRectSquareDeckTranslation R w).2)
    let V : Int × Int :=
      (4 * (fkRectSquareDeckTranslation R z).1,
        4 * (fkRectSquareDeckTranslation R z).2)
    0 ≤ fkRectRefinedRawInteraction
        ((fkRectRepeatTranslatedDartPath
          (fkRectRefinedBoundaryDarts pairing d c n) U L).map
            (fkRectIntegralSquareDartMod L))
        ((fkRectRepeatTranslatedDartPath
          (fkRectRefinedPrimalEdgeDarts R e) V L).map
            (fkRectIntegralSquareDartMod L)) := by
  classical
  dsimp only at havoid ⊢
  let pairing := fkRectConfigurationToMedialPairing R
    (fkRectConfigurationOfEdges R F)
  let c := fkRectRefinedBoundaryCanonicalCenter R d
  let n := orderOf (fkMedialBoundaryStep pairing)
  let L := fkRectSquareCoverSide (fkRectRefinedCoverTorus R)
  let U : Int × Int :=
    (4 * (fkRectSquareDeckTranslation R w).1,
      4 * (fkRectSquareDeckTranslation R w).2)
  let V : Int × Int :=
    (4 * (fkRectSquareDeckTranslation R z).1,
      4 * (fkRectSquareDeckTranslation R z).2)
  rw [fkRectRefinedRawInteraction_repeatTranslated_both]
  apply Finset.sum_nonneg
  intro i hi
  apply Finset.sum_nonneg
  intro j hj
  let u : Int × Int :=
    ((i : Int) * w.1 - (j : Int) * z.1,
      (i : Int) * w.2 - (j : Int) * z.2)
  rw [fkRectRefinedRawInteraction_translated_boundary_eq_matchedVisits
    R F e heF d n (fkRectNatScale i U) (fkRectNatScale j V) u]
  · apply fkRectRefinedBoundaryMatchedVisitTrace_nonneg_of_avoid_east
      R pairing e d _ n hcolor havoid
  · exact hcolor
  · apply Prod.ext <;>
      simp [u, U, V, fkRectNatScale, fkRectSquareDeckTranslation] <;> ring



theorem FKRectRefinedOpenEdgeBlocks.boundary_interaction_eq_zero
    (R : FKRectTorus) (F : Finset R.EdgeIndex)
    {l : List FKRectIntegralSquareDart}
    (hl : FKRectRefinedOpenEdgeBlocks R F l)
    (d : FKMedialDart R.medialTorus) (n : Nat) (w : Int × Int) :
    let pairing := fkRectConfigurationToMedialPairing R
      (fkRectConfigurationOfEdges R F)
    let c := fkRectRefinedBoundaryCanonicalCenter R d
    let L := fkRectSquareCoverSide (fkRectRefinedCoverTorus R)
    let U : Int × Int :=
      (4 * (fkRectSquareDeckTranslation R w).1,
        4 * (fkRectSquareDeckTranslation R w).2)
    fkRectRefinedRawInteraction
        ((fkRectRepeatTranslatedDartPath
          (fkRectRefinedBoundaryDarts pairing d c n) U L).map
            (fkRectIntegralSquareDartMod L))
        (l.map (fkRectIntegralSquareDartMod L)) = 0 := by
  induction hl with
  | nil => simp [fkRectRefinedRawInteraction]
  | @consForward e s he l tail ih =>
      dsimp only
      rw [List.map_append, fkRectRefinedRawInteraction_append_right]
      rw [fkRectRefinedRawInteraction_repeated_boundary_openEdgeOnce_eq_zero
        R F e he d n s w, ih, zero_add]
  | @consReverse e s he l tail ih =>
      dsimp only
      rw [List.map_append, fkRectRefinedRawInteraction_append_right]
      rw [
        fkRectRefinedRawInteraction_repeated_boundary_openEdgeReverseOnce_eq_zero
          R F e he d n s w,
        ih, zero_add]

end

end StatMech.FrontierD
