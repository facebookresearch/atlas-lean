/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/




import Code.FrontierD.FKRectRefinedDualPrimalOpenInteraction
import Code.FrontierD.FKRectRefinedDualWalkCarrier









namespace StatMech.FrontierD

noncomputable section



theorem fkRect_dualOpen_primalOpen_closedWalks_not_windingIndependent
    (R : FKRectTorus) (omega : R.Configuration)
    {x y : R.Vertex}
    (z : (fkRectOpenGraph R
      (fkRectDualConfigurationEquiv R omega)).Walk x x)
    (w : (fkRectOpenGraph R omega).Walk y y) :
    ¬ FKRectWindingIndependent
      (fkRectWalkWinding R z) (fkRectWalkWinding R w) := by
  classical
  let F := fkRectOpenEdges R omega
  have homega : fkRectConfigurationOfEdges R F = omega := by
    simp [F]
  have hle : fkRectOpenGraph R omega ≤
      fkRectOpenGraph R (fkRectConfigurationOfEdges R F) := by
    rw [homega]
  let wF := w.mapLe hle
  let p : Int × Int := ((x.1.val : Int), (x.2.val : Int))
  have hp : fkRectLiftedVertex R p = x := by
    apply Prod.ext <;> simp [p, fkRectLiftedVertex]
  obtain ⟨q, l, hq, hzlift, hlpath, hlblocks⟩ :=
    exists_fkRectRefinedDualOpenWalkCarrier R omega z p hp
  let D : FKRectRefinedDualWalkCarrier R hzlift := ⟨l, hlpath⟩
  let a : Int × Int := ((y.1.val : Int), (y.2.val : Int))
  have ha : fkRectLiftedVertex R a = y := by
    apply Prod.ext <;> simp [a, fkRectLiftedVertex]
  obtain ⟨b, k, hb, hwlift, hkpath, hkblocks⟩ :=
    exists_fkRectRefinedOpenWalkCarrier R F wF a ha
  let C : FKRectRefinedWalkCarrier R hwlift := ⟨k, hkpath⟩
  have hDtranslation : D.translation =
      fkRectRefinedDeckTranslation R (fkRectWalkWinding R z) := by
    unfold FKRectRefinedDualWalkCarrier.translation
    rw [hzlift.closed_develop_sub_eq_deck_winding R]
    rfl
  have hCtranslation : C.translation =
      fkRectRefinedDeckTranslation R (fkRectWalkWinding R wF) := by
    unfold FKRectRefinedWalkCarrier.translation
    rw [hwlift.closed_develop_sub_eq_deck_winding R]
    rfl
  have hzero := hlblocks.repeated_interaction_eq_zero_of_edgeBlocks
    R omega F hkblocks
    (fkRectWalkWinding R z) (fkRectWalkWinding R wF)
    (fkRectSquareCoverSide (fkRectRefinedCoverTorus R))
    (fkRectSquareCoverSide (fkRectRefinedCoverTorus R))
    (fun d e hd he u v =>
      fkRectRefined_dualOpen_primalOpen_edgeBlocks_interaction_eq_zero
        R omega d e hd (by
          rw [← homega]
          exact (fkRectConfigurationOfEdges_apply R F e).2 he) u v)
  have hinteraction :
      fkRectRefinedRawInteraction D.coverDarts C.coverDarts = 0 := by
    unfold FKRectRefinedDualWalkCarrier.coverDarts
      FKRectRefinedWalkCarrier.coverDarts fkRectSquareCoverDartList
    rw [hDtranslation, hCtranslation]
    exact hzero
  intro hindependent
  have hindependentF : FKRectWindingIndependent
      (fkRectWalkWinding R z) (fkRectWalkWinding R wF) := by
    simpa [wF, fkRectWalkWinding_mapLe] using hindependent
  have hne :=
    (D.interaction_ne_zero_iff_windingIndependent R C).2 hindependentF
  exact hne hinteraction

end

end StatMech.FrontierD
