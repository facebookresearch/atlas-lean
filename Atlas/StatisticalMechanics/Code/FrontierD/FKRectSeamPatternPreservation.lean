/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/




import Code.FrontierD.FKRectDualSourceBarrierPattern



namespace StatMech.FrontierD

noncomputable section



theorem fkRectForceIndexedPattern_innerRestrict_eq_of_outside
    (R : FKRectTorus) (S : Set R.Vertex)
    (I : Finset R.EdgeIndex) (eta omega : R.Configuration)
    (hI : ∀ a ∈ I,
      fkRectTorusIndexedEdge R a ∉
        Set.range (FK.ocd_innerEdge
          (Subtype.val : FKRectInducedVertex R S -> R.Vertex))) :
    FK.ocd_innerRestrict
        (Subtype.val : FKRectInducedVertex R S -> R.Vertex)
        (fkRectFullGraphConfiguration R
          (fkRectForceIndexedPattern R I eta omega)) =
      FK.ocd_innerRestrict
        (Subtype.val : FKRectInducedVertex R S -> R.Vertex)
        (fkRectFullGraphConfiguration R omega) := by
  funext e
  let E := FK.ocd_innerEdge
    (Subtype.val : FKRectInducedVertex R S -> R.Vertex) e
  by_cases hE : E ∈ (fkRectTorusGraph R).edgeSet
  · let a : R.EdgeIndex :=
      (fkRectEdgeGraphEquiv R).symm ⟨E, hE⟩
    have haedge : fkRectTorusIndexedEdge R a = E := by
      exact fkRectEdgeGraphEquiv_symm_indexedEdge R ⟨E, hE⟩
    have ha : a ∉ I := by
      intro ha
      apply hI a ha
      rw [haedge]
      exact ⟨e, rfl⟩
    change fkRectFullGraphConfiguration R
        (fkRectForceIndexedPattern R I eta omega) E =
      fkRectFullGraphConfiguration R omega E
    rw [← haedge, fkRectFullGraphConfiguration_indexedEdge,
      fkRectFullGraphConfiguration_indexedEdge,
      fkRectForceIndexedPattern_of_not_mem R eta omega ha]
  · change fkRectFullGraphConfiguration R
        (fkRectForceIndexedPattern R I eta omega) E =
      fkRectFullGraphConfiguration R omega E
    rw [fkRectFullGraphConfiguration_eq_false_of_not_edge R _ hE,
      fkRectFullGraphConfiguration_eq_false_of_not_edge R _ hE]


theorem fkRectForceHorizontalCut_innerRestrict_rightBand_eq
    (R : FKRectTorus) (cut lower upper : Nat) (hlower : 1 <= lower)
    (eta omega : R.Configuration) :
    FK.ocd_innerRestrict
        (Subtype.val :
          FKRectRightStripBandVertex R cut lower upper -> R.Vertex)
        (fkRectFullGraphConfiguration R
          (fkRectForceIndexedPattern R
            (fkRectHorizontalCutEdges R) eta omega)) =
      FK.ocd_innerRestrict
        (Subtype.val :
          FKRectRightStripBandVertex R cut lower upper -> R.Vertex)
        (fkRectFullGraphConfiguration R omega) := by
  apply fkRectForceIndexedPattern_innerRestrict_eq_of_outside
  intro a ha
  exact fkRect_verticalSeam_not_rightStripBand_innerEdgeRange
    R cut lower upper hlower
      (fkRectHorizontalCutEdge_crossesVerticalSeam R a ha)



theorem fkRectForceDualPullbackSeam_preserves_rightBand_chain
    (R : FKRectTorus) (cut lower upper : Nat) (hlower : 1 <= lower)
    (eta omega : R.Configuration)
    (t : Finset (FKRectRightStripBandVertex R cut lower upper ×
      FKRectRightStripBandVertex R cut lower upper))
    (hchain :
      FK.ocd_innerRestrict
          (Subtype.val :
            FKRectRightStripBandVertex R cut lower upper -> R.Vertex)
          (fkRectFullGraphConfiguration R omega) ∈
        fkRectInducedConnectionChainEvent R
          (fkRectRightStripBand R cut lower upper) t) :
    FK.ocd_innerRestrict
        (Subtype.val :
          FKRectRightStripBandVertex R cut lower upper -> R.Vertex)
        (fkRectFullGraphConfiguration R
          (fkRectForceIndexedPattern R
            (fkRectDualPullbackIndexSet R (fkRectHorizontalCutEdges R))
            eta omega)) ∈
      fkRectInducedConnectionChainEvent R
        (fkRectRightStripBand R cut lower upper) t := by
  rw [fkRectDualPullbackIndexSet_horizontalCutEdges,
    fkRectForceHorizontalCut_innerRestrict_rightBand_eq
      R cut lower upper hlower]
  exact hchain


def fkRectUnitGapColumn (R : FKRectTorus) : Fin R.width :=
  ⟨1, lt_trans Nat.one_lt_two R.width_gt_two⟩

theorem fkRectDualPullbackUnitGap_eq_verticalSeam (R : FKRectTorus) :
    fkRectDualEdgeToEdge R (fkRectUnitLeftBarrierGap R) =
      fkRectVerticalSeamEdgeAt R (fkRectUnitGapColumn R) := by
  rfl

theorem fkRectEdgeToDualEdge_unitVerticalSeam (R : FKRectTorus) :
    fkRectEdgeToDualEdge R
        (fkRectVerticalSeamEdgeAt R (fkRectUnitGapColumn R)) =
      fkRectUnitLeftBarrierGap R := by
  rfl



theorem fkRectForceDualPullbackUnitPattern_verticalSeam_open
    (R : FKRectTorus) (omega : R.Configuration) :
    fkRectForceIndexedPattern R
        (fkRectDualPullbackIndexSet R (fkRectHorizontalCutEdges R))
        (fkRectDualPullbackConfiguration R
          (fkRectAllButOneOpenConfiguration R
            (fkRectUnitLeftBarrierGap R))) omega
        (fkRectVerticalSeamEdgeAt R (fkRectUnitGapColumn R)) = true := by
  rw [fkRectDualPullbackIndexSet_horizontalCutEdges,
    fkRectForceIndexedPattern_of_mem]
  · unfold fkRectDualPullbackConfiguration
    rw [fkRectEdgeToDualEdge_unitVerticalSeam]
    simp [fkRectAllButOneOpenConfiguration]
  · simp [mem_fkRectHorizontalCutEdges_iff, fkRectVerticalSeamEdgeAt,
      fkRectRowZeroVertex]



theorem fkRectForceDualPullbackUnitPattern_attachment_eq
    (R : FKRectTorus) (omega : R.Configuration) :
    fkRectForceIndexedPattern R
        (fkRectDualPullbackIndexSet R (fkRectHorizontalCutEdges R))
        (fkRectDualPullbackConfiguration R
          (fkRectAllButOneOpenConfiguration R
            (fkRectUnitLeftBarrierGap R))) omega
        (fkRectRowZeroAttachmentEdgeAt R (fkRectUnitGapColumn R)) =
      omega (fkRectRowZeroAttachmentEdgeAt R (fkRectUnitGapColumn R)) := by
  rw [fkRectDualPullbackIndexSet_horizontalCutEdges,
    fkRectForceIndexedPattern_of_not_mem]
  simp [mem_fkRectHorizontalCutEdges_iff,
    fkRectRowZeroAttachmentEdgeAt, fkRectRowOneVertex]



theorem fkRectForceDualPullbackUnitPattern_verticalWinding_of_chain
    (R : FKRectTorus) (omega : R.Configuration)
    (t : Finset (FKRectRightStripBandVertex R 1 1 (R.height - 1) ×
      FKRectRightStripBandVertex R 1 1 (R.height - 1)))
    (hpair :
      (fkRectRightBandRowOne R 1 (fkRectUnitGapColumn R) (by rfl),
        fkRectRightBandLastRow R 1 (fkRectUnitGapColumn R) (by rfl)) ∈ t)
    (hchain :
      FK.ocd_innerRestrict
          (Subtype.val :
            FKRectRightStripBandVertex R 1 1 (R.height - 1) -> R.Vertex)
          (fkRectFullGraphConfiguration R omega) ∈
        fkRectInducedConnectionChainEvent R
          (fkRectRightStripBand R 1 1 (R.height - 1)) t)
    (hattach :
      omega (fkRectRowZeroAttachmentEdgeAt R
        (fkRectUnitGapColumn R)) = true) :
    fkRectForceIndexedPattern R
        (fkRectDualPullbackIndexSet R (fkRectHorizontalCutEdges R))
        (fkRectDualPullbackConfiguration R
          (fkRectAllButOneOpenConfiguration R
            (fkRectUnitLeftBarrierGap R))) omega ∈
      fkRectVerticalWindingEvent R := by
  let eta := fkRectDualPullbackConfiguration R
    (fkRectAllButOneOpenConfiguration R (fkRectUnitLeftBarrierGap R))
  let forced := fkRectForceIndexedPattern R
    (fkRectDualPullbackIndexSet R (fkRectHorizontalCutEdges R)) eta omega
  apply fkRectVerticalWindingEvent_of_rightBand_chain R 1
    (fkRectUnitGapColumn R) (by rfl) forced t hpair
  · exact fkRectForceDualPullbackSeam_preserves_rightBand_chain
      R 1 1 (R.height - 1) (by rfl) eta omega t hchain
  · exact fkRectForceDualPullbackUnitPattern_verticalSeam_open R omega
  · dsimp [forced, eta]
    rw [fkRectForceDualPullbackUnitPattern_attachment_eq]
    exact hattach

end

end StatMech.FrontierD
