/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/




import Code.FrontierD.FKRectRightBandVerticalWitness



namespace StatMech.FrontierD

noncomputable section



def fkRectAugmentedSourcePatternEdges (R : FKRectTorus)
    (x : Fin R.width) : Finset R.EdgeIndex :=
  fkRectHorizontalCutEdges R ∪ {fkRectRowZeroAttachmentEdgeAt R x}




def fkRectAugmentedSourceBarrier (R : FKRectTorus)
    (leftRight : Nat) (gap : R.EdgeIndex) (x : Fin R.width) :
    Set R.Configuration :=
  fkRectLeftBarrierWithSeamPattern R leftRight
    (fkRectAugmentedSourcePatternEdges R x)
    (fkRectAllButOneOpenConfiguration R gap)

theorem fkRectAugmentedSourcePatternEdges_outsideRightBand
    (R : FKRectTorus) (cut : Nat) (x : Fin R.width)
    (a : R.EdgeIndex) (ha : a ∈ fkRectAugmentedSourcePatternEdges R x) :
    fkRectTorusIndexedEdge R a ∉
      Set.range (FK.ocd_innerEdge
        (Subtype.val :
          FKRectRightStripBandVertex R cut 1 (R.height - 1) → R.Vertex)) := by
  rw [fkRectAugmentedSourcePatternEdges, Finset.mem_union] at ha
  rcases ha with hseam | hattach
  · exact fkRect_verticalSeam_not_rightStripBand_innerEdgeRange
      R cut 1 (R.height - 1) (by omega)
        (fkRectHorizontalCutEdge_crossesVerticalSeam R a hseam)
  · have haeq : a = fkRectRowZeroAttachmentEdgeAt R x := by
      simpa using hattach
    subst a
    rw [fkRectRowZeroAttachmentEdgeAt_indexedEdge,
      fkRect_innerEdge_subtype_mk_mem_range_iff]
    intro hboth
    have hzero := hboth.2.2.1
    change 1 ≤ 0 at hzero
    omega

theorem fkRectAugmentedSourceBarrier_dependsOnOutsideRightBand
    (R : FKRectTorus) (leftRight cut : Nat)
    (hsep : leftRight < cut) (gap : R.EdgeIndex) (x : Fin R.width) :
    FKRectDependsOnOutsideRegion R
      (fkRectRightStripBand R cut 1 (R.height - 1))
      (fkRectAugmentedSourceBarrier R leftRight gap x) := by
  apply FKRectDependsOnOutsideRegion.inter
  · exact fkRectNoLeftStripCrossing_dependsOnOutsideRightStripBand
      R leftRight cut 1 (R.height - 1) hsep
  · apply fkRectIndexedPatternEvent_dependsOnOutsideRegion
    exact fkRectAugmentedSourcePatternEdges_outsideRightBand R cut x



theorem fkRectAugmentedSourceBarrier_witnessEdges_open
    (R : FKRectTorus) (leftRight : Nat)
    {gap : R.EdgeIndex} (hgap : gap ∈ fkRectHorizontalCutEdges R)
    (x : Fin R.width)
    (hchosen : fkRectVerticalSeamEdgeAt R x ≠ gap)
    {omega : R.Configuration}
    (homega : omega ∈
      fkRectAugmentedSourceBarrier R leftRight gap x) :
    omega (fkRectVerticalSeamEdgeAt R x) = true ∧
      omega (fkRectRowZeroAttachmentEdgeAt R x) = true := by
  have hpattern := homega.2
  have hseamMem : fkRectVerticalSeamEdgeAt R x ∈
      fkRectAugmentedSourcePatternEdges R x := by
    apply Finset.mem_union_left
    simp [mem_fkRectHorizontalCutEdges_iff, fkRectVerticalSeamEdgeAt,
      fkRectRowZeroVertex]
  have hattachMem : fkRectRowZeroAttachmentEdgeAt R x ∈
      fkRectAugmentedSourcePatternEdges R x := by
    apply Finset.mem_union_right
    simp
  have hattachNotCut : fkRectRowZeroAttachmentEdgeAt R x ∉
      fkRectHorizontalCutEdges R := by
    simp [mem_fkRectHorizontalCutEdges_iff,
      fkRectRowZeroAttachmentEdgeAt, fkRectRowOneVertex]
  have hattachNe : fkRectRowZeroAttachmentEdgeAt R x ≠ gap := by
    intro h
    apply hattachNotCut
    rw [h]
    exact hgap
  constructor
  · simpa [fkRectAllButOneOpenConfiguration, hchosen] using
      hpattern (fkRectVerticalSeamEdgeAt R x) hseamMem
  · simpa [fkRectAllButOneOpenConfiguration, hattachNe] using
      hpattern (fkRectRowZeroAttachmentEdgeAt R x) hattachMem



def fkRectAugmentedBarrierConnectionEvent
    (R : FKRectTorus) (leftRight cut : Nat)
    (gap : R.EdgeIndex) (x : Fin R.width)
    (t : Finset (FKRectRightStripBandVertex R cut 1 (R.height - 1) ×
      FKRectRightStripBandVertex R cut 1 (R.height - 1))) :
    Set (ConfigSpace (Sym2 R.Vertex)) :=
  (FK.ocd_innerRestrict
      (Subtype.val :
        FKRectRightStripBandVertex R cut 1 (R.height - 1) → R.Vertex) ⁻¹'
        fkRectInducedConnectionChainEvent R
          (fkRectRightStripBand R cut 1 (R.height - 1)) t) ∩
    fkRectFullGraphEvent R
      (fkRectAugmentedSourceBarrier R leftRight gap x)

theorem fkRectAugmentedSource_barrierConnectionProduct_le
    (R : FKRectTorus) (leftRight cut : Nat) (hsep : leftRight < cut)
    {q : Real} (hq : 1 ≤ q) (gap : R.EdgeIndex) (x : Fin R.width)
    (t : Finset (FKRectRightStripBandVertex R cut 1 (R.height - 1) ×
      FKRectRightStripBandVertex R cut 1 (R.height - 1))) :
    (∏ xy ∈ t,
        FK.twoPointFun
          (fkRectInducedGraph R
            (fkRectRightStripBand R cut 1 (R.height - 1)))
          (fkRectCriticalP q) q xy.1 xy.2) *
        fkRectCriticalEventMass R q
          (fkRectAugmentedSourceBarrier R leftRight gap x) ≤
      ∑ rho,
        (fkRectAugmentedBarrierConnectionEvent R
          leftRight cut gap x t).indicator (fun _ => (1 : Real)) rho *
          FK.fkProb (fkRectTorusGraph R)
            (fkRectCriticalP q) q rho := by
  exact fkRectRightStripBand_connectionProduct_mul_outsideMass_le_genericInter
    R cut 1 (R.height - 1) hq t
      (fkRectAugmentedSourceBarrier_dependsOnOutsideRightBand
        R leftRight cut hsep gap x)

end

end StatMech.FrontierD
