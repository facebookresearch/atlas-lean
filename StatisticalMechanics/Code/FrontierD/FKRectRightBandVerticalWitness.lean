/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/




import Code.FrontierD.FKRectSourceSeamBarrier
import Code.FrontierD.FKRectTorusWindingEvent



open SimpleGraph

namespace StatMech.FrontierD

noncomputable section



theorem fkRectRightStripBand_connection_reachable_verticalCut
    (R : FKRectTorus) (cut lower upper : Nat) (hlower : 1 ≤ lower)
    (omega : R.Configuration)
    (x y : FKRectRightStripBandVertex R cut lower upper)
    (hxy :
      FK.ocd_innerRestrict
          (Subtype.val :
            FKRectRightStripBandVertex R cut lower upper → R.Vertex)
          (fkRectFullGraphConfiguration R omega) ∈
        FK.connEvent
          (fkRectInducedGraph R
            (fkRectRightStripBand R cut lower upper)) x y) :
    (fkRectVerticalCutGraph R omega).Reachable x.1 y.1 := by
  let f :
      FK.openSub
          (fkRectInducedGraph R
            (fkRectRightStripBand R cut lower upper))
          (FK.ocd_innerRestrict
            (Subtype.val :
              FKRectRightStripBandVertex R cut lower upper → R.Vertex)
            (fkRectFullGraphConfiguration R omega)) →g
        fkRectVerticalCutGraph R omega :=
    { toFun := Subtype.val
      map_rel' := by
        intro u v huv
        rw [fkRectVerticalCutGraph, SimpleGraph.deleteEdges_adj]
        constructor
        · rw [← fkOpenSub_fullGraphConfiguration R omega]
          constructor
          · exact huv.1
          · simpa [FK.ocd_innerRestrict, FK.ocd_innerEdge_mk] using huv.2
        · intro hseam
          change fkRectCrossesVerticalSeam R s(u.1, v.1) at hseam
          rw [fkRectCrossesVerticalSeam_mk] at hseam
          rcases hseam with hseam | hseam
          · exact (Nat.ne_of_gt (Nat.zero_lt_one.trans_le
              (hlower.trans u.2.2.1))) hseam.1
          · exact (Nat.ne_of_gt (Nat.zero_lt_one.trans_le
              (hlower.trans v.2.2.1))) hseam.1 }
  exact hxy.map f

def fkRectRowZeroVertex (R : FKRectTorus) (x : Fin R.width) : R.Vertex :=
  (x, ⟨0, R.height_pos⟩)

def fkRectRowOneVertex (R : FKRectTorus) (x : Fin R.width) : R.Vertex :=
  (x, ⟨1, lt_trans Nat.one_lt_two R.height_gt_two⟩)

def fkRectLastRowVertex (R : FKRectTorus) (x : Fin R.width) : R.Vertex :=
  (x, svFinLast R.height_pos)


def fkRectVerticalSeamEdgeAt (R : FKRectTorus)
    (x : Fin R.width) : R.EdgeIndex :=
  (true, fkRectRowZeroVertex R x)


def fkRectRowZeroAttachmentEdgeAt (R : FKRectTorus)
    (x : Fin R.width) : R.EdgeIndex :=
  (true, fkRectRowOneVertex R x)

theorem fkRectVerticalSeamEdgeAt_indexedEdge
    (R : FKRectTorus) (x : Fin R.width) :
    fkRectTorusIndexedEdge R (fkRectVerticalSeamEdgeAt R x) =
      s(fkRectRowZeroVertex R x, fkRectLastRowVertex R x) := by
  simp [fkRectVerticalSeamEdgeAt, fkRectRowZeroVertex,
    fkRectLastRowVertex, fkRectTorusIndexedEdge, svCyclicPred_zero]

theorem fkRectRowZeroAttachmentEdgeAt_indexedEdge
    (R : FKRectTorus) (x : Fin R.width) :
    fkRectTorusIndexedEdge R (fkRectRowZeroAttachmentEdgeAt R x) =
      s(fkRectRowOneVertex R x, fkRectRowZeroVertex R x) := by
  unfold fkRectRowZeroAttachmentEdgeAt fkRectRowOneVertex
  simp only [fkRectTorusIndexedEdge, if_true]
  rw [show SixVertexArrows.cyclicPred R.height_pos
      (⟨1, lt_trans Nat.one_lt_two R.height_gt_two⟩ : Fin R.height) =
        (⟨0, R.height_pos⟩ : Fin R.height) by
    apply Fin.ext
    rw [fkRectCyclicPred_val]
    simp]
  rfl

theorem fkRectVerticalSeamEdgeAt_crosses
    (R : FKRectTorus) (x : Fin R.width) :
    fkRectCrossesVerticalSeam R
      (fkRectTorusIndexedEdge R (fkRectVerticalSeamEdgeAt R x)) := by
  apply fkRectHorizontalCutEdge_crossesVerticalSeam
  simp [mem_fkRectHorizontalCutEdges_iff, fkRectVerticalSeamEdgeAt,
    fkRectRowZeroVertex]

theorem fkRectRowZeroAttachmentEdgeAt_not_crosses
    (R : FKRectTorus) (x : Fin R.width) :
    ¬ fkRectCrossesVerticalSeam R
      (fkRectTorusIndexedEdge R
        (fkRectRowZeroAttachmentEdgeAt R x)) := by
  rw [fkRectRowZeroAttachmentEdgeAt_indexedEdge,
    fkRectCrossesVerticalSeam_mk]
  change ¬ ((1 = 0 ∧ 0 + 1 = R.height) ∨
    (0 = 0 ∧ 1 + 1 = R.height))
  have hheight := R.height_gt_two
  omega


def fkRectRightBandRowOne
    (R : FKRectTorus) (cut : Nat) (x : Fin R.width)
    (hx : cut ≤ x.val) :
    FKRectRightStripBandVertex R cut 1 (R.height - 1) :=
  ⟨fkRectRowOneVertex R x, by
    change cut ≤ x.val ∧ 1 ≤ 1 ∧ 1 ≤ R.height - 1
    exact ⟨hx, le_rfl, by
      have hheight := R.height_gt_two
      omega⟩⟩

def fkRectRightBandLastRow
    (R : FKRectTorus) (cut : Nat) (x : Fin R.width)
    (hx : cut ≤ x.val) :
    FKRectRightStripBandVertex R cut 1 (R.height - 1) :=
  ⟨fkRectLastRowVertex R x, by
    change cut ≤ x.val ∧ 1 ≤ (svFinLast R.height_pos).val ∧
      (svFinLast R.height_pos).val ≤ R.height - 1
    refine ⟨hx, ?_, ?_⟩
    · simp [svFinLast]
      have hheight := R.height_gt_two
      omega
    · simp [svFinLast]⟩



theorem fkRectRightBand_chain_reachable_verticalCut
    (R : FKRectTorus) (cut : Nat) (x : Fin R.width)
    (hx : cut ≤ x.val) (omega : R.Configuration)
    (t : Finset (FKRectRightStripBandVertex R cut 1 (R.height - 1) ×
      FKRectRightStripBandVertex R cut 1 (R.height - 1)))
    (hpair : (fkRectRightBandRowOne R cut x hx,
      fkRectRightBandLastRow R cut x hx) ∈ t)
    (hchain :
      FK.ocd_innerRestrict
          (Subtype.val :
            FKRectRightStripBandVertex R cut 1 (R.height - 1) → R.Vertex)
          (fkRectFullGraphConfiguration R omega) ∈
        fkRectInducedConnectionChainEvent R
          (fkRectRightStripBand R cut 1 (R.height - 1)) t) :
    (fkRectVerticalCutGraph R omega).Reachable
      (fkRectRowOneVertex R x) (fkRectLastRowVertex R x) := by
  apply fkRectRightStripBand_connection_reachable_verticalCut
    R cut 1 (R.height - 1) (by omega) omega
      (fkRectRightBandRowOne R cut x hx)
      (fkRectRightBandLastRow R cut x hx)
  exact hchain _ hpair



theorem fkRectVerticalWindingEvent_of_rightBand_chain
    (R : FKRectTorus) (cut : Nat) (x : Fin R.width)
    (hx : cut ≤ x.val) (omega : R.Configuration)
    (t : Finset (FKRectRightStripBandVertex R cut 1 (R.height - 1) ×
      FKRectRightStripBandVertex R cut 1 (R.height - 1)))
    (hpair : (fkRectRightBandRowOne R cut x hx,
      fkRectRightBandLastRow R cut x hx) ∈ t)
    (hchain :
      FK.ocd_innerRestrict
          (Subtype.val :
            FKRectRightStripBandVertex R cut 1 (R.height - 1) → R.Vertex)
          (fkRectFullGraphConfiguration R omega) ∈
        fkRectInducedConnectionChainEvent R
          (fkRectRightStripBand R cut 1 (R.height - 1)) t)
    (hseam : omega (fkRectVerticalSeamEdgeAt R x) = true)
    (hattach : omega (fkRectRowZeroAttachmentEdgeAt R x) = true) :
    omega ∈ fkRectVerticalWindingEvent R := by
  let v0 := fkRectRowZeroVertex R x
  let v1 := fkRectRowOneVertex R x
  let vt := fkRectLastRowVertex R x
  have hseamAdj : (fkRectOpenGraph R omega).Adj v0 vt := by
    refine ⟨fkRectVerticalSeamEdgeAt R x, hseam, ?_⟩
    exact fkRectVerticalSeamEdgeAt_indexedEdge R x
  have hattachAdj : (fkRectVerticalCutGraph R omega).Adj v0 v1 := by
    rw [fkRectVerticalCutGraph, SimpleGraph.deleteEdges_adj]
    constructor
    · refine ⟨fkRectRowZeroAttachmentEdgeAt R x, hattach, ?_⟩
      rw [fkRectRowZeroAttachmentEdgeAt_indexedEdge]
      exact Sym2.eq_swap
    · intro hcross
      apply fkRectRowZeroAttachmentEdgeAt_not_crosses R x
      rw [fkRectRowZeroAttachmentEdgeAt_indexedEdge]
      simpa only [Sym2.eq_swap] using hcross
  have hband : (fkRectVerticalCutGraph R omega).Reachable v1 vt := by
    exact fkRectRightBand_chain_reachable_verticalCut
      R cut x hx omega t hpair hchain
  refine ⟨v0, vt, hseamAdj, ?_, hattachAdj.reachable.trans hband⟩
  rw [← fkRectVerticalSeamEdgeAt_indexedEdge R x]
  exact fkRectVerticalSeamEdgeAt_crosses R x

end

end StatMech.FrontierD
