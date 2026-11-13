/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/




import Code.FrontierD.FKRectDualBarrierLocalizedWalk
import Code.FrontierD.FKRectLeftStripNoNet



open SimpleGraph

namespace StatMech.FrontierD

noncomputable section



theorem fkRectWalkWinding_eq_zero_of_support_in_positiveColumnBand
    (R : FKRectTorus) (right : Nat) (_hright : right + 1 < R.width)
    {omega : R.Configuration} {x y : R.Vertex}
    (w : (fkRectOpenGraph R omega).Walk x y)
    (hsupport : ∀ v ∈ w.support,
      1 <= v.1.val ∧ v.1.val <= right ∧
        1 <= v.2.val ∧ v.2.val <= R.height - 1) :
    fkRectWalkWinding R w = (0, 0) := by
  induction w with
  | nil => rfl
  | @cons u v z huv w ih =>
      have hu := hsupport u (by simp)
      have hv := hsupport v (by simp)
      have htail : ∀ a ∈ w.support,
          1 <= a.1.val ∧ a.1.val <= right ∧
            1 <= a.2.val ∧ a.2.val <= R.height - 1 := by
        intro a ha
        apply hsupport a
        simp [ha]
      have hh : ¬ fkRectCrossesHorizontalSeam R s(u, v) := by
        rw [fkRectCrossesHorizontalSeam_mk]
        push Not
        constructor <;> omega
      have hvv : ¬ fkRectCrossesVerticalSeam R s(u, v) := by
        rw [fkRectCrossesVerticalSeam_mk]
        push Not
        constructor <;> omega
      simp only [fkRectWalkWinding]
      rw [fkRectHorizontalSeamIncrement_eq_zero_of_not_crosses_leftStrip
          R u v hh,
        fkRectVerticalSeamIncrement_eq_zero_of_not_crosses R u v hvv,
        ih htail]
      rfl




theorem exists_fkRectForceDualPullbackUnitPattern_localizedVerticalCycle
    (R : FKRectTorus) (right : Nat) (hright : 1 <= right)
    (hproper : right + 1 < R.width)
    (omega : R.Configuration)
    (t : Finset
      (FKRectColumnBandVertex R 1 right 1 (R.height - 1) ×
        FKRectColumnBandVertex R 1 right 1 (R.height - 1)))
    (hspans : FKRectColumnBandConnectionChainSpans R 1 right
      (fkRectUnitGapColumn R) (by rfl) hright t)
    (haux : fkRectUnitDualBarrierAuxiliary R right t omega) :
    let forced := fkRectForceIndexedPattern R
      (fkRectDualPullbackIndexSet R (fkRectHorizontalCutEdges R))
      (fkRectDualPullbackConfiguration R
        (fkRectAllButOneOpenConfiguration R
          (fkRectUnitLeftBarrierGap R))) omega
    ∃ z : (fkRectOpenGraph R forced).Walk
        (fkRectRowOneVertex R (fkRectUnitGapColumn R))
        (fkRectRowOneVertex R (fkRectUnitGapColumn R)),
      fkRectWalkWinding R z = (0, 1) ∧
      ∀ v ∈ z.support, 1 <= v.1.val ∧ v.1.val <= right := by
  dsimp only
  let eta := fkRectDualPullbackConfiguration R
    (fkRectAllButOneOpenConfiguration R (fkRectUnitLeftBarrierGap R))
  let forced := fkRectForceIndexedPattern R
    (fkRectDualPullbackIndexSet R (fkRectHorizontalCutEdges R)) eta omega
  obtain ⟨w, hwSupport⟩ :=
    exists_fkRectForceDualPullbackUnitPattern_localizedVerticalWalk
      R right hright omega t hspans haux
  let x := fkRectUnitGapColumn R
  let v0 := fkRectRowZeroVertex R x
  let v1 := fkRectRowOneVertex R x
  let vt := fkRectLastRowVertex R x
  have hseamOpen : forced (fkRectVerticalSeamEdgeAt R x) = true := by
    dsimp [forced, eta, x]
    exact fkRectForceDualPullbackUnitPattern_verticalSeam_open R omega
  have hattachOpen : forced (fkRectRowZeroAttachmentEdgeAt R x) = true := by
    dsimp [forced, eta, x]
    rw [fkRectForceDualPullbackUnitPattern_attachment_eq]
    exact haux.2
  have hseamAdj : (fkRectOpenGraph R forced).Adj vt v0 := by
    refine ⟨fkRectVerticalSeamEdgeAt R x, hseamOpen, ?_⟩
    rw [fkRectVerticalSeamEdgeAt_indexedEdge]
    exact Sym2.eq_swap
  have hattachAdj : (fkRectOpenGraph R forced).Adj v0 v1 := by
    refine ⟨fkRectRowZeroAttachmentEdgeAt R x, hattachOpen, ?_⟩
    rw [fkRectRowZeroAttachmentEdgeAt_indexedEdge]
    exact Sym2.eq_swap
  let z := (w.concat hseamAdj).concat hattachAdj
  have hwZero : fkRectWalkWinding R w = (0, 0) := by
    apply fkRectWalkWinding_eq_zero_of_support_in_positiveColumnBand
      R right hproper w
    exact hwSupport
  have hseamHorizontal :
      fkRectHorizontalSeamIncrement R vt v0 = 0 := by
    exact fkRectHorizontalSeamIncrement_same_fst R x _ _
  have hattachHorizontal :
      fkRectHorizontalSeamIncrement R v0 v1 = 0 := by
    exact fkRectHorizontalSeamIncrement_same_fst R x _ _
  have hseamVertical : fkRectVerticalSeamIncrement R vt v0 = 1 := by
    have hlast : vt =
        (x, SixVertexArrows.cyclicPred R.height_pos
          (⟨0, R.height_pos⟩ : Fin R.height)) := by
      apply Prod.ext
      · rfl
      · apply Fin.ext
        simp [vt, fkRectLastRowVertex, svFinLast, fkRectCyclicPred_val]
    rw [hlast]
    exact fkRectVerticalSeamIncrement_pred_zero_reverse R x x
  have hattachVertical : fkRectVerticalSeamIncrement R v0 v1 = 0 := by
    apply fkRectVerticalSeamIncrement_eq_zero_of_not_crosses
    rw [fkRectCrossesVerticalSeam_mk]
    dsimp [v0, v1, fkRectRowZeroVertex, fkRectRowOneVertex]
    have hheight := R.height_gt_two
    omega
  refine ⟨z, ?_, ?_⟩
  · dsimp [z]
    rw [fkRectWalkWinding_concat, fkRectWalkWinding_concat, hwZero]
    rw [hseamHorizontal, hattachHorizontal, hseamVertical,
      hattachVertical]
    rfl
  · intro v hv
    dsimp [z] at hv
    simp only [Walk.support_concat, List.mem_append, List.mem_singleton] at hv
    rcases hv with (hv | rfl) | rfl
    · exact ⟨(hwSupport v hv).1, (hwSupport v hv).2.1⟩
    · change 1 <= x.val ∧ x.val <= right
      exact ⟨by simp [x, fkRectUnitGapColumn], hright⟩
    · change 1 <= x.val ∧ x.val <= right
      exact ⟨by simp [x, fkRectUnitGapColumn], hright⟩

end

end StatMech.FrontierD
