/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/




import Code.FrontierD.FKRectDualRankOneWinding
import Code.FrontierD.FKRectTorusNetFull



open SimpleGraph

namespace StatMech.FrontierD

noncomputable section




def fkRectDualBarrierNetObstructionConfiguration (R : FKRectTorus) :
    R.Configuration :=
  fkRectDualPullbackConfiguration R
    (fkRectUnitLeftBarrierConfiguration R)

@[simp] theorem fkRectDualConfigurationEquiv_dualPullbackConfiguration
    (R : FKRectTorus) (eta : R.Configuration) :
    fkRectDualConfigurationEquiv R
        (fkRectDualPullbackConfiguration R eta) = eta := by
  funext e
  rw [fkRectDualConfigurationEquiv_apply]
  simp [fkRectDualPullbackConfiguration]

theorem fkRectDualBarrierNetObstruction_dual_mem_source
    (R : FKRectTorus) :
    fkRectDualConfigurationEquiv R
        (fkRectDualBarrierNetObstructionConfiguration R) ∈
      fkRectSourceLeftBarrier R 1 (fkRectUnitLeftBarrierGap R) := by
  rw [fkRectDualBarrierNetObstructionConfiguration,
    fkRectDualConfigurationEquiv_dualPullbackConfiguration]
  exact fkRectUnitLeftBarrierConfiguration_mem_source R

private theorem fkRectDualBarrierNetObstruction_vertical_open
    (R : FKRectTorus) (y : Fin R.height) :
    fkRectDualBarrierNetObstructionConfiguration R
        (true, (fkRectUnitGapColumn R, y)) = true := by
  unfold fkRectDualBarrierNetObstructionConfiguration
    fkRectDualPullbackConfiguration
  simp only [fkRectEdgeToDualEdge, Bool.true_eq, if_true]
  by_cases hy : y.val = 0
  · have hey : (false, (fkRectUnitGapColumn R, y)) =
        fkRectUnitLeftBarrierGap R := by
      rcases y with ⟨yv, hyv⟩
      apply Prod.ext
      · rfl
      · apply Prod.ext
        · rfl
        · apply Fin.ext
          exact hy
    rw [hey]
    rw [fkRectAllButOneOpenSeamEvent_gap_closed R
      (fkRectUnitLeftBarrierGap_mem R)
      (fkRectUnitLeftBarrierConfiguration_seam R)]
    rfl
  · have hnot : (false, (fkRectUnitGapColumn R, y)) ∉
        fkRectHorizontalCutEdges R := by
      simpa [mem_fkRectHorizontalCutEdges_iff] using hy
    have herase : (false, (fkRectUnitGapColumn R, y)) ∉
        (fkRectHorizontalCutEdges R).erase
          (fkRectUnitLeftBarrierGap R) := by
      exact fun h => hnot (Finset.mem_erase.mp h).2
    simp [fkRectUnitLeftBarrierConfiguration,
      fkRectConfigurationOfEdges, herase]

private theorem fkRectDualBarrierNetObstruction_verticalAdj
    (R : FKRectTorus) (y : Fin R.height) :
    (fkRectOpenGraph R
      (fkRectDualBarrierNetObstructionConfiguration R)).Adj
        (fkRectUnitGapColumn R, y)
        (fkRectUnitGapColumn R,
          SixVertexArrows.cyclicPred R.height_pos y) := by
  refine ⟨(true, (fkRectUnitGapColumn R, y)),
    fkRectDualBarrierNetObstruction_vertical_open R y, rfl⟩

private theorem fkRectDualBarrierNetObstruction_rowOneVerticalAdj
    (R : FKRectTorus) (x : Fin R.width) :
    (fkRectOpenGraph R
      (fkRectDualBarrierNetObstructionConfiguration R)).Adj
        (x, (⟨1, lt_trans Nat.one_lt_two R.height_gt_two⟩ : Fin R.height))
        (x, (⟨0, R.height_pos⟩ : Fin R.height)) := by
  let y1 : Fin R.height :=
    ⟨1, lt_trans Nat.one_lt_two R.height_gt_two⟩
  refine ⟨(true, (x, y1)), ?_, ?_⟩
  · unfold fkRectDualBarrierNetObstructionConfiguration
      fkRectDualPullbackConfiguration
    simp only [fkRectEdgeToDualEdge, Bool.true_eq, if_true]
    have hnot : (false, (x, y1)) ∉ fkRectHorizontalCutEdges R := by
      simp [mem_fkRectHorizontalCutEdges_iff, y1]
    have herase : (false, (x, y1)) ∉
        (fkRectHorizontalCutEdges R).erase
          (fkRectUnitLeftBarrierGap R) := by
      exact fun h => hnot (Finset.mem_erase.mp h).2
    simp [fkRectUnitLeftBarrierConfiguration,
      fkRectConfigurationOfEdges, herase]
  · have hpred : SixVertexArrows.cyclicPred R.height_pos y1 =
        (⟨0, R.height_pos⟩ : Fin R.height) := by
      apply Fin.ext
      rw [fkRectCyclicPred_val]
      simp [y1]
    simpa [fkRectTorusIndexedEdge, y1, hpred]

private theorem fkRectDualBarrierNetObstruction_rowOneDiagonalAdj
    (R : FKRectTorus) (x : Fin R.width) :
    (fkRectOpenGraph R
      (fkRectDualBarrierNetObstructionConfiguration R)).Adj
        (x, (⟨0, R.height_pos⟩ : Fin R.height))
        (SixVertexArrows.cyclicPred R.width_pos x,
          (⟨1, lt_trans Nat.one_lt_two R.height_gt_two⟩ : Fin R.height)) := by
  let y1 : Fin R.height :=
    ⟨1, lt_trans Nat.one_lt_two R.height_gt_two⟩
  refine ⟨(false, (x, y1)), ?_, ?_⟩
  · unfold fkRectDualBarrierNetObstructionConfiguration
      fkRectDualPullbackConfiguration
    simp only [fkRectEdgeToDualEdge, Bool.false_eq_true, if_false]
    have hnot :
        (true, (SixVertexArrows.cyclicPred R.width_pos x, y1)) ∉
          fkRectHorizontalCutEdges R := by
      simp [mem_fkRectHorizontalCutEdges_iff, y1]
    have herase :
        (true, (SixVertexArrows.cyclicPred R.width_pos x, y1)) ∉
          (fkRectHorizontalCutEdges R).erase
            (fkRectUnitLeftBarrierGap R) := by
      exact fun h => hnot (Finset.mem_erase.mp h).2
    simp [fkRectUnitLeftBarrierConfiguration,
      fkRectConfigurationOfEdges, herase]
  · have hpred : SixVertexArrows.cyclicPred R.height_pos y1 =
        (⟨0, R.height_pos⟩ : Fin R.height) := by
      apply Fin.ext
      rw [fkRectCyclicPred_val]
      simp [y1]
    simp [fkRectTorusIndexedEdge, y1, hpred]

private noncomputable def fkRectDualBarrierNetObstructionVerticalAux
    (R : FKRectTorus) :
    (n : Nat) →
      (fkRectOpenGraph R
        (fkRectDualBarrierNetObstructionConfiguration R)).Walk
        (fkRectUnitGapColumn R, (⟨0, R.height_pos⟩ : Fin R.height))
        (fkRectUnitGapColumn R,
          (SixVertexArrows.cyclicPred R.height_pos)^[n]
            (⟨0, R.height_pos⟩ : Fin R.height))
  | 0 => .nil
  | n + 1 =>
      (fkRectDualBarrierNetObstructionVerticalAux R n).concat
        (by
          have h := fkRectDualBarrierNetObstruction_verticalAdj R
            ((SixVertexArrows.cyclicPred R.height_pos)^[n]
              (⟨0, R.height_pos⟩ : Fin R.height))
          simpa only [Function.iterate_succ_apply'] using h)

private theorem fkRectDualBarrierNetObstructionVerticalAux_winding
    (R : FKRectTorus) (n : Nat) (hn : n ≤ R.height) :
    fkRectWalkWinding R
        (fkRectDualBarrierNetObstructionVerticalAux R n) =
      (0, if n = 0 then 0 else -1) := by
  induction n with
  | zero => rfl
  | succ n ih =>
      have hn' : n ≤ R.height := by omega
      rw [fkRectDualBarrierNetObstructionVerticalAux,
        fkRectWalkWinding_concat, ih hn']
      simp only [Function.iterate_succ_apply']
      rw [fkRectHorizontalSeamIncrement_same_fst,
        fkRectVerticalSeamIncrement_pred]
      have hval := fkRectCyclicPred_iterate_zero_val R.height_pos n hn'
      rw [hval]
      by_cases hzero : n = 0
      · simp [hzero]
      · have hnlt : n < R.height := by omega
        simp [hzero]
        omega

private noncomputable def fkRectDualBarrierNetObstructionVerticalWalk
    (R : FKRectTorus) :
    (fkRectOpenGraph R
      (fkRectDualBarrierNetObstructionConfiguration R)).Walk
      (fkRectUnitGapColumn R, (⟨0, R.height_pos⟩ : Fin R.height))
      (fkRectUnitGapColumn R, (⟨0, R.height_pos⟩ : Fin R.height)) :=
  (fkRectDualBarrierNetObstructionVerticalAux R R.height).copy rfl (by
    rw [fkRectCyclicPred_iterate_zero_card])

private noncomputable def fkRectDualBarrierNetObstructionHorizontalAux
    (R : FKRectTorus) :
    (n : Nat) →
      (fkRectOpenGraph R
        (fkRectDualBarrierNetObstructionConfiguration R)).Walk
        ((⟨0, R.width_pos⟩ : Fin R.width),
          (⟨1, lt_trans Nat.one_lt_two R.height_gt_two⟩ : Fin R.height))
        ((SixVertexArrows.cyclicPred R.width_pos)^[n]
            (⟨0, R.width_pos⟩ : Fin R.width),
          (⟨1, lt_trans Nat.one_lt_two R.height_gt_two⟩ : Fin R.height))
  | 0 => .nil
  | n + 1 =>
      ((fkRectDualBarrierNetObstructionHorizontalAux R n).concat
        (fkRectDualBarrierNetObstruction_rowOneVerticalAdj R
          ((SixVertexArrows.cyclicPred R.width_pos)^[n]
            (⟨0, R.width_pos⟩ : Fin R.width)))).concat
        (by
          have h := fkRectDualBarrierNetObstruction_rowOneDiagonalAdj R
            ((SixVertexArrows.cyclicPred R.width_pos)^[n]
              (⟨0, R.width_pos⟩ : Fin R.width))
          simpa only [Function.iterate_succ_apply'] using h)

private theorem fkRectDualBarrierNetObstructionHorizontalAux_winding
    (R : FKRectTorus) (n : Nat) (hn : n ≤ R.width) :
    fkRectWalkWinding R
        (fkRectDualBarrierNetObstructionHorizontalAux R n) =
      (if n = 0 then 0 else -1, 0) := by
  induction n with
  | zero => rfl
  | succ n ih =>
      have hn' : n ≤ R.width := by omega
      rw [fkRectDualBarrierNetObstructionHorizontalAux,
        fkRectWalkWinding_concat, fkRectWalkWinding_concat, ih hn']
      simp only [Function.iterate_succ_apply']
      have hfirstVertical :
          fkRectVerticalSeamIncrement R
            (((SixVertexArrows.cyclicPred R.width_pos)^[n]
                (⟨0, R.width_pos⟩ : Fin R.width),
              (⟨1, lt_trans Nat.one_lt_two R.height_gt_two⟩ : Fin R.height)))
            (((SixVertexArrows.cyclicPred R.width_pos)^[n]
                (⟨0, R.width_pos⟩ : Fin R.width),
              (⟨0, R.height_pos⟩ : Fin R.height))) = 0 := by
        unfold fkRectVerticalSeamIncrement
        have hheight := R.height_gt_two
        simp
        omega
      have hdiagVertical :
          fkRectVerticalSeamIncrement R
            (((SixVertexArrows.cyclicPred R.width_pos)^[n]
                (⟨0, R.width_pos⟩ : Fin R.width),
              (⟨0, R.height_pos⟩ : Fin R.height)))
            (SixVertexArrows.cyclicPred R.width_pos
                ((SixVertexArrows.cyclicPred R.width_pos)^[n]
                  (⟨0, R.width_pos⟩ : Fin R.width)),
              (⟨1, lt_trans Nat.one_lt_two R.height_gt_two⟩ : Fin R.height)) = 0 := by
        apply fkRectVerticalSeamIncrement_eq_zero_of_not_crosses
        rw [fkRectCrossesVerticalSeam_mk]
        have hheight := R.height_gt_two
        simp
        omega
      rw [fkRectHorizontalSeamIncrement_same_fst, hfirstVertical,
        fkRectHorizontalSeamIncrement_pred, hdiagVertical]
      have hval := fkRectCyclicPred_iterate_zero_val R.width_pos n hn'
      rw [hval]
      by_cases hzero : n = 0
      · simp [hzero]
      · have hnlt : n < R.width := by omega
        simp [hzero]
        omega

private noncomputable def fkRectDualBarrierNetObstructionHorizontalWalk
    (R : FKRectTorus) :
    (fkRectOpenGraph R
      (fkRectDualBarrierNetObstructionConfiguration R)).Walk
      ((⟨0, R.width_pos⟩ : Fin R.width),
        (⟨1, lt_trans Nat.one_lt_two R.height_gt_two⟩ : Fin R.height))
      ((⟨0, R.width_pos⟩ : Fin R.width),
        (⟨1, lt_trans Nat.one_lt_two R.height_gt_two⟩ : Fin R.height)) :=
  (fkRectDualBarrierNetObstructionHorizontalAux R R.width).copy rfl (by
    rw [fkRectCyclicPred_iterate_zero_card])

private theorem fkRectDualBarrierNetObstructionHorizontalWalk_winding
    (R : FKRectTorus) :
    fkRectWalkWinding R
        (fkRectDualBarrierNetObstructionHorizontalWalk R) = (-1, 0) := by
  unfold fkRectDualBarrierNetObstructionHorizontalWalk
  rw [fkRectWalkWinding_copy,
    fkRectDualBarrierNetObstructionHorizontalAux_winding R R.width le_rfl]
  simp [ne_of_gt R.width_pos]

private theorem fkRectDualBarrierNetObstructionVerticalWalk_winding
    (R : FKRectTorus) :
    fkRectWalkWinding R
        (fkRectDualBarrierNetObstructionVerticalWalk R) = (0, -1) := by
  unfold fkRectDualBarrierNetObstructionVerticalWalk
  rw [fkRectWalkWinding_copy,
    fkRectDualBarrierNetObstructionVerticalAux_winding R R.height le_rfl]
  simp [ne_of_gt R.height_pos]

private noncomputable def fkRectDualBarrierNetObstructionConnectionWalk
    (R : FKRectTorus) :
    (fkRectOpenGraph R
      (fkRectDualBarrierNetObstructionConfiguration R)).Walk
      ((⟨0, R.width_pos⟩ : Fin R.width),
        (⟨1, lt_trans Nat.one_lt_two R.height_gt_two⟩ : Fin R.height))
      (fkRectUnitGapColumn R,
        (⟨0, R.height_pos⟩ : Fin R.height)) := by
  have hpred :
      (SixVertexArrows.cyclicPred R.width_pos)^[R.width - 1]
          (⟨0, R.width_pos⟩ : Fin R.width) = fkRectUnitGapColumn R := by
    apply Fin.ext
    rw [fkRectCyclicPred_iterate_zero_val R.width_pos (R.width - 1)]
    · have hw := R.width_gt_two
      have hne : R.width - 1 ≠ 0 := by omega
      rw [if_neg hne]
      change R.width - (R.width - 1) = 1
      omega
    · omega
  let p := fkRectDualBarrierNetObstructionHorizontalAux R (R.width - 1)
  let p' := p.copy rfl (by rw [hpred])
  exact p'.concat
    (fkRectDualBarrierNetObstruction_rowOneVerticalAdj R
      (fkRectUnitGapColumn R))




theorem fkRectDualBarrierNetObstruction_hasNet (R : FKRectTorus) :
    FKRectHasNet R (fkRectDualBarrierNetObstructionConfiguration R) := by
  apply FKRectHasNet.of_connected_closedWalks R
    (fkRectDualBarrierNetObstructionConfiguration R)
    (fkRectDualBarrierNetObstructionConnectionWalk R).reachable
    (fkRectDualBarrierNetObstructionHorizontalWalk R)
    (fkRectDualBarrierNetObstructionVerticalWalk R)
  rw [fkRectDualBarrierNetObstructionHorizontalWalk_winding,
    fkRectDualBarrierNetObstructionVerticalWalk_winding]
  norm_num [FKRectWindingIndependent]



theorem fkRectDualBarrierNetObstruction_hasNet_and_dualNoCrossing
    (R : FKRectTorus) :
    FKRectHasNet R (fkRectDualBarrierNetObstructionConfiguration R) ∧
      fkRectDualBarrierNetObstructionConfiguration R ∈
        fkRectDualPreimageEvent R
          (fkRectNoLeftStripCrossingEvent R 1) := by
  exact ⟨fkRectDualBarrierNetObstruction_hasNet R,
    (fkRectDualBarrierNetObstruction_dual_mem_source R).1⟩

end

end StatMech.FrontierD
