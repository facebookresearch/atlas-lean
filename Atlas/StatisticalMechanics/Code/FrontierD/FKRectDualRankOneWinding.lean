/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/




import Code.FrontierD.FKRectMedialDualWinding
import Code.FrontierD.FKRectDualBarrierForceTopology
import Code.FrontierD.FKRectSourceSeamWindingUpper



namespace StatMech.FrontierD

noncomputable section



theorem fkRectVerticalRankOne_dualPreimageAllButOne_subset_windingOne
    (R : FKRectTorus) (gap : R.EdgeIndex) :
    fkRectVerticalRankOneEvent R ∩
        fkRectDualPreimageEvent R
          (fkRectAllButOneOpenSeamEvent R gap) ⊆
      {omega | fkRectUnorientedVerticalWindingNumber R omega = 1} := by
  intro omega homega
  have hlower : 1 ≤ fkRectUnorientedVerticalWindingNumber R omega :=
    fkRectVerticalRankOneEvent_subset_windingTail R homega.1
  have hupperDual :
      fkRectUnorientedVerticalWindingNumber R
          (fkRectDualConfigurationEquiv R omega) ≤ 1 :=
    fkRectUnorientedVerticalWindingNumber_le_one_of_allButOneOpenSeam
      R homega.2
  have hupper : fkRectUnorientedVerticalWindingNumber R omega ≤ 1 := by
    rwa [fkRectUnorientedVerticalWindingNumber_dual] at hupperDual
  exact le_antisymm hupper hlower





theorem fkRectForceDualPullbackUnitPattern_windingOne_of_not_hasNet
    (R : FKRectTorus) (right : Nat) (hright : 1 ≤ right)
    (hproper : right + 1 < R.width)
    (omega : R.Configuration)
    (t : Finset
      (FKRectColumnBandVertex R 1 right 1 (R.height - 1) ×
        FKRectColumnBandVertex R 1 right 1 (R.height - 1)))
    (hspans : FKRectColumnBandConnectionChainSpans R 1 right
      (fkRectUnitGapColumn R) (by rfl) hright t)
    (haux : fkRectUnitDualBarrierAuxiliary R right t omega)
    (hnoNet :
      let forced := fkRectForceIndexedPattern R
        (fkRectDualPullbackIndexSet R (fkRectHorizontalCutEdges R))
        (fkRectDualPullbackConfiguration R
          (fkRectAllButOneOpenConfiguration R
            (fkRectUnitLeftBarrierGap R))) omega
      ¬ FKRectHasNet R forced) :
    let forced := fkRectForceIndexedPattern R
      (fkRectDualPullbackIndexSet R (fkRectHorizontalCutEdges R))
      (fkRectDualPullbackConfiguration R
        (fkRectAllButOneOpenConfiguration R
          (fkRectUnitLeftBarrierGap R))) omega
    fkRectUnorientedVerticalWindingNumber R forced = 1 := by
  dsimp only at hnoNet ⊢
  let forced := fkRectForceIndexedPattern R
    (fkRectDualPullbackIndexSet R (fkRectHorizontalCutEdges R))
    (fkRectDualPullbackConfiguration R
      (fkRectAllButOneOpenConfiguration R
        (fkRectUnitLeftBarrierGap R))) omega
  have hvertical : forced ∈ fkRectVerticalWindingEvent R :=
    (fkRectForceDualPullbackUnitPattern_verticalWinding_of_columnBandSpans
      R right hright omega t hspans haux).1
  have hnoCrossing : forced ∈ fkRectDualPreimageEvent R
      (fkRectNoLeftStripCrossingEvent R right) :=
    fkRectForceDualPullbackUnitPattern_mem_dualPreimage_noLeftStripCrossing
      R right hright hproper omega t hspans haux
  have hpullback : forced ∈ fkRectDualPullbackSourceLeftBarrier R right
      (fkRectUnitLeftBarrierGap R) := by
    rw [fkRectDualPullbackSourceLeftBarrier_eq]
    refine ⟨hnoCrossing, ?_⟩
    intro edge hedge
    exact fkRectForceIndexedPattern_of_mem R _ omega hedge
  have hdualSeam : forced ∈ fkRectDualPreimageEvent R
      (fkRectAllButOneOpenSeamEvent R (fkRectUnitLeftBarrierGap R)) := by
    exact hpullback.2
  exact fkRectVerticalRankOne_dualPreimageAllButOne_subset_windingOne
    R (fkRectUnitLeftBarrierGap R) ⟨⟨hvertical, hnoNet⟩, hdualSeam⟩

end

end StatMech.FrontierD
