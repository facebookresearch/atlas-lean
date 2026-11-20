/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/




import Code.FrontierA.KacWardAngularPortPhase
import Code.FrontierA.KacWardAngularSplitUnitCycleReduction
import Code.FrontierA.KacWardAdaptiveClosure





namespace StatMech.FrontierA

open SimpleGraph




theorem kwAngularSplitCyclePhaseSign_adaptive
    {V : Type*} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj]
    (embedding : KWStraightLineEmbedding G) :
    KWAngularSplitCyclePhaseSign embedding := by
  classical
  obtain ⟨data⟩ := embedding.exists_angularPortRadiusData
  intro root p hp
  letI : NeZero p.darts.length :=
    ⟨Nat.ne_of_gt (List.length_pos_of_ne_nil
      (SimpleGraph.Walk.darts_eq_nil.not.mpr hp.not_nil))⟩
  let split := kwOrderedDartPortSplitGraph G (kwAngularPortOrder embedding)
  let loop := kwGraphCycleDartLoop p
  have hvalid : kwGraphLoopNonbacktracking split loop :=
    kwGraphCycleDartLoop_nonbacktracking split p hp
  have hgauge := kwGraphLoopScalar_phaseGauge split
    (kwAngularSplitPhase embedding) data.phaseGauge
    data.phaseGauge_ne_zero loop
  rw [kwGraphCycleDartLoop_scalar_eq_phaseProduct split
      (kwPhaseGauge data.phaseGauge (kwAngularSplitPhase embedding)) p hp,
    kwGraphCycleDartLoop_scalar_eq_phaseProduct split
      (kwAngularSplitPhase embedding) p hp] at hgauge
  have hrealized :
      kwLoopPhaseProduct
          (kwPhaseGauge data.phaseGauge (kwAngularSplitPhase embedding)) loop =
        kwLoopPhaseProduct data.toStraightLineEmbedding.turnPhase loop := by
    unfold kwLoopPhaseProduct
    apply Finset.prod_congr rfl
    intro k _
    exact (data.realizedTurnPhase_eq_phaseGauge
      (loop k) (loop (k + 1)) (hvalid k).1 (hvalid k).2).symm
  calc
    kwLoopPhaseProduct (kwAngularSplitPhase embedding) loop =
        kwLoopPhaseProduct
          (kwPhaseGauge data.phaseGauge (kwAngularSplitPhase embedding)) loop :=
      hgauge.symm
    _ = kwLoopPhaseProduct data.toStraightLineEmbedding.turnPhase loop :=
      hrealized
    _ = -1 := kwStraightLineCyclePhaseSign_adaptive
      data.toStraightLineEmbedding p hp



theorem kacWard_straightLine_arbitrary_adaptive
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (embedding : KWStraightLineEmbedding G)
    (weight : Sym2 V → ℂ) :
    (1 - kwGraphTransition G weight embedding.turnPhase).det =
      (kwEvenPolynomial G weight) ^ 2 :=
  kacWard_original_of_angularSplit_cyclePhaseSign embedding weight
    (kwAngularSplitCyclePhaseSign_adaptive embedding)

end StatMech.FrontierA
