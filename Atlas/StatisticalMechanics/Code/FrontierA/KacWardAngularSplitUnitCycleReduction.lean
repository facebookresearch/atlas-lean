/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/




import Code.FrontierA.KacWardAngularSplitCycleReversal









namespace StatMech.FrontierA

open SimpleGraph


def KWAngularSplitCyclePhaseSign
    {V : Type*} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj]
    (embedding : KWStraightLineEmbedding G) : Prop :=
  ∀ {root : KWDartPort G}
    (p : (kwOrderedDartPortSplitGraph G
      (kwAngularPortOrder embedding)).Walk root root),
    (hp : p.IsCycle) →
      letI : NeZero p.darts.length :=
        ⟨Nat.ne_of_gt (List.length_pos_of_ne_nil
          (SimpleGraph.Walk.darts_eq_nil.not.mpr
            hp.not_nil))⟩
      kwLoopPhaseProduct (kwAngularSplitPhase embedding)
        (kwGraphCycleDartLoop p) = -1




theorem kwAngularSplit_unitCycleLog_of_cyclePhaseSign
    {V : Type*} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj]
    (embedding : KWStraightLineEmbedding G)
    (hphase : KWAngularSplitCyclePhaseSign embedding) :
    KWGraphUnitCycleLog
      (kwOrderedDartPortSplitGraph G (kwAngularPortOrder embedding))
      (kwAngularSplitPhase embedding) := by
  apply (kwGraphUnitCycleLog_iff_cycleCoeff_of_degree_le_three
    (kwOrderedDartPortSplitGraph G (kwAngularPortOrder embedding))
    (kwAngularSplitPhase embedding)
    (kwAngularSplit_degree_le_three embedding)).2
  intro root p hp
  exact kwGraphFormalLogCoeff_cycle_of_reversalInvariant_phaseProduct_neg_one
    (kwOrderedDartPortSplitGraph G (kwAngularPortOrder embedding))
    (kwAngularSplitPhase embedding)
    (kwAngularSplit_loopReversalInvariant embedding)
    (kwAngularSplit_degree_le_three embedding) p hp (hphase p hp)



theorem kacWard_original_of_angularSplit_cyclePhaseSign
    {V : Type*} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj]
    (embedding : KWStraightLineEmbedding G) (weight : Sym2 V → Complex)
    (hphase : KWAngularSplitCyclePhaseSign embedding) :
    (1 - kwGraphTransition G weight embedding.turnPhase).det =
      (kwEvenPolynomial G weight) ^ 2 := by
  exact kacWard_original_of_angularSplit_unitCycleLog_closed
    embedding weight
    (kwAngularSplit_unitCycleLog_of_cyclePhaseSign embedding hphase)

end StatMech.FrontierA
