/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/




import Code.FrontierA.KacWardAdaptiveActualPhaseModel
import Code.FrontierA.KacWardGenericPolygonReduction
import Code.FrontierA.KacWardPolygonGlobalReduction





namespace StatMech.FrontierA

open SimpleGraph


theorem kwFiniteSimplePolygonPhaseSign_adaptive :
    KWFiniteSimplePolygonPhaseSign :=
  kwFiniteSimplePolygonPhaseSign_of_genericCoordinate
    (fun polygon hcross hcoords ↦
      polygon.phaseCycle_eq_neg_one_of_generic hcross hcoords)


theorem kwStraightLineCyclePhaseSign_adaptive
    {V : Type*} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj]
    (embedding : KWStraightLineEmbedding G) :
    KWStraightLineCyclePhaseSign G embedding := by
  intro root p hp
  letI : NeZero p.darts.length :=
    ⟨Nat.ne_of_gt (List.length_pos_of_ne_nil
      (SimpleGraph.Walk.darts_eq_nil.not.mpr hp.not_nil))⟩
  rw [← embedding.vectorPhaseCycle_of_dartLoop (kwGraphCycleDartLoop p)]
  rw [← embedding.cyclePolygon_edgeList p hp]
  exact kwFiniteSimplePolygonPhaseSign_adaptive
    (embedding.cyclePolygon p hp)



theorem kwStraightLineCycleOddTurning_adaptive
    {V : Type*} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj]
    (embedding : KWStraightLineEmbedding G) :
    KWStraightLineCycleOddTurning G embedding :=
  KWStraightLineCyclePhaseSign.toOddTurning G embedding
    (kwStraightLineCyclePhaseSign_adaptive embedding)



theorem kacWard_straightLine_trivalent_adaptive
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (embedding : KWStraightLineEmbedding G)
    (hdeg : ∀ vertex, G.degree vertex ≤ 3)
    (weight : Sym2 V → ℂ) :
    (1 - kwGraphTransition G weight embedding.turnPhase).det =
      (kwEvenPolynomial G weight) ^ 2 :=
  kacWard_straightLine_trivalent_of_oddCycleTurning G embedding hdeg
    (kwStraightLineCycleOddTurning_adaptive embedding) weight

end StatMech.FrontierA
