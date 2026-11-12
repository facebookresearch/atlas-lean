/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/




import Code.FrontierA.KacWardPolygonPhaseInduction
import Code.FrontierA.KacWardPolygonGlobalReduction





open SimpleGraph

namespace StatMech.FrontierA

universe u



theorem KWStraightLineCyclePhaseSign.of_cleanChordCompatibility
    (hcompat : KWCleanChordPhaseCompatibility)
    {V : Type u} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj]
    (embedding : KWStraightLineEmbedding G) :
    KWStraightLineCyclePhaseSign G embedding := by
  intro root p hp
  letI : NeZero p.darts.length :=
    ⟨Nat.ne_of_gt (List.length_pos_of_ne_nil
      (SimpleGraph.Walk.darts_eq_nil.not.mpr hp.not_nil))⟩
  rw [← embedding.vectorPhaseCycle_of_dartLoop
    (kwGraphCycleDartLoop p)]
  rw [← embedding.cyclePolygon_edgeList p hp]
  exact KWFiniteSimplePolygon.phaseCycle_eq_neg_one_of_cleanChordCompatibility
    hcompat (embedding.cyclePolygon p hp)


theorem KWStraightLineCycleOddTurning.of_cleanChordCompatibility
    (hcompat : KWCleanChordPhaseCompatibility)
    {V : Type u} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj]
    (embedding : KWStraightLineEmbedding G) :
    KWStraightLineCycleOddTurning G embedding :=
  KWStraightLineCyclePhaseSign.toOddTurning G embedding
    (KWStraightLineCyclePhaseSign.of_cleanChordCompatibility
      hcompat embedding)


theorem kw_straightLineGraph_formalRoot_eq_evenPolynomial_of_cleanChordCompatibility
    (hcompat : KWCleanChordPhaseCompatibility)
    {V : Type u} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (embedding : KWStraightLineEmbedding G)
    (hdeg : ∀ vertex, G.degree vertex ≤ 3) :
    kwGraphFormalRoot G embedding.turnPhase =
      kwGraphFormalEvenPolynomial G :=
  kw_straightLineGraph_formalRoot_eq_evenPolynomial_of_oddCycleTurning
    G embedding hdeg
      (KWStraightLineCycleOddTurning.of_cleanChordCompatibility
        hcompat embedding)



theorem kacWard_straightLine_trivalent_of_cleanChordCompatibility
    (hcompat : KWCleanChordPhaseCompatibility)
    {V : Type u} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (embedding : KWStraightLineEmbedding G)
    (hdeg : ∀ vertex, G.degree vertex ≤ 3)
    (weight : Sym2 V → ℂ) :
    (1 - kwGraphTransition G weight embedding.turnPhase).det =
      (kwEvenPolynomial G weight) ^ 2 :=
  kacWard_straightLine_trivalent_of_oddCycleTurning G embedding hdeg
    (KWStraightLineCycleOddTurning.of_cleanChordCompatibility
      hcompat embedding) weight

end StatMech.FrontierA
