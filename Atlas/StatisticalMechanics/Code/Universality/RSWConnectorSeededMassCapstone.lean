/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Code.Universality.RSWConnectorSeededOrdinaryAmbient











open Finset SimpleGraph Set

namespace StatMech.Universality

open StatMech.Percolation StatMech.Lattice StatMech.RSW.Box

noncomputable section

theorem rlc_finiteAxisGapConnectorEvent_isIncreasing {n : Int}
    {gamma : RlcRightDiagonalPath n} {gamma' : RlcLeftDiagonalPath n}
    (G : RlcAxisBarrierGap gamma gamma') :
    IsIncreasing (rlc_finiteAxisGapConnectorEvent G) := by
  intro omega tau hot
  rintro ⟨x, y, hx, hy, hxy⟩
  refine ⟨x, y, hx, hy, hxy.mono ?_⟩
  intro u v huv
  rw [FK.openSub_adj] at huv ⊢
  exact ⟨huv.1, hot _ huv.2⟩



noncomputable def rlc_axisGapPIMSSourceSuccessMass {n : Int}
    {gamma : RlcRightDiagonalPath n} {gamma' : RlcLeftDiagonalPath n}
    (G : RlcAxisBarrierGap gamma gamma') (q : Real) : Real :=
  FK.bcEventMass (rlc_axisGapFiniteGraph G)
    (rlc_connectorSeparateWiring gamma gamma')
    (BeffaraDC.selfDualPoint q) q
    (rlc_axisGapPIMSMixedReflectedConfig G ⁻¹'
      rlc_finiteAxisGapConnectorEvent G)



def RlcAxisGapPIMSFailureMassTransport {n : Int}
    {gamma : RlcRightDiagonalPath n} {gamma' : RlcLeftDiagonalPath n}
    (G : RlcAxisBarrierGap gamma gamma') (q : Real) : Prop :=
  FK.bcEventMass (rlc_axisGapFiniteGraph G)
      (rlc_connectorSeparateWiring gamma gamma')
      (BeffaraDC.selfDualPoint q) q
      (rlc_finiteAxisGapConnectorEvent G)ᶜ <=
    rlc_axisGapPIMSSourceSuccessMass G q



theorem rlc_axisGapPIMS_pushforward_le_merged_of_inducedWiring {n : Int}
    {gamma : RlcRightDiagonalPath n} {gamma' : RlcLeftDiagonalPath n}
    (G : RlcAxisBarrierGap gamma gamma')
    {q : Real} (hq : 1 <= q)
    (C : SimpleGraph (RlcConnectorVertex n)) [DecidableRel C.Adj]
    (hC : C <= rlc_connectorMergedWiring gamma gamma')
    (hpush : rlc_axisGapPIMSSourceSuccessMass G q =
      FK.bcEventMass (rlc_axisGapFiniteGraph G) C
        (BeffaraDC.selfDualPoint q) q
        (rlc_finiteAxisGapConnectorEvent G)) :
    rlc_axisGapPIMSSourceSuccessMass G q <=
      FK.bcEventMass (rlc_axisGapFiniteGraph G)
        (rlc_connectorMergedWiring gamma gamma')
        (BeffaraDC.selfDualPoint q) q
        (rlc_finiteAxisGapConnectorEvent G) := by
  have hq0 : 0 < q := zero_lt_one.trans_le hq
  obtain ⟨hp, hp1⟩ := BeffaraDC.selfDualPoint_mem_Ioo hq0
  rw [hpush]
  exact FK.bcProb_mono_bc
    (rlc_axisGapFiniteGraph G) C
    (rlc_connectorMergedWiring gamma gamma') hC hp hp1 hq
    (rlc_finiteAxisGapConnectorEvent_isIncreasing G)



theorem rlc_axisGapPIMS_pushforward_le_merged_of_inducedMixture
    {n : Int} {I : Type*} [Fintype I]
    {gamma : RlcRightDiagonalPath n} {gamma' : RlcLeftDiagonalPath n}
    (G : RlcAxisBarrierGap gamma gamma')
    {q : Real} (hq : 1 <= q)
    (w : I -> Real) (C : I -> SimpleGraph (RlcConnectorVertex n))
    [forall i, DecidableRel (C i).Adj]
    (hw : forall i, 0 <= w i) (hwSum : ∑ i, w i = 1)
    (hC : forall i, C i <= rlc_connectorMergedWiring gamma gamma')
    (hpush : rlc_axisGapPIMSSourceSuccessMass G q =
      ∑ i, w i * FK.bcEventMass (rlc_axisGapFiniteGraph G) (C i)
        (BeffaraDC.selfDualPoint q) q
        (rlc_finiteAxisGapConnectorEvent G)) :
    rlc_axisGapPIMSSourceSuccessMass G q <=
      FK.bcEventMass (rlc_axisGapFiniteGraph G)
        (rlc_connectorMergedWiring gamma gamma')
        (BeffaraDC.selfDualPoint q) q
        (rlc_finiteAxisGapConnectorEvent G) := by
  classical
  have hq0 : 0 < q := zero_lt_one.trans_le hq
  obtain ⟨hp, hp1⟩ := BeffaraDC.selfDualPoint_mem_Ioo hq0
  rw [hpush]
  let target := FK.bcEventMass (rlc_axisGapFiniteGraph G)
    (rlc_connectorMergedWiring gamma gamma')
    (BeffaraDC.selfDualPoint q) q
    (rlc_finiteAxisGapConnectorEvent G)
  calc
    (∑ i, w i * FK.bcEventMass (rlc_axisGapFiniteGraph G) (C i)
        (BeffaraDC.selfDualPoint q) q
        (rlc_finiteAxisGapConnectorEvent G)) <=
        ∑ i, w i * target := by
      apply Finset.sum_le_sum
      intro i _
      apply mul_le_mul_of_nonneg_left _ (hw i)
      exact FK.bcProb_mono_bc
        (rlc_axisGapFiniteGraph G) (C i)
        (rlc_connectorMergedWiring gamma gamma') (hC i) hp hp1 hq
        (rlc_finiteAxisGapConnectorEvent_isIncreasing G)
    _ = target := by rw [← Finset.sum_mul, hwSum, one_mul]










theorem rlc_axisGap_G201_of_inducedWiring {n : Int}
    {gamma : RlcRightDiagonalPath n} {gamma' : RlcLeftDiagonalPath n}
    (G : RlcAxisBarrierGap gamma gamma')
    {q : Real} (hq : 1 <= q)
    (C : SimpleGraph (RlcConnectorVertex n)) [DecidableRel C.Adj]
    (hC : rlc_connectorSeparateWiring gamma gamma' <= C) :
    FK.bcEventMass (rlc_axisGapFiniteGraph G)
        (rlc_connectorSeparateWiring gamma gamma')
        (BeffaraDC.selfDualPoint q) q
        (rlc_finiteAxisGapConnectorEvent G) <=
      FK.bcEventMass (rlc_axisGapFiniteGraph G) C
        (BeffaraDC.selfDualPoint q) q
        (rlc_finiteAxisGapConnectorEvent G) := by
  have hq0 : 0 < q := zero_lt_one.trans_le hq
  obtain ⟨hp, hp1⟩ := BeffaraDC.selfDualPoint_mem_Ioo hq0
  exact FK.bcProb_mono_bc
    (rlc_axisGapFiniteGraph G)
    (rlc_connectorSeparateWiring gamma gamma') C hC hp hp1 hq
    (rlc_finiteAxisGapConnectorEvent_isIncreasing G)






theorem rlc_axisGap_G201_of_inducedMixture
    {n : Int} {I : Type*} [Fintype I]
    {gamma : RlcRightDiagonalPath n} {gamma' : RlcLeftDiagonalPath n}
    (G : RlcAxisBarrierGap gamma gamma')
    {q : Real} (hq : 1 <= q)
    (conditionalConnectorMass : Real)
    (w : I -> Real) (C : I -> SimpleGraph (RlcConnectorVertex n))
    [forall i, DecidableRel (C i).Adj]
    (hw : forall i, 0 <= w i) (hwSum : ∑ i, w i = 1)
    (hC : forall i, rlc_connectorSeparateWiring gamma gamma' <= C i)
    (hconditional : conditionalConnectorMass =
      ∑ i, w i * FK.bcEventMass (rlc_axisGapFiniteGraph G) (C i)
        (BeffaraDC.selfDualPoint q) q
        (rlc_finiteAxisGapConnectorEvent G)) :
    FK.bcEventMass (rlc_axisGapFiniteGraph G)
        (rlc_connectorSeparateWiring gamma gamma')
        (BeffaraDC.selfDualPoint q) q
        (rlc_finiteAxisGapConnectorEvent G) <=
      conditionalConnectorMass := by
  classical
  rw [hconditional]
  let source := FK.bcEventMass (rlc_axisGapFiniteGraph G)
    (rlc_connectorSeparateWiring gamma gamma')
    (BeffaraDC.selfDualPoint q) q
    (rlc_finiteAxisGapConnectorEvent G)
  calc
    source = ∑ i, w i * source := by rw [← Finset.sum_mul, hwSum, one_mul]
    _ <= ∑ i, w i *
        FK.bcEventMass (rlc_axisGapFiniteGraph G) (C i)
          (BeffaraDC.selfDualPoint q) q
          (rlc_finiteAxisGapConnectorEvent G) := by
      apply Finset.sum_le_sum
      intro i _
      exact mul_le_mul_of_nonneg_left
        (rlc_axisGap_G201_of_inducedWiring G hq (C i) (hC i)) (hw i)




theorem rlc_axisGap_G201_floor_of_inducedMixture
    {n : Int} {I : Type*} [Fintype I]
    {gamma : RlcRightDiagonalPath n} {gamma' : RlcLeftDiagonalPath n}
    (G : RlcAxisBarrierGap gamma gamma')
    {q c : Real} (hq : 1 <= q)
    (conditionalConnectorMass : Real)
    (w : I -> Real) (C : I -> SimpleGraph (RlcConnectorVertex n))
    [forall i, DecidableRel (C i).Adj]
    (hw : forall i, 0 <= w i) (hwSum : ∑ i, w i = 1)
    (hC : forall i, rlc_connectorSeparateWiring gamma gamma' <= C i)
    (hconditional : conditionalConnectorMass =
      ∑ i, w i * FK.bcEventMass (rlc_axisGapFiniteGraph G) (C i)
        (BeffaraDC.selfDualPoint q) q
        (rlc_finiteAxisGapConnectorEvent G))
    (hfloor : c <= FK.bcEventMass (rlc_axisGapFiniteGraph G)
      (rlc_connectorSeparateWiring gamma gamma')
      (BeffaraDC.selfDualPoint q) q
      (rlc_finiteAxisGapConnectorEvent G)) :
    c <= conditionalConnectorMass :=
  hfloor.trans (rlc_axisGap_G201_of_inducedMixture
    G hq conditionalConnectorMass w C hw hwSum hC hconditional)


theorem rlc_finiteAxisGapConnectorMass_selfDual_ge_one_div_one_add_q
    {n : Int} {gamma : RlcRightDiagonalPath n}
    {gamma' : RlcLeftDiagonalPath n}
    (G : RlcAxisBarrierGap gamma gamma')
    {q : Real} (hq : 1 <= q)
    (hdual :
      FK.bcEventMass (rlc_axisGapFiniteGraph G)
          (rlc_connectorSeparateWiring gamma gamma')
          (BeffaraDC.selfDualPoint q) q
          (rlc_finiteAxisGapConnectorEvent G)ᶜ <=
        FK.bcEventMass (rlc_axisGapFiniteGraph G)
          (rlc_connectorMergedWiring gamma gamma')
          (BeffaraDC.selfDualPoint q) q
          (rlc_finiteAxisGapConnectorEvent G)) :
    1 / (1 + q) <=
      FK.bcEventMass (rlc_axisGapFiniteGraph G)
        (rlc_connectorSeparateWiring gamma gamma')
        (BeffaraDC.selfDualPoint q) q
        (rlc_finiteAxisGapConnectorEvent G) := by
  have hq0 : 0 < q := zero_lt_one.trans_le hq
  obtain ⟨hp, hp1⟩ := BeffaraDC.selfDualPoint_mem_Ioo hq0
  apply FrontierD.bcEventMass_ge_one_div_one_add_q_of_compl_le_sup_edge
    (rlc_axisGapFiniteGraph G)
    (rlc_connectorSeparateWiring gamma gamma')
    (rlc_connectorRightAnchor gamma) (rlc_connectorLeftAnchor gamma')
    hp hp1 hq (rlc_finiteAxisGapConnectorEvent G)
  simpa only [rlc_connectorMergedWiring] using hdual

theorem
    rlc_finiteAxisGapConnectorMass_selfDual_ge_of_failureMass_inducedWiring
    {n : Int} {gamma : RlcRightDiagonalPath n}
    {gamma' : RlcLeftDiagonalPath n}
    (G : RlcAxisBarrierGap gamma gamma')
    {q : Real} (hq : 1 <= q)
    (C : SimpleGraph (RlcConnectorVertex n)) [DecidableRel C.Adj]
    (hC : C <= rlc_connectorMergedWiring gamma gamma')
    (htransport : RlcAxisGapPIMSFailureMassTransport G q)
    (hpush : rlc_axisGapPIMSSourceSuccessMass G q =
      FK.bcEventMass (rlc_axisGapFiniteGraph G) C
        (BeffaraDC.selfDualPoint q) q
        (rlc_finiteAxisGapConnectorEvent G)) :
    1 / (1 + q) <=
      FK.bcEventMass (rlc_axisGapFiniteGraph G)
        (rlc_connectorSeparateWiring gamma gamma')
        (BeffaraDC.selfDualPoint q) q
        (rlc_finiteAxisGapConnectorEvent G) := by
  apply rlc_finiteAxisGapConnectorMass_selfDual_ge_one_div_one_add_q G hq
  exact htransport.trans
    (rlc_axisGapPIMS_pushforward_le_merged_of_inducedWiring
      G hq C hC hpush)

theorem
    rlc_finiteAxisGapConnectorMass_selfDual_ge_of_failureMass_inducedMixture
    {n : Int} {I : Type*} [Fintype I]
    {gamma : RlcRightDiagonalPath n} {gamma' : RlcLeftDiagonalPath n}
    (G : RlcAxisBarrierGap gamma gamma')
    {q : Real} (hq : 1 <= q)
    (w : I -> Real) (C : I -> SimpleGraph (RlcConnectorVertex n))
    [forall i, DecidableRel (C i).Adj]
    (hw : forall i, 0 <= w i) (hwSum : ∑ i, w i = 1)
    (hC : forall i, C i <= rlc_connectorMergedWiring gamma gamma')
    (htransport : RlcAxisGapPIMSFailureMassTransport G q)
    (hpush : rlc_axisGapPIMSSourceSuccessMass G q =
      ∑ i, w i * FK.bcEventMass (rlc_axisGapFiniteGraph G) (C i)
        (BeffaraDC.selfDualPoint q) q
        (rlc_finiteAxisGapConnectorEvent G)) :
    1 / (1 + q) <=
      FK.bcEventMass (rlc_axisGapFiniteGraph G)
        (rlc_connectorSeparateWiring gamma gamma')
        (BeffaraDC.selfDualPoint q) q
        (rlc_finiteAxisGapConnectorEvent G) := by
  apply rlc_finiteAxisGapConnectorMass_selfDual_ge_one_div_one_add_q G hq
  exact htransport.trans
    (rlc_axisGapPIMS_pushforward_le_merged_of_inducedMixture
      G hq w C hw hwSum hC hpush)


theorem rlc_finiteAxisGapConnectorMass_half_of_failureMass_inducedMixture
    {n : Int} {I : Type*} [Fintype I]
    {gamma : RlcRightDiagonalPath n} {gamma' : RlcLeftDiagonalPath n}
    (G : RlcAxisBarrierGap gamma gamma')
    (w : I -> Real) (C : I -> SimpleGraph (RlcConnectorVertex n))
    [forall i, DecidableRel (C i).Adj]
    (hw : forall i, 0 <= w i) (hwSum : ∑ i, w i = 1)
    (hC : forall i, C i <= rlc_connectorMergedWiring gamma gamma')
    (htransport : RlcAxisGapPIMSFailureMassTransport G 1)
    (hpush : rlc_axisGapPIMSSourceSuccessMass G 1 =
      ∑ i, w i * FK.bcEventMass (rlc_axisGapFiniteGraph G) (C i)
        (BeffaraDC.selfDualPoint 1) 1
        (rlc_finiteAxisGapConnectorEvent G)) :
    (1 : Real) / 2 <=
      FK.bcEventMass (rlc_axisGapFiniteGraph G)
        (rlc_connectorSeparateWiring gamma gamma')
        (BeffaraDC.selfDualPoint 1) 1
        (rlc_finiteAxisGapConnectorEvent G) := by
  convert
    (rlc_finiteAxisGapConnectorMass_selfDual_ge_of_failureMass_inducedMixture
      G (q := 1) (by norm_num) w C hw hwSum hC htransport hpush) using 1 <;> norm_num

end

end StatMech.Universality
