/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Code.Universality.RSWConnectorFiniteGraph











open Finset SimpleGraph Set

namespace StatMech.Universality

open StatMech.Percolation StatMech.Lattice StatMech.RSW.Box

noncomputable section



def RlcConnectorPIMSFailureMassTransport {n : Int}
    (gamma : RlcRightDiagonalPath n) (gamma' : RlcLeftDiagonalPath n)
    (q : Real) : Prop :=
  rlc_connectorForcedDualEventMass gamma gamma'
      (BeffaraDC.selfDualPoint q) q
      (rlc_finiteConnectorEvent gamma gamma')ᶜ <=
    rlc_connectorForcedDualEventMass gamma gamma'
      (BeffaraDC.selfDualPoint q) q
      (rlc_connectorPIMSReflectedConfig gamma gamma' ⁻¹'
        rlc_finiteConnectorEvent gamma gamma')


def RlcConnectorPIMSCollaredFailureMassTransport {n : Int}
    (gamma : RlcRightDiagonalPath n) (gamma' : RlcLeftDiagonalPath n)
    (q : Real) : Prop :=
  rlc_connectorForcedDualEventMass gamma gamma'
      (BeffaraDC.selfDualPoint q) q
      (rlc_finiteConnectorEvent gamma gamma')ᶜ <=
    rlc_connectorForcedDualEventMass gamma gamma'
      (BeffaraDC.selfDualPoint q) q
      (rlc_connectorPIMSCollaredReflectedConfig gamma gamma' ⁻¹'
        rlc_finiteConnectorEvent gamma gamma')



theorem rlc_connectorPIMSFailureMassTransport_of_pointwise {n : Int}
    (gamma : RlcRightDiagonalPath n) (gamma' : RlcLeftDiagonalPath n)
    {q : Real} (hq : 1 <= q)
    (hfailure : forall tau,
      tau ∉ rlc_finiteConnectorEvent gamma gamma' ->
        rlc_connectorPIMSReflectedConfig gamma gamma' tau ∈
          rlc_finiteConnectorEvent gamma gamma') :
    RlcConnectorPIMSFailureMassTransport gamma gamma' q := by
  have hq0 : 0 < q := zero_lt_one.trans_le hq
  obtain ⟨hp, hp1⟩ := BeffaraDC.selfDualPoint_mem_Ioo hq0
  apply rlc_connectorForcedDualEventMass_mono gamma gamma' hp hp1 hq0
  intro tau htau
  exact hfailure tau (by simpa using htau)


theorem rlc_connectorPIMSCollaredFailureMassTransport_of_pointwise
    {n : Int}
    (gamma : RlcRightDiagonalPath n) (gamma' : RlcLeftDiagonalPath n)
    {q : Real} (hq : 1 <= q)
    (hfailure : forall tau,
      tau ∉ rlc_finiteConnectorEvent gamma gamma' ->
        rlc_connectorPIMSCollaredReflectedConfig gamma gamma' tau ∈
          rlc_finiteConnectorEvent gamma gamma') :
    RlcConnectorPIMSCollaredFailureMassTransport gamma gamma' q := by
  have hq0 : 0 < q := zero_lt_one.trans_le hq
  obtain ⟨hp, hp1⟩ := BeffaraDC.selfDualPoint_mem_Ioo hq0
  apply rlc_connectorForcedDualEventMass_mono gamma gamma' hp hp1 hq0
  intro tau htau
  exact hfailure tau (by simpa using htau)



theorem rlc_connectorPIMSFailureMassTransport_of_boundaryArc {n : Int}
    (gamma : RlcRightDiagonalPath n) (gamma' : RlcLeftDiagonalPath n)
    {q : Real} (hq : 1 <= q)
    (harc : forall tau,
      tau ∉ rlc_finiteConnectorEvent gamma gamma' ->
        RlcConnectorPIMSBoundaryArc gamma gamma' tau) :
    RlcConnectorPIMSFailureMassTransport gamma gamma' q := by
  apply rlc_connectorPIMSFailureMassTransport_of_pointwise gamma gamma' hq
  intro tau hno
  apply rlc_connectorPIMSReflectedConfig_mem_event_of_actualSelectedArc
    gamma gamma' tau
  exact rlc_connectorPIMSActualSelectedArc_of_boundaryArc_of_failure
    gamma gamma' tau hno (harc tau hno)



theorem rlc_connectorPIMSFailureMassTransport_of_contourCertificate
    {n : Int}
    (gamma : RlcRightDiagonalPath n) (gamma' : RlcLeftDiagonalPath n)
    {q : Real} (hq : 1 <= q)
    (hcontour : forall tau,
      tau ∉ rlc_finiteConnectorEvent gamma gamma' ->
        RlcConnectorPIMSContourCertificate gamma gamma' tau) :
    RlcConnectorPIMSFailureMassTransport gamma gamma' q := by
  apply rlc_connectorPIMSFailureMassTransport_of_boundaryArc
    gamma gamma' hq
  intro tau hno
  exact rlc_connectorPIMSBoundaryArc_of_contourCertificate
    gamma gamma' tau (hcontour tau hno)



theorem
    rlc_connectorPIMSCollaredFailureMassTransport_of_reflectedDual
    {n : Int}
    (gamma : RlcRightDiagonalPath n) (gamma' : RlcLeftDiagonalPath n)
    {q : Real} (hq : 1 <= q)
    (hfailure : forall tau,
      tau ∉ rlc_finiteConnectorEvent gamma gamma' ->
        rlc_connectorReflectedDualConfig gamma gamma' tau ∈
          rlc_finiteConnectorEvent gamma gamma') :
    RlcConnectorPIMSCollaredFailureMassTransport gamma gamma' q := by
  apply rlc_connectorPIMSCollaredFailureMassTransport_of_pointwise
    gamma gamma' hq
  intro tau hno
  exact rlc_connectorPIMSCollaredReflectedConfig_mem_event_of_reflectedDual
    gamma gamma' tau (hfailure tau hno)


theorem
    rlc_finiteConnectorMass_selfDual_ge_of_PIMSFailureMass_inducedWiring
    {n : Int}
    (gamma : RlcRightDiagonalPath n) (gamma' : RlcLeftDiagonalPath n)
    {q : Real} (hq : 1 <= q)
    (C : SimpleGraph (RlcConnectorVertex n)) [DecidableRel C.Adj]
    (hC : C <= rlc_connectorMergedWiring gamma gamma')
    (htransport : RlcConnectorPIMSFailureMassTransport gamma gamma' q)
    (hpush :
      rlc_connectorForcedDualEventMass gamma gamma'
          (BeffaraDC.selfDualPoint q) q
          (rlc_connectorPIMSReflectedConfig gamma gamma' ⁻¹'
            rlc_finiteConnectorEvent gamma gamma') =
        FK.bcEventMass (rlc_connectorFiniteGraph gamma gamma') C
          (BeffaraDC.selfDualPoint q) q
          (rlc_finiteConnectorEvent gamma gamma')) :
    1 / (1 + q) <=
      FK.bcEventMass (rlc_connectorFiniteGraph gamma gamma')
        (rlc_connectorSeparateWiring gamma gamma')
        (BeffaraDC.selfDualPoint q) q
        (rlc_finiteConnectorEvent gamma gamma') := by
  apply rlc_finiteConnectorMass_selfDual_ge_one_div_one_add_q
    gamma gamma' hq
  exact htransport.trans
    (rlc_connectorPIMS_pushforward_le_merged_of_inducedWiring
      gamma gamma' hq C hC hpush)



theorem
    rlc_finiteConnectorMass_selfDual_ge_of_PIMSFailureMass_inducedMixture
    {n : Int} {I : Type*} [Fintype I]
    (gamma : RlcRightDiagonalPath n) (gamma' : RlcLeftDiagonalPath n)
    {q : Real} (hq : 1 <= q)
    (w : I -> Real) (C : I -> SimpleGraph (RlcConnectorVertex n))
    [forall i, DecidableRel (C i).Adj]
    (hw : forall i, 0 <= w i) (hwSum : ∑ i, w i = 1)
    (hC : forall i, C i <= rlc_connectorMergedWiring gamma gamma')
    (htransport : RlcConnectorPIMSFailureMassTransport gamma gamma' q)
    (hpush :
      rlc_connectorForcedDualEventMass gamma gamma'
          (BeffaraDC.selfDualPoint q) q
          (rlc_connectorPIMSReflectedConfig gamma gamma' ⁻¹'
            rlc_finiteConnectorEvent gamma gamma') =
        ∑ i, w i *
          FK.bcEventMass (rlc_connectorFiniteGraph gamma gamma') (C i)
            (BeffaraDC.selfDualPoint q) q
            (rlc_finiteConnectorEvent gamma gamma')) :
    1 / (1 + q) <=
      FK.bcEventMass (rlc_connectorFiniteGraph gamma gamma')
        (rlc_connectorSeparateWiring gamma gamma')
        (BeffaraDC.selfDualPoint q) q
        (rlc_finiteConnectorEvent gamma gamma') := by
  classical
  apply rlc_finiteConnectorMass_selfDual_ge_one_div_one_add_q
    gamma gamma' hq
  exact htransport.trans
    (rlc_connectorPIMS_pushforward_le_merged_of_inducedMixture
      gamma gamma' hq w C hw hwSum hC hpush)



theorem
    rlc_finiteConnectorMass_selfDual_ge_of_PIMSFailureMass_weightedMixture
    {n : Int} {I : Type*} [Fintype I]
    (gamma : RlcRightDiagonalPath n) (gamma' : RlcLeftDiagonalPath n)
    {q : Real} (hq : 1 <= q)
    (w : I -> Real) (C : I -> SimpleGraph (RlcConnectorVertex n))
    [forall i, DecidableRel (C i).Adj]
    (pf : I -> Sym2 (RlcConnectorVertex n) -> Real)
    (hw : forall i, 0 <= w i) (hwSum : ∑ i, w i = 1)
    (hC : forall i, C i <= rlc_connectorMergedWiring gamma gamma')
    (hpf0 : forall i e, 0 <= pf i e)
    (hpf1 : forall i e, pf i e < 1)
    (hpfle : forall i e, pf i e <= BeffaraDC.selfDualPoint q)
    (htransport : RlcConnectorPIMSFailureMassTransport gamma gamma' q)
    (hpush :
      rlc_connectorForcedDualEventMass gamma gamma'
          (BeffaraDC.selfDualPoint q) q
          (rlc_connectorPIMSReflectedConfig gamma gamma' ⁻¹'
            rlc_finiteConnectorEvent gamma gamma') =
        ∑ i, w i *
          (∑ omega,
            (rlc_finiteConnectorEvent gamma gamma').indicator
                (fun _ => (1 : Real)) omega *
              FK.bcProbW (rlc_connectorFiniteGraph gamma gamma')
                (C i) (pf i) q omega)) :
    1 / (1 + q) <=
      FK.bcEventMass (rlc_connectorFiniteGraph gamma gamma')
        (rlc_connectorSeparateWiring gamma gamma')
        (BeffaraDC.selfDualPoint q) q
        (rlc_finiteConnectorEvent gamma gamma') := by
  classical
  apply rlc_finiteConnectorMass_selfDual_ge_one_div_one_add_q
    gamma gamma' hq
  exact htransport.trans
    (rlc_connectorPIMS_pushforward_le_merged_of_weightedMixture
      gamma gamma' hq w C pf hw hwSum hC hpf0 hpf1 hpfle hpush)



theorem
    rlc_finiteConnectorMass_selfDual_ge_of_PIMSCollaredFailureMass_componentMixture
    {n : Int} {I : Type*} [Fintype I]
    (gamma : RlcRightDiagonalPath n) (gamma' : RlcLeftDiagonalPath n)
    {q : Real} (hq : 1 <= q)
    (w : I -> Real)
    (tauExt : I -> ConfigSpace (Sym2 (RlcConnectorVertex n)))
    (hw : forall i, 0 <= w i) (hwSum : ∑ i, w i = 1)
    (htransport : RlcConnectorPIMSCollaredFailureMassTransport
      gamma gamma' q)
    (hpush :
      rlc_connectorForcedDualEventMass gamma gamma'
          (BeffaraDC.selfDualPoint q) q
          (rlc_connectorPIMSCollaredReflectedConfig gamma gamma' ⁻¹'
            rlc_finiteConnectorEvent gamma gamma') =
        ∑ i, w i *
          (∑ omega,
            (rlc_finiteConnectorEvent gamma gamma').indicator
                (fun _ => (1 : Real)) omega *
              FK.bcProbW (rlc_connectorFiniteGraph gamma gamma')
                (rlc_connectorComponentWiring
                  (rlc_connectorPIMSCollaredExteriorOpenGraph
                    gamma gamma' (tauExt i)))
                (rlc_connectorPIMSCollaredParameter gamma gamma'
                  (BeffaraDC.selfDualPoint q)) q omega)) :
    1 / (1 + q) <=
      FK.bcEventMass (rlc_connectorFiniteGraph gamma gamma')
        (rlc_connectorSeparateWiring gamma gamma')
        (BeffaraDC.selfDualPoint q) q
        (rlc_finiteConnectorEvent gamma gamma') := by
  classical
  apply rlc_finiteConnectorMass_selfDual_ge_one_div_one_add_q
    gamma gamma' hq
  exact htransport.trans
    (rlc_connectorPIMSCollared_pushforward_le_merged_of_componentMixture
      gamma gamma' hq w tauExt hw hwSum hpush)

end

end StatMech.Universality
