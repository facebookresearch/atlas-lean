/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Code.Universality.RSWConnectorMassDualityCapstone
import Code.Universality.RSWConnectorActualSelectedObstruction
import Code.Universality.RSWStoppedPathPIMSActiveObstruction










open Finset SimpleGraph Set

namespace StatMech.Universality

open StatMech.Percolation StatMech.Lattice StatMech.RSW.Box

noncomputable section

theorem rlc_scaleTwoDoubleFailure_finiteConnectorEvent_eq_empty :
    rlc_finiteConnectorEvent rlc_scaleTwoDoubleFailureRight
      rlc_scaleTwoDoubleFailureLeft = ∅ := by
  ext tau
  simp only [Set.mem_empty_iff_false, iff_false]
  exact rlc_scaleTwoDoubleFailure_finiteConnector_failure tau

private theorem rlc_scaleTwoDoubleFailure_forcedDualMass_univ
    {q : Real} (hq : 1 <= q) :
    rlc_connectorForcedDualEventMass rlc_scaleTwoDoubleFailureRight
        rlc_scaleTwoDoubleFailureLeft (BeffaraDC.selfDualPoint q) q univ = 1 := by
  have hq0 : 0 < q := zero_lt_one.trans_le hq
  obtain ⟨hp, hp1⟩ := BeffaraDC.selfDualPoint_mem_Ioo hq0
  rw [← rlc_bcEventMass_separate_selfDual_eq_forcedDualEventMass
    rlc_scaleTwoDoubleFailureRight rlc_scaleTwoDoubleFailureLeft univ hq0]
  unfold FK.bcEventMass
  simp only [Set.indicator_of_mem (Set.mem_univ _), one_mul]
  exact FK.bcProb_sum_eq_one
    (rlc_connectorFiniteGraph rlc_scaleTwoDoubleFailureRight
      rlc_scaleTwoDoubleFailureLeft)
    (rlc_connectorSeparateWiring rlc_scaleTwoDoubleFailureRight
      rlc_scaleTwoDoubleFailureLeft) hp hp1 hq0

private theorem rlc_scaleTwoDoubleFailure_forcedDualMass_empty
    (p q : Real) :
    rlc_connectorForcedDualEventMass rlc_scaleTwoDoubleFailureRight
        rlc_scaleTwoDoubleFailureLeft p q ∅ = 0 := by
  unfold rlc_connectorForcedDualEventMass
  simp



theorem rlc_scaleTwoDoubleFailure_not_PIMSFailureMassTransport
    {q : Real} (hq : 1 <= q) :
    ¬ RlcConnectorPIMSFailureMassTransport
      rlc_scaleTwoDoubleFailureRight rlc_scaleTwoDoubleFailureLeft q := by
  intro htransport
  unfold RlcConnectorPIMSFailureMassTransport at htransport
  rw [rlc_scaleTwoDoubleFailure_finiteConnectorEvent_eq_empty] at htransport
  simp only [compl_empty, Set.preimage_empty] at htransport
  rw [rlc_scaleTwoDoubleFailure_forcedDualMass_univ hq,
    rlc_scaleTwoDoubleFailure_forcedDualMass_empty] at htransport
  norm_num at htransport



theorem rlc_scaleTwoDoubleFailure_not_PIMSCollaredFailureMassTransport
    {q : Real} (hq : 1 <= q) :
    ¬ RlcConnectorPIMSCollaredFailureMassTransport
      rlc_scaleTwoDoubleFailureRight rlc_scaleTwoDoubleFailureLeft q := by
  intro htransport
  unfold RlcConnectorPIMSCollaredFailureMassTransport at htransport
  rw [rlc_scaleTwoDoubleFailure_finiteConnectorEvent_eq_empty] at htransport
  simp only [compl_empty, Set.preimage_empty] at htransport
  rw [rlc_scaleTwoDoubleFailure_forcedDualMass_univ hq,
    rlc_scaleTwoDoubleFailure_forcedDualMass_empty] at htransport
  norm_num at htransport

end

end StatMech.Universality
