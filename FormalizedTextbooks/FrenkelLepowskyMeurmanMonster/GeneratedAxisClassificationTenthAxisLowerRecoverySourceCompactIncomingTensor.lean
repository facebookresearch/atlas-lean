/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationTenthAxisLowerRecoverySourceTensorCalibration
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationTenthRepresentative

/-! Ungated genuine compact source binding; full central signs are retained. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open Multiplicative
set_option backward.isDefEq.respectTransparency false

/-- Under the genuine combined tensor anchor, the entire actual incoming Root02 tensor is the
explicit compact tensor action on the actual original Fifth tensor. -/
theorem generatedTenth_source_compact_incoming_tensor
    (hanchor : generatedTenthAxisLowerRecoverySourceTensorAnchorCondition) :
    generatedAxisGlobalFifthRoot02Packet.2.2 =
      generatedTenthAxisLowerRecoverySourceCompactTensor (griessConwayEncode generatedFifthAxis).2.2
        := by
  rw [← generatedAxisGlobalFifthRoot02Packet_actual,
    generatedAxisGlobalFifthShortWordFiber_encode, localConwayRawRepresentation_tensor,
    generatedTenth_axis_lower_recovery_source_tensor_actual hanchor]

/-- Every physical coefficient retains the genuine combined sign calibration. -/
theorem generatedTenth_source_compact_incoming_tensor_coordinate
    (hanchor : generatedTenthAxisLowerRecoverySourceTensorAnchorCondition)
    (t : SpinIndex) (i : Fin 24) :
    generatedAxisGlobalFifthRoot02Packet.2.2 t i =
      generatedTenthAxisLowerRecoverySourceCompactTensor
        (griessConwayEncode generatedFifthAxis).2.2 t i :=
  congrFun (congrFun (generatedTenth_source_compact_incoming_tensor hanchor) t) i

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
