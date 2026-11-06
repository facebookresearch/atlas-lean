/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationTenthAxisLowerRecoveryPackedBoundaryQuarterGeneric
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationTenthAxisLowerRecoveryPackedBoundaryStartPacket00000Quarter00
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationTenthAxisLowerRecoveryPackedBoundaryStartPacket00000Quarter01
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationTenthAxisLowerRecoveryPackedBoundaryStartPacket00000Quarter02
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationTenthAxisLowerRecoveryPackedBoundaryStartPacket00000Quarter03

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationTenthAxisLowerRecoveryPackedBoundaryPacketGeneric

/-! Ungated complete two-fixer boundary certificates. No declaration has passed Lean. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open scoped BigOperators
set_option backward.isDefEq.respectTransparency false

/-- Complete genuine pre-label, quadratic, physical-weight and stage-zero word equations. -/
theorem generatedTenth_packed_boundary_start_packet_0_00_00 :
    GeneratedTenthPackedBoundaryStartPacketCondition 0 0 0 := by
  unfold GeneratedTenthPackedBoundaryStartPacketCondition
  intro u
  refine generatedTenth_packed_boundary_quarter_cover
    (fun v : Fin 64 =>
      (∑ k : Fin 24, generatedTenthTwoFixerTensorNumerator 0 0 k *
        generatedRootEightPackedSignedWord (generatedTenthPackedBoundaryPreWord 0 k
          (generatedTenthPackedBoundaryPacketPrefix 0 v))) =
        (generatedTenthTwoFixerTensorDenominator 0 : ℤ) *
          generatedRootEightPackedSignedWord (generatedTenthPackedBoundaryStageWord 0 0 0
            (generatedTenthPackedBoundaryPacketPrefix 0 v))) ?_ u
  intro b
  fin_cases b
  · exact generatedTenth_packed_boundary_start_0_00_00_quarter_0
  · exact generatedTenth_packed_boundary_start_0_00_00_quarter_1
  · exact generatedTenth_packed_boundary_start_0_00_00_quarter_2
  · exact generatedTenth_packed_boundary_start_0_00_00_quarter_3

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
