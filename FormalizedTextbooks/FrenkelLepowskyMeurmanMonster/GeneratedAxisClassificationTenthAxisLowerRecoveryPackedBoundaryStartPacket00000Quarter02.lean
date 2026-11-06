/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationTenthAxisLowerRecoveryPackedBoundaryFourPrefixGeneric
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationTenthAxisLowerRecoveryPackedBoundaryStartPacket00000Quarter02Block00
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationTenthAxisLowerRecoveryPackedBoundaryStartPacket00000Quarter02Block01
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationTenthAxisLowerRecoveryPackedBoundaryStartPacket00000Quarter02Block02
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationTenthAxisLowerRecoveryPackedBoundaryStartPacket00000Quarter02Block03

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationTenthAxisLowerRecoveryPackedBoundaryPacketGeneric

/-! Exact complete whole-word boundary partition into sixteen-prefix blocks. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open scoped BigOperators
set_option backward.isDefEq.respectTransparency false

set_option maxHeartbeats 2000000 in
-- Exact finite-address normalization joins four complete original weighted word certificates.
/-- Original complete weighted pre and stage-zero equation for one exact prefix block. -/
theorem generatedTenth_packed_boundary_start_0_00_00_quarter_2 :
    ∀ u : Fin 16,
      (∑ k : Fin 24, generatedTenthTwoFixerTensorNumerator 0 0 k *
        generatedRootEightPackedSignedWord (generatedTenthPackedBoundaryPreWord 0 k
          (generatedTenthPackedBoundaryPacketPrefix 0 ⟨16 * 2 + u.val, by omega⟩))) =
        (generatedTenthTwoFixerTensorDenominator 0 : ℤ) *
          generatedRootEightPackedSignedWord (generatedTenthPackedBoundaryStageWord 0 0 0
            (generatedTenthPackedBoundaryPacketPrefix 0 ⟨16 * 2 + u.val, by omega⟩)) := by
  intro u
  refine generatedTenth_packed_boundary_four_prefix_cover
    (fun v : Fin 16 =>
      (∑ k : Fin 24, generatedTenthTwoFixerTensorNumerator 0 0 k *
        generatedRootEightPackedSignedWord (generatedTenthPackedBoundaryPreWord 0 k
          (generatedTenthPackedBoundaryPacketPrefix 0 ⟨16 * 2 + v.val, by omega⟩))) =
        (generatedTenthTwoFixerTensorDenominator 0 : ℤ) *
          generatedRootEightPackedSignedWord (generatedTenthPackedBoundaryStageWord 0 0 0
            (generatedTenthPackedBoundaryPacketPrefix 0 ⟨16 * 2 + v.val, by omega⟩)) ) ?_ u
  intro b
  fin_cases b
  · simpa only [Fin.val_mk, Nat.add_assoc] using
      generatedTenth_packed_boundary_start_0_00_00_quarter_2_block_0
  · simpa only [Fin.val_mk, Nat.add_assoc] using
      generatedTenth_packed_boundary_start_0_00_00_quarter_2_block_1
  · simpa only [Fin.val_mk, Nat.add_assoc] using
      generatedTenth_packed_boundary_start_0_00_00_quarter_2_block_2
  · simpa only [Fin.val_mk, Nat.add_assoc] using
      generatedTenth_packed_boundary_start_0_00_00_quarter_2_block_3

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
