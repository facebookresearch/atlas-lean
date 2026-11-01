/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedFeasibleContainingZeroOutsideAnchorMatrixData

/-! Every physical matrix entry follows from the genuine original Xi and triality formulas. -/

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 100000
set_option maxHeartbeats 24000000

/-- All72 coordinates in this packet are the actual Xi image of the original source projection. -/
theorem generatedFeasibleContainingZeroOutsideAnchorMatrixPacket06_source : ∀ i : Fin 3, ∀ j : Fin 24,
    (co1XiMatrixQ * generatedFeasibleContainingZeroOutsideAnchorSourceProjectionQ * co1XiMatrixQ.transpose)
      (generatedFeasibleContainingZeroOutsideAnchorMatrixPacketIndex 6 i) j =
        generatedFeasibleContainingZeroOutsideAnchorMatrix1Q (generatedFeasibleContainingZeroOutsideAnchorMatrixPacketIndex 6 i) j := by decide +kernel

/-- All72 intermediate matrix coordinates retain both original signed pair constituents. -/
theorem generatedFeasibleContainingZeroOutsideAnchorMatrixPacket06_triality : ∀ i : Fin 3, ∀ j : Fin 24,
    generatedFeasibleContainingZeroOutsideAnchorForwardMatrixQ (generatedFeasibleContainingZeroOutsideAnchorMatrixPacketIndex 6 i) j =
      generatedFeasibleContainingZeroOutsideAnchorMatrix2Q (generatedFeasibleContainingZeroOutsideAnchorMatrixPacketIndex 6 i) j := by decide +kernel

/-- All72 final coordinates are exactly the original target octad projection. -/
theorem generatedFeasibleContainingZeroOutsideAnchorMatrixPacket06_target : ∀ i : Fin 3, ∀ j : Fin 24,
    (co1XiMatrixQ * generatedFeasibleContainingZeroOutsideAnchorMatrix2Q * co1XiMatrixQ.transpose)
      (generatedFeasibleContainingZeroOutsideAnchorMatrixPacketIndex 6 i) j =
        generatedFeasibleContainingZeroOutsideAnchorTargetProjectionQ (generatedFeasibleContainingZeroOutsideAnchorMatrixPacketIndex 6 i) j := by decide +kernel

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
