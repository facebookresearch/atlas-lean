/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedFeasibleContainingZeroOutsideAnchorQData

/-! Ordinary-kernel complete preferred-Q images for fifteen actual support addresses. -/

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 100000
set_option maxHeartbeats 24000000

/-- Decidable equality of genuine Q by both extension coordinates, for finite certificates. -/
local instance generatedFeasibleContainingZeroOutsideAnchorQDecidable03 : DecidableEq Q :=
  generatedSixthQDecidableEq

/-- Both entire genuine Q images are checked, including their actual central signs. -/
theorem generatedFeasibleContainingZeroOutsideAnchorQPacket03 : ∀ t : Fin 2, ∀ n : Fin 15,
    generatedFeasibleContainingZeroOutsideAnchorQImage t
      (generatedFeasibleContainingZeroOutsideAnchorQ (generatedFeasibleContainingZeroOutsideAnchorRoot (if t = 0 then 0 else 2)
        (generatedFeasibleContainingZeroOutsideAnchorPacketIndex 3 n))) =
      qCentral (generatedFeasibleContainingZeroOutsideAnchorPhase t (generatedFeasibleContainingZeroOutsideAnchorPacketIndex 3 n)) *
        generatedFeasibleContainingZeroOutsideAnchorQ (generatedFeasibleContainingZeroOutsideAnchorRoot (if t = 0 then 1 else 3)
          (generatedFeasibleContainingZeroOutsideAnchorPacketIndex 3 n)) := by decide +kernel

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
