/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedFeasibleContainingZeroOutsideAnchorLiteralData

/-! Complete actual pair coordinates in a bounded69-pair packet. -/

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 100000
set_option maxHeartbeats 24000000

/-- Both signs and stages include every sparse source coefficient at every indicated pair. -/
theorem generatedFeasibleContainingZeroOutsideAnchorPairPacket00_sparse : ∀ t : Fin 2, ∀ s : Fin 2, ∀ p : Fin 69,
    generatedFeasibleContainingZeroOutsideAnchorPairQ (if t = 0 then 1 else 2) s (generatedFeasibleContainingZeroOutsideAnchorPairPacketIndex 0 p) =
      generatedFeasibleContainingZeroOutsideAnchorPairLiteralQ t s (generatedFeasibleContainingZeroOutsideAnchorPairPacketIndex 0 p) := by decide +kernel

/-- Every indicated preferred pair sign is the complete original forward triality coordinate. -/
theorem generatedFeasibleContainingZeroOutsideAnchorPairPacket00_triality : ∀ s : Fin 2, ∀ p : Fin 69,
    let r := generatedFeasibleContainingZeroOutsideAnchorPairPacketIndex 0 p
    let m := generatedFeasibleContainingZeroOutsideAnchorMatrix1Q (generatedAxisGlobalPairCoordinates r).1
      (generatedAxisGlobalPairCoordinates r).2
    let b := (generatedFeasibleContainingZeroOutsideAnchorPairLiteralQ 0 0 r - generatedFeasibleContainingZeroOutsideAnchorPairLiteralQ 0 1 r) / 2
    (if s = 0 then m + b else b - m) =
      generatedFeasibleContainingZeroOutsideAnchorPairLiteralQ 1 s r := by decide +kernel

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
