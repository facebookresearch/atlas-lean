/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationNinthColumnPackedData

/-! Check every packed mask against the original frozen 64-bit chronological blocks. -/

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster

set_option maxRecDepth 20000 in
set_option maxHeartbeats 20000000 in
-- Compare 640 original blocks with their exact packed integer chunks.
/-- Every original positive block is the corresponding exact packed chunk. -/
theorem generatedNinth_column_packed_positive_chunks : ∀ k : Fin 10, ∀ b : Fin 64,
    (generatedNinthColumnPackedPositive k >>> (64 * b.val)) &&& 0xffffffffffffffff =
      generatedNinthColumnSpinPositive k b := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 20000000 in
-- Compare 640 original blocks with their exact packed integer chunks.
/-- Every original magnitudeone block is the corresponding exact packed chunk. -/
theorem generatedNinth_column_packed_magnitudeOne_chunks : ∀ k : Fin 10, ∀ b : Fin 64,
    (generatedNinthColumnPackedMagnitudeOne k >>> (64 * b.val)) &&& 0xffffffffffffffff =
      generatedNinthColumnSpinMagnitudeOne k b := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 20000000 in
-- Compare 640 original blocks with their exact packed integer chunks.
/-- Every original magnitudetwo block is the corresponding exact packed chunk. -/
theorem generatedNinth_column_packed_magnitudeTwo_chunks : ∀ k : Fin 10, ∀ b : Fin 64,
    (generatedNinthColumnPackedMagnitudeTwo k >>> (64 * b.val)) &&& 0xffffffffffffffff =
      generatedNinthColumnSpinMagnitudeTwo k b := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 20000000 in
-- Compare 640 original blocks with their exact packed integer chunks.
/-- Every original magnitudefour block is the corresponding exact packed chunk. -/
theorem generatedNinth_column_packed_magnitudeFour_chunks : ∀ k : Fin 10, ∀ b : Fin 64,
    (generatedNinthColumnPackedMagnitudeFour k >>> (64 * b.val)) &&& 0xffffffffffffffff =
      generatedNinthColumnSpinMagnitudeFour k b := by
  decide +kernel

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
