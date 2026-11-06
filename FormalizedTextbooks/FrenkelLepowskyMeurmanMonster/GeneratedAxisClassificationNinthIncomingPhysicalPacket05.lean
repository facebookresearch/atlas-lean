/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationNinthIncomingSourceData
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationNinthInverseCoordinates

/-! Original inverse odd-short vector certificates for label block 5. -/

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open scoped Matrix BigOperators
set_option backward.isDefEq.respectTransparency false

set_option maxRecDepth 100000 in
set_option maxHeartbeats 30000000 in
-- Replay the actual inverse matrix on only sixty-four original odd labels.
/-- Every target in this block has the genuine preferred source and physical sign. -/
theorem generatedNinth_incoming_physical_packet_05 : ∀ m : Fin 64, ∀ i : Fin 24,
    let d : Fin 2048 := ⟨320 + m.val, by omega⟩
    (∑ j : Fin 24, generatedNinthInverseNumerator i j *
      ((if (golayEncodedMask d.val).testBit j.val then (-1 : ℤ) else 1) *
        (if j = 1 then -3 else 1))) =
      8 * generatedNinthIncomingPhysicalSign d *
        generatedNinthIncomingShortIntegral (generatedNinthIncomingSource d) i := by
  decide +kernel

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
