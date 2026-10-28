/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationNinthOddMarkingMasks
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationNinthFinalOddNumeric

/-! Original integer coefficient checks on chronological odd dictionary block3. -/

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
set_option backward.isDefEq.respectTransparency false

set_option maxRecDepth 100000 in
set_option maxHeartbeats 80000000 in
-- Check all physical columns of these512 original odd dictionary labels.
/-- The complete original numerator identifies each marker and bounds every other physical row. -/
theorem generatedNinth_odd_marking_packet_03 : ∀ v : Fin 512, ∀ i : Fin 24,
    let d : Fin 2048 := ⟨1536 + v.val, by omega⟩
    (|generatedNinthFinalOddNumerator d i| = 8 ↔
      (generatedNinthOddMarkingMask i).testBit d.val = true) ∧
      ((generatedNinthOddMarkingMask i).testBit d.val = false →
        |generatedNinthFinalOddNumerator d i| ≤ 2) := by
  decide +kernel

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
