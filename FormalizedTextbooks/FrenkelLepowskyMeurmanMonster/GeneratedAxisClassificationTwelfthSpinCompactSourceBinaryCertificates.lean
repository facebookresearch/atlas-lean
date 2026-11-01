/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationTwelfthSpinCompactData
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationTwelfthSectionPackedWordActions

/-! Complete original source-word bindings of every proposed compact spatial lift. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster

set_option maxRecDepth 20000 in
set_option maxHeartbeats 20000000 in
-- Check every full original signed spatial source word on all twenty-four coordinate generators.
/-- Every compact binary column is exactly the complete original signed source-word replay. -/
theorem generatedTwelfth_spin_compact_source_binary_certificate : ∀ (g : Fin 12) (j : Fin 24),
    generatedTwelfthSectionPackedMaskWord (generatedTwelfthSpinCompactSpatialWord g)
        (2 ^ j.val) = generatedTwelfthSpinCompactBinaryColumns g j := by
  decide +kernel

/-- The full actual lattice action of every original spatial source word retains its checked column. -/
theorem generatedTwelfth_spin_compact_source_binary_actual (g : Fin 12) (j : Fin 24) :
    leechBinaryAction
        (((generatedTwelfthSpinCompactSpatialWord g).map
          generatedTwelfthRootOrbitLetter).prod).val
        (monsterCo1GeometryBinaryMaskDecode (n := 24) (2 ^ j.val)) =
      monsterCo1GeometryBinaryMaskDecode (generatedTwelfthSpinCompactBinaryColumns g j) := by
  rw [generatedTwelfth_section_word_packed_actual,
    generatedTwelfth_spin_compact_source_binary_certificate]

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
