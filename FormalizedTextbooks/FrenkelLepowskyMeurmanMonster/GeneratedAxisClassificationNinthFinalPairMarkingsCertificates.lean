/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationNinthFinalPairMarkingsData
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationNinthPreferredPairs

/-! Original integer checks distinguish the actual signed-pair marking coefficients. -/

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
set_option backward.isDefEq.respectTransparency false

set_option maxRecDepth 100000 in
set_option maxHeartbeats 40000000 in
-- Check all552 actual preferred pair labels against the source integer matrix and phases.
/-- The original final pair numerators identify the displayed markings and bound every other row. -/
theorem generatedNinth_final_pair_marking_integer_certificate : ∀ s : Fin 2, ∀ p : Fin 276,
    (generatedNinthFinalPairInteger s p = -32 ↔ (s, p) ∈ generatedNinthFinalPairMarkings) ∧
      ((s, p) ∉ generatedNinthFinalPairMarkings → |generatedNinthFinalPairInteger s p| ≤ 8) := by
  simp only [generatedNinthFinalPairInteger]
  simp_rw [generatedNinth_coordinate_pair_actual]
  decide +kernel

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
