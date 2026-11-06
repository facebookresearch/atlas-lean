/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationEighthQTrivial
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationEighthQProjectedEquality
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.Co1OrderExact

/-! The exact eighth local stabilizer and orbit from the genuine kernel and full projection. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster

/-- The full actual eighth-axis stabilizer in H has exactly 16,220,160 elements. -/
theorem generatedEighth_local_stabilizer_card :
    Nat.card generatedEighthLocalAxisStabilizer = 16220160 := by
  rw [generatedEighth_local_stabilizer_card_range, generatedEighth_Q_stabilizer_card,
    generatedEighth_projected_stabilizer_eq_spatial,
    generatedEighthCo1SpatialStabilizer_card, one_mul]

/-- The genuine eighth-axis orbit under H has exactly 8,601,138,282,627,072,000 elements. -/
theorem generatedEighth_local_axis_orbit_card :
    Nat.card (MulAction.orbit H generatedEighthAxis) = 8601138282627072000 := by
  have h := generatedEighthLocalAxisStabilizer.card_mul_index
  rw [generatedEighth_local_stabilizer_card, local_h_card_exact] at h
  have hi : generatedEighthLocalAxisStabilizer.index = 8601138282627072000 := by omega
  rw [generatedEighthLocalAxisStabilizer, MulAction.index_stabilizer,
    ← Nat.card_coe_set_eq] at hi
  exact hi

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
