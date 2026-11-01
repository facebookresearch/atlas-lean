/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationTenthLocalProjection

/-! Actual Tenth Conway matrix quotient order and full original axis stabilizer bound. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster

/-- The entire actual matrix stabilizer has exactly2903040 genuine Conway quotient values. -/
theorem generatedTenth_Co1_spatial_stabilizer_card :
    Nat.card generatedTenthCo1SpatialStabilizer = 2903040 := by
  have h := generatedTenth_spatial_card_twice_Co1
  rw [generatedTenth_e7_actual_original_matrix_stabilizer_card] at h
  omega

/-- The entire original full-axis local stabilizer has an unconditional actual upper bound. -/
theorem generatedTenth_local_axis_stabilizer_upper :
    Nat.card generatedTenthLocalAxisStabilizer ≤ 2903040 := by
  rw [generatedTenth_local_stabilizer_card_range]
  have h := generatedTenth_projected_card_le_spatial
  rw [generatedTenth_Co1_spatial_stabilizer_card] at h
  exact h

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
