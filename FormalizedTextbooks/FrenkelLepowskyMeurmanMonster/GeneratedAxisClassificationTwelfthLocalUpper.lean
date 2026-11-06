/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationTwelfthLocalProjection
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationTwelfthGoldenOrbitSpatialUpper

/-! An actual full-axis local bound follows from complete matrix and genuine Q certificates. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster

/-- The actual entire matrix stabilizer has at most 3686400 genuine Conway quotient values. -/
theorem generatedTwelfth_Co1_spatial_stabilizer_upper :
    Nat.card generatedTwelfthCo1SpatialStabilizer ≤ 3686400 := by
  have h := generatedTwelfth_spatial_stabilizer_upper
  rw [generatedTwelfth_spatial_card_twice_Co1] at h
  omega

/-- The whole original full-axis local stabilizer has an unconditional actual upper bound. -/
theorem generatedTwelfth_local_axis_stabilizer_upper :
    Nat.card generatedTwelfthLocalAxisStabilizer ≤ 3686400 := by
  rw [generatedTwelfth_local_stabilizer_card_range]
  exact generatedTwelfth_projected_card_le_spatial.trans
    generatedTwelfth_Co1_spatial_stabilizer_upper

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
