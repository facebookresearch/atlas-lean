/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import
  FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisFifthRootEightLocalProjection
public import
  FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisFifthRootEightQKernelUpper

/-! The entire actual root-eight full-axis stabilizer has the required unconditional upper bound. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster

/-- The actual full-axis stabilizer is bounded by its genuine kernel and matrix quotient. -/
theorem generatedFifthRootEight_local_axis_stabilizer_upper :
    Nat.card generatedFifthRootEightLocalAxisStabilizer ≤ 177408000 := by
  have hp := generatedFifthRootEight_projected_card_le_spatial
  rw [generatedFifthRootEight_Co1_spatial_stabilizer_card] at hp
  rw [generatedFifthRootEight_local_stabilizer_card_Q_mul_range]
  calc
    _ ≤ 2 * 88704000 := Nat.mul_le_mul
      generatedFifthRootEight_axis_Q_kernel_upper_two hp
    _ = 177408000 := by decide

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
