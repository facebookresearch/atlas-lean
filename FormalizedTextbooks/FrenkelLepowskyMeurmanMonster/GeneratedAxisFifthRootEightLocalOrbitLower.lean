/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import
  FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisFifthRootEightLocalUpper
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.Co1OrderExact

/-! A genuine unconditional lower bound for the original root-eight local axis orbit. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster

/-- The actual local orbit has at least 786389785840189440 axes by its whole stabilizer bound. -/
theorem generatedFifthRootEight_local_axis_orbit_lower :
    786389785840189440 ≤ Nat.card (MulAction.orbit H generatedFifthRootEightAxis) := by
  have h := generatedFifthRootEightLocalAxisStabilizer.card_mul_index
  rw [local_h_card_exact] at h
  have hl := Nat.mul_le_mul_right generatedFifthRootEightLocalAxisStabilizer.index
    generatedFifthRootEight_local_axis_stabilizer_upper
  rw [h] at hl
  have hi : 786389785840189440 ≤ generatedFifthRootEightLocalAxisStabilizer.index := by
    omega
  rw [generatedFifthRootEightLocalAxisStabilizer, MulAction.index_stabilizer,
    ← Nat.card_coe_set_eq] at hi
  exact hi

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
