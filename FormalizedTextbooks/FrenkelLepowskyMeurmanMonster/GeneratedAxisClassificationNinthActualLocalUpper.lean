/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisE8FrameRootRangeAction
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationNinthActualOctadMarking
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationNinthAffineConstraintUpper
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationNinthLocalProjection

/-! The complete genuine source and spread certificates bound the actual Ninth local stabilizer. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster

/-- The full actual Conway projection has at most 92897280 elements, with the original
root range and all actual short markings proved unconditionally. -/
theorem generatedNinth_actual_projected_axis_stabilizer_card_le :
    Nat.card generatedNinthProjectedAxisStabilizer ≤ 92897280 :=
  generatedNinth_affine_projection_card_le_of_octad_comparison
    generatedAxisE8FrameRootRange_section_action generatedNinth_actual_octad_marking_iff

/-- The genuine extraspecial kernel is trivial, so the same bound holds for the entire
actual local axis stabilizer. -/
theorem generatedNinth_actual_local_axis_stabilizer_card_le :
    Nat.card generatedNinthLocalAxisStabilizer ≤ 92897280 := by
  rw [generatedNinth_local_stabilizer_card_range]
  exact generatedNinth_actual_projected_axis_stabilizer_card_le

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
