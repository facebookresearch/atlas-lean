/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationNinthActualLocalUpper
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationNinthLowerSpinThreeWholeActualLower
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.Co1OrderExact

/-! The genuine complete Ninth-axis stabilizer and its actual local orbit have
exact cardinalities. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
set_option backward.isDefEq.respectTransparency false

/-- The entire actual full-axis Conway projection has exactly92897280 elements. -/
theorem generatedNinth_actual_projected_axis_stabilizer_card :
    Nat.card generatedNinthProjectedAxisStabilizer = 92897280 :=
  le_antisymm generatedNinth_actual_projected_axis_stabilizer_card_le
    generatedNinth_lower_spin_three_whole_actual_projected_card_lower

/-- The genuine extraspecial kernel is trivial, giving the full actual local stabilizer order. -/
theorem generatedNinth_actual_local_axis_stabilizer_card :
    Nat.card generatedNinthLocalAxisStabilizer = 92897280 := by
  rw [generatedNinth_local_stabilizer_card_range]
  exact generatedNinth_actual_projected_axis_stabilizer_card

/-- The whole Ninth-axis orbit under the actual local group H has its exact cardinality. -/
theorem generatedNinth_actual_local_axis_orbit_card :
    Nat.card (MulAction.orbit H generatedNinthAxis) = 1501786049347584000 := by
  have h := generatedNinthLocalAxisStabilizer.card_mul_index
  rw [generatedNinth_actual_local_axis_stabilizer_card, local_h_card_exact] at h
  have hi : generatedNinthLocalAxisStabilizer.index = 1501786049347584000 := by omega
  rw [generatedNinthLocalAxisStabilizer, MulAction.index_stabilizer,
    ← Nat.card_coe_set_eq] at hi
  exact hi

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
