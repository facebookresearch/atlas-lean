/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationFourthQStabilizerExact

/-! The full actual fourth-axis extraspecial orbit has exactly 262144 points. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
set_option backward.isDefEq.respectTransparency false

/-- Genuine full axes obtained by the actual extraspecial action on the fourth representative. -/
def generatedFourthQAxisOrbit : Set GriessSpace :=
  Set.range (fun q : Q => rhoLocal (inclQ q) generatedFourthAxis)

/-- The actual full-axis Q stabilizer has index 262144 in the genuine extraspecial group. -/
theorem generatedFourth_axis_q_stabilizer_index :
    generatedFourthAxisQStabilizer.index = 262144 := by
  have h := generatedFourthAxisQStabilizer.card_mul_index
  rw [generatedFourth_axis_q_stabilizer_card, q_card] at h
  omega

/-- Exactly 262144 distinct full axes occur in the genuine fourth Q phase orbit. -/
theorem generatedFourth_q_axis_orbit_card : Nat.card generatedFourthQAxisOrbit = 262144 := by
  let : MulAction Q GriessSpace := MulAction.compHom GriessSpace inclQ
  have hs : MulAction.stabilizer Q generatedFourthAxis = generatedFourthAxisQStabilizer := by
    ext q
    rfl
  have h := generatedFourth_axis_q_stabilizer_index
  rw [← hs, MulAction.index_stabilizer, ← Nat.card_coe_set_eq] at h
  exact h

/-- Every counted Q-axis point belongs to the genuine local H orbit. -/
theorem generatedFourth_q_axis_orbit_subset_local :
    generatedFourthQAxisOrbit ⊆ MulAction.orbit H generatedFourthAxis := by
  rintro x ⟨q, hq⟩
  exact ⟨inclQ q, hq⟩

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
