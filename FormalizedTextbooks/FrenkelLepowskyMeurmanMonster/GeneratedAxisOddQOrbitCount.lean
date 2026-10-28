/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisOddStabilizerProjection
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.LocalStructure

/-! The full actual odd-axis phase orbit, independently of the projected-lift obligation. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
set_option backward.isDefEq.respectTransparency false

/-- Actual axes obtained by applying the genuine extraspecial subgroup to the odd image. -/
def generatedOddQAxisOrbit : Set GriessSpace :=
  Set.range (fun q : Q => rhoLocal (inclQ q) generatedOddAxis)

theorem generatedOddAxisQStabilizer_index : generatedOddAxisQStabilizer.index = 8192 := by
  have h := generatedOddAxisQStabilizer.card_mul_index
  rw [generatedOddAxisQStabilizer_card, q_card] at h
  omega

/-- Exactly 8192 actual full axes, rather than just spin states, occur in the Q orbit. -/
theorem generatedOddQAxisOrbit_card : Nat.card generatedOddQAxisOrbit = 8192 := by
  let : MulAction Q GriessSpace := MulAction.compHom GriessSpace inclQ
  have hs : MulAction.stabilizer Q generatedOddAxis = generatedOddAxisQStabilizer := by
    ext q
    rfl
  have h := generatedOddAxisQStabilizer_index
  rw [← hs, MulAction.index_stabilizer, ← Nat.card_coe_set_eq] at h
  exact h

/-- Every counted actual Q-axis point lies in the genuine local H orbit. -/
theorem generatedOddQAxisOrbit_subset_local :
    generatedOddQAxisOrbit ⊆ MulAction.orbit H generatedOddAxis := by
  rintro x ⟨q, hq⟩
  exact ⟨inclQ q, hq⟩

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
