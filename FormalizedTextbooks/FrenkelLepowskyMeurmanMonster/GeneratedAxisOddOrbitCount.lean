/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisOddStabilizerExact
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationOctadTransition

/-! Unconditional exact counting of the third genuine local axis orbit. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
set_option backward.isDefEq.respectTransparency false

/-- The genuine H orbit of the actual original odd triality-image axis. -/
def generatedOddLocalAxisOrbit : Set GriessSpace := MulAction.orbit H generatedOddAxis

theorem generatedOddLocalAxisStabilizer_index :
    generatedOddLocalAxisStabilizer.index = 1630347264000 := by
  have h := generatedOddLocalAxisStabilizer.card_mul_index
  rw [generatedOddLocalAxisStabilizer_card, local_h_card_exact] at h
  omega

/-- Precisely 1630347264000 actual axes occur in the genuine third local H orbit. -/
theorem generatedOddLocalAxisOrbit_card :
    Nat.card generatedOddLocalAxisOrbit = 1630347264000 := by
  have h := generatedOddLocalAxisStabilizer_index
  rw [generatedOddLocalAxisStabilizer, MulAction.index_stabilizer,
    ← Nat.card_coe_set_eq] at h
  exact h

/-- Every counted actual odd-image axis belongs to the genuine global axis orbit. -/
theorem generatedOddLocalAxisOrbit_subset_generated (r : GriessShortIndex) (d : ZMod 2) :
    generatedOddLocalAxisOrbit ⊆ generatedVectorOrbit (conwayShortAxis r d) := by
  rintro x ⟨k, hk⟩
  obtain ⟨h, hh⟩ := generatedAxis_local_signed_transitive r (Sum.inr (Sum.inr (0, 0))) d 0
  refine ⟨localIntoGenerated k * extraIntoGenerated * localIntoGenerated h, ?_⟩
  change rhoLocal k (sExtra (rhoLocal h (conwayShortAxis r d))) = x
  rw [hh]
  exact hk

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
