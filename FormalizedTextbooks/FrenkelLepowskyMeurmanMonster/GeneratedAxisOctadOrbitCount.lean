/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisOctadStabilizerExact
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationOctadTransition

/-! Unconditional counting of the actual octad-image local axis orbit. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
set_option backward.isDefEq.respectTransparency false

/-- The actual H orbit of the actual triality octad-image axis. -/
def generatedOctadLocalAxisOrbit (e : Fin 64) (c : ZMod 2) : Set GriessSpace :=
  MulAction.orbit H (generatedOctadLocalAxis e c)

/-- The actual octad-image local stabilizer has index 11935123200 in H. -/
theorem generatedOctadLocalAxisStabilizer_index (e : Fin 64) (c : ZMod 2) :
    (generatedOctadLocalAxisStabilizer e c).index = 11935123200 := by
  have h := (generatedOctadLocalAxisStabilizer e c).card_mul_index
  rw [generatedOctadLocalAxisStabilizer_card, local_h_card_exact] at h
  omega

/-- Exactly 11935123200 actual vectors occur in this genuine local axis orbit. -/
theorem generatedOctadLocalAxisOrbit_card (e : Fin 64) (c : ZMod 2) :
    Nat.card (generatedOctadLocalAxisOrbit e c) = 11935123200 := by
  have h := generatedOctadLocalAxisStabilizer_index e c
  rw [generatedOctadLocalAxisStabilizer, MulAction.index_stabilizer,
    ← Nat.card_coe_set_eq] at h
  exact h

/-- Every counted octad-image local axis belongs to the genuine global axis orbit. -/
theorem generatedOctadLocalAxisOrbit_subset_generated
    (e : Fin 64) (c : ZMod 2) (r : GriessShortIndex) (d : ZMod 2) :
    generatedOctadLocalAxisOrbit e c ⊆ generatedVectorOrbit (conwayShortAxis r d) := by
  rintro x ⟨k, hk⟩
  obtain ⟨h, hh⟩ := generatedAxis_local_signed_transitive r
    (Sum.inr (Sum.inl (generatedOctadBasisOctad, e))) d c
  refine ⟨localIntoGenerated k * extraIntoGenerated * localIntoGenerated h, ?_⟩
  change rhoLocal k (sExtra (rhoLocal h (conwayShortAxis r d))) = x
  rw [hh]
  exact hk

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
