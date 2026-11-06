/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisOctadStabilizerExact
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.LocalStructure

/-! The actual octad-image phase orbit has precisely 256 full axes. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
set_option backward.isDefEq.respectTransparency false

/-- Actual full axes obtained from the octad image by genuine extraspecial elements. -/
def generatedOctadQAxisOrbit (e : Fin 64) (c : ZMod 2) : Set GriessSpace :=
  Set.range (fun q : Q => rhoLocal (inclQ q) (generatedOctadLocalAxis e c))

theorem generatedOctadAxisQStabilizer_index (e : Fin 64) (c : ZMod 2) :
    (generatedOctadAxisQStabilizer e c).index = 256 := by
  have h := (generatedOctadAxisQStabilizer e c).card_mul_index
  rw [generatedOctadAxisQStabilizer_card, q_card] at h
  omega

/-- Each genuine octad-image Q phase orbit consists of 256 distinct actual full axes. -/
theorem generatedOctadQAxisOrbit_card (e : Fin 64) (c : ZMod 2) :
    Nat.card (generatedOctadQAxisOrbit e c) = 256 := by
  let : MulAction Q GriessSpace := MulAction.compHom GriessSpace inclQ
  have hs : MulAction.stabilizer Q (generatedOctadLocalAxis e c) =
      generatedOctadAxisQStabilizer e c := by
    ext q
    rfl
  have h := generatedOctadAxisQStabilizer_index e c
  rw [← hs, MulAction.index_stabilizer, ← Nat.card_coe_set_eq] at h
  exact h

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
