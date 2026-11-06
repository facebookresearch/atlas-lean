/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationFifthQFull
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisTransitionPairOrbit
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.LocalStructure

/-! The actual full-axis extraspecial stabilizer and its exact phase orbit. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
set_option backward.isDefEq.respectTransparency false

/-- The genuine Q intersection of the local stabilizer of the original fifth axis. -/
def generatedFifthAxisQStabilizer : Subgroup Q :=
  (MulAction.stabilizer H generatedFifthAxis).comap inclQ

/-- The full original-axis Q stabilizer equals the proven tensor-fixing subgroup. -/
theorem generatedFifth_axis_Q_stabilizer_eq :
    generatedFifthAxisQStabilizer = generatedFifthTensorQStabilizer := by
  ext q
  change rhoLocal (inclQ q) generatedFifthAxis = generatedFifthAxis ↔ _
  exact generatedFifth_Q_full_fixed_iff q

/-- The actual full-axis extraspecial stabilizer has exactly 32 elements. -/
theorem generatedFifth_axis_Q_stabilizer_card : Nat.card generatedFifthAxisQStabilizer = 32 := by
  rw [generatedFifth_axis_Q_stabilizer_eq, generatedFifth_tensor_Q_card]

/-- Actual full axes obtained by the genuine extraspecial action. -/
def generatedFifthQAxisOrbit : Set GriessSpace :=
  Set.range (fun q : Q => rhoLocal (inclQ q) generatedFifthAxis)

/-- The actual full-axis extraspecial stabilizer has index 2^20. -/
theorem generatedFifth_axis_Q_stabilizer_index :
    generatedFifthAxisQStabilizer.index = 1048576 := by
  have h := generatedFifthAxisQStabilizer.card_mul_index
  rw [generatedFifth_axis_Q_stabilizer_card, q_card] at h
  omega

/-- Exactly 2^20 genuine full axes occur in the extraspecial phase orbit. -/
theorem generatedFifth_Q_axis_orbit_card : Nat.card generatedFifthQAxisOrbit = 1048576 := by
  let : MulAction Q GriessSpace := MulAction.compHom GriessSpace inclQ
  have hs : MulAction.stabilizer Q generatedFifthAxis = generatedFifthAxisQStabilizer := by
    ext q
    rfl
  have h := generatedFifth_axis_Q_stabilizer_index
  rw [← hs, MulAction.index_stabilizer, ← Nat.card_coe_set_eq] at h
  exact h

/-- Every counted phase-axis point belongs to the genuine local orbit of the fifth prototype. -/
theorem generatedFifth_Q_axis_orbit_subset_local :
    generatedFifthQAxisOrbit ⊆ MulAction.orbit H generatedFifthAxis := by
  rintro x ⟨q, hq⟩
  exact ⟨inclQ q, hq⟩

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
