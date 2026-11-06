/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedOrbitCoverage
public import Mathlib.GroupTheory.Index

/-! The two-axis orbit--stabilizer identity used in Höhn--Seysen,
arXiv:2508.01037, Theorem 5.1, for the actual named Griess representation.
The two orbit cardinalities and the common stabilizer are not prescribed. -/

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
set_option backward.isDefEq.respectTransparency false

/-- The actual subgroup of G fixing the specified vector. -/
noncomputable def generatedVectorStabilizer (a : GriessSpace) : Subgroup G :=
  MulAction.stabilizer G a

/-- The actual orbit of the second vector under the first vector's stabilizer. -/
noncomputable def generatedFeasibleVectorOrbit (a b : GriessSpace) : Set GriessSpace :=
  MulAction.orbit (generatedVectorStabilizer a) b

/-- The actual common stabilizer, regarded as a subgroup of the first stabilizer. -/
noncomputable def generatedVectorPairStabilizer (a b : GriessSpace) :
    Subgroup (generatedVectorStabilizer a) :=
  MulAction.stabilizer (generatedVectorStabilizer a) b

theorem generatedVectorOrbit_eq_action_orbit (a : GriessSpace) :
    generatedVectorOrbit a = MulAction.orbit G a := by
  ext x
  exact MulAction.mem_orbit_iff.symm

theorem generatedVectorStabilizer_index (a : GriessSpace) :
    (generatedVectorStabilizer a).index = Nat.card (generatedVectorOrbit a) := by
  rw [generatedVectorStabilizer, MulAction.index_stabilizer,
    ← Nat.card_coe_set_eq, generatedVectorOrbit_eq_action_orbit]

/-- First actual orbit--stabilizer count. -/
theorem generated_card_eq_vector_orbit_mul_stabilizer (a : GriessSpace) :
    Nat.card G = Nat.card (generatedVectorOrbit a) * Nat.card (generatedVectorStabilizer a) := by
  rw [← (generatedVectorStabilizer a).index_mul_card, generatedVectorStabilizer_index]

/-- Exact two-vector counting. Instantiating the source axes does not require
recognizing either stabilizer as the Baby Monster or assuming any global order. -/
theorem generated_card_eq_two_vector_orbits_mul_pair_stabilizer (a b : GriessSpace) :
    Nat.card G = Nat.card (generatedVectorOrbit a) *
      Nat.card (generatedFeasibleVectorOrbit a b) *
      Nat.card (generatedVectorPairStabilizer a b) := by
  have hindex : (generatedVectorPairStabilizer a b).index =
      Nat.card (generatedFeasibleVectorOrbit a b) := by
    rw [generatedVectorPairStabilizer, MulAction.index_stabilizer, ← Nat.card_coe_set_eq]
    rfl
  rw [generated_card_eq_vector_orbit_mul_stabilizer,
    ← (generatedVectorPairStabilizer a b).index_mul_card, hindex, mul_assoc]

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
