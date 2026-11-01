/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisPairLocal
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedOrbitStabilizers

/-! The actual two-axis counting identity with the now-proved local pair stabilizer. -/

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
set_option backward.isDefEq.respectTransparency false

/-- Identifying the nested common stabilizer with the genuine subgroup fixing both axes. -/
noncomputable def generatedAxisPairStabilizerEquiv (p : Fin 276) :
    generatedVectorPairStabilizer (conwayShortAxis (Sum.inl (0, p)) 0)
      (conwayShortAxis (Sum.inl (0, p)) 1) ≃* generatedShortAxisPairStabilizer p where
  toFun x := ⟨x.val.val, x.val.property, x.property⟩
  invFun y := ⟨⟨y.val, y.property.1⟩, y.property.2⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_mul' _ _ := rfl

/-- The two global orbit sizes are the only still-uncomputed factors in this
actual order identity; the common stabilizer is proved to be the local one. -/
theorem generated_card_eq_actual_axis_orbits (p : Fin 276) :
    Nat.card G =
      Nat.card (generatedVectorOrbit (conwayShortAxis (Sum.inl (0, p)) 0)) *
      Nat.card (generatedFeasibleVectorOrbit (conwayShortAxis (Sum.inl (0, p)) 0)
        (conwayShortAxis (Sum.inl (0, p)) 1)) *
      (2 ^ 24 * Nat.card (co2ShortStabilizer (Sum.inl (0, p)))) := by
  rw [generated_card_eq_two_vector_orbits_mul_pair_stabilizer,
    Nat.card_congr (generatedAxisPairStabilizerEquiv p).toEquiv,
    generatedShortAxisPairStabilizer_card_relation]

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
