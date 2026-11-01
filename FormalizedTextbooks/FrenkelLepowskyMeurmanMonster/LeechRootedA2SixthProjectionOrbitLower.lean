/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.LeechRootedA2SixthProjection

/-! The actual counted sixth spatial group is exhausted by genuine frame orbit lower bounds. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
set_option backward.isDefEq.respectTransparency false

/-- Actual frame orbit and monomial stabilizer lower bounds exhaust the spatial projection. -/
theorem generatedSixthProjectedAxisStabilizer_eq_of_orbit_lower
    {X : Type*} [Finite X] [MulAction Co1 X] (x : X)
    (ho : 891 ≤ Nat.card (MulAction.orbit generatedSixthProjectedAxisStabilizer x))
    (hs : 20643840 ≤ Nat.card (MulAction.stabilizer generatedSixthProjectedAxisStabilizer x)) :
    generatedSixthProjectedAxisStabilizer = generatedSixthCo1SpatialStabilizer := by
  let : Finite leechIsomSubgroup := leechIsomSubgroup_finite
  let _ := Fintype.ofFinite generatedSixthProjectedAxisStabilizer
  let _ := Fintype.ofFinite (MulAction.orbit generatedSixthProjectedAxisStabilizer x)
  let _ := Fintype.ofFinite (MulAction.stabilizer generatedSixthProjectedAxisStabilizer x)
  have h := MulAction.card_orbit_mul_card_stabilizer_eq_card_group
    generatedSixthProjectedAxisStabilizer x
  simp only [← Nat.card_eq_fintype_card] at h
  have hlow := Nat.mul_le_mul ho hs
  rw [h] at hlow
  apply Subgroup.eq_of_le_of_card_ge generatedSixthProjectedAxisStabilizer_le_spatial
  rw [generatedSixthCo1SpatialStabilizer_card]
  exact hlow

/-- The same genuine orbit lower bounds give the actual full local stabilizer order. -/
theorem generatedSixthLocalAxisStabilizer_card_of_orbit_lower
    {X : Type*} [Finite X] [MulAction Co1 X] (x : X)
    (ho : 891 ≤ Nat.card (MulAction.orbit generatedSixthProjectedAxisStabilizer x))
    (hs : 20643840 ≤ Nat.card (MulAction.stabilizer generatedSixthProjectedAxisStabilizer x)) :
    Nat.card generatedSixthLocalAxisStabilizer = 73574645760 :=
  generatedSixthLocalAxisStabilizer_card_of_projection
    (generatedSixthProjectedAxisStabilizer_eq_of_orbit_lower x ho hs)

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
