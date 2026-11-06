/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.SixthFrameOrbitSpatialOrbit

/-! Exact order of the genuine spatial stabilizer of the original coordinate frame. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster

/-- The actual spatial frame stabilizer has exactly the counted monomial order. -/
theorem sixthFrameOrbit_spatial_stabilizer_card :
    Nat.card (MulAction.stabilizer generatedSixthCo1SpatialStabilizer sixthFrameOrbitBase) =
      20643840 := by
  let : Finite leechIsomSubgroup := leechIsomSubgroup_finite
  let _ := Fintype.ofFinite generatedSixthCo1SpatialStabilizer
  let _ := Fintype.ofFinite
    (MulAction.orbit generatedSixthCo1SpatialStabilizer sixthFrameOrbitBase)
  let _ := Fintype.ofFinite
    (MulAction.stabilizer generatedSixthCo1SpatialStabilizer sixthFrameOrbitBase)
  have hp := MulAction.card_orbit_mul_card_stabilizer_eq_card_group
    generatedSixthCo1SpatialStabilizer sixthFrameOrbitBase
  simp only [← Nat.card_eq_fintype_card] at hp
  rw [sixthFrameOrbit_spatial_card, generatedSixthCo1SpatialStabilizer_card] at hp
  omega

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
