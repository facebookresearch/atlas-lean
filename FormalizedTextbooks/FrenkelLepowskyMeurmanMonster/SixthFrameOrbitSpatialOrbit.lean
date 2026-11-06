/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.SixthFrameOrbitSpatialActions
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.SixthFrameOrbitStabilizer
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.SixthFrameOrbitFrames

/-! Unconditional genuine spatial frame-orbit and monomial stabilizer lower bounds. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
set_option backward.isDefEq.respectTransparency false

/-- Every one of the 891 checked vectors is in the actual sixth spatial frame orbit. -/
theorem sixthFrameOrbitVector_mem_spatial_orbit (i : Fin 891) :
    sixthFrameOrbitVector i ∈ MulAction.orbit generatedSixthCo1SpatialStabilizer
      sixthFrameOrbitBase :=
  sixthFrameOrbitVector_mem_orbit _ _ sixthFrameOrbit_original_co1_spatial_mem
    sixthFrameOrbitOriginalGenerator_binary i

/-- All 891 checked source-word vectors belong to the genuine norm-eight frame carrier. -/
theorem sixthFrameOrbitVector_actual_frame (i : Fin 891) :
    sixthFrameOrbitVector i ∈ generatedCo1GeometryPoints :=
  sixthFrameOrbit_orbit_actual_frames _ _ (sixthFrameOrbitVector_mem_spatial_orbit i)

/-- The actual counted sixth spatial subgroup has at least 891 genuine frame-orbit elements. -/
theorem sixthFrameOrbit_spatial_card_lower :
    891 ≤ Nat.card (MulAction.orbit generatedSixthCo1SpatialStabilizer sixthFrameOrbitBase) :=
  sixthFrameOrbit_card_lower _ _ sixthFrameOrbit_original_co1_spatial_mem
    sixthFrameOrbitOriginalGenerator_binary

/-- The actual counted monomial group supplies the spatial frame stabilizer lower bound. -/
theorem sixthFrameOrbit_spatial_stabilizer_card_lower :
    20643840 ≤ Nat.card (MulAction.stabilizer generatedSixthCo1SpatialStabilizer
      sixthFrameOrbitBase) :=
  sixthFrameOrbit_stabilizer_card_lower _
    (fun k => sixthFrameOrbit_original_co1_spatial_mem (Fin.castAdd 1 k))

/-- The genuine counted spatial group has exactly 891 elements in the original frame orbit. -/
theorem sixthFrameOrbit_spatial_card :
    Nat.card (MulAction.orbit generatedSixthCo1SpatialStabilizer sixthFrameOrbitBase) = 891 := by
  let : Finite leechIsomSubgroup := leechIsomSubgroup_finite
  let _ := Fintype.ofFinite generatedSixthCo1SpatialStabilizer
  let _ := Fintype.ofFinite
    (MulAction.orbit generatedSixthCo1SpatialStabilizer sixthFrameOrbitBase)
  let _ := Fintype.ofFinite
    (MulAction.stabilizer generatedSixthCo1SpatialStabilizer sixthFrameOrbitBase)
  have hp := MulAction.card_orbit_mul_card_stabilizer_eq_card_group
    generatedSixthCo1SpatialStabilizer sixthFrameOrbitBase
  simp only [← Nat.card_eq_fintype_card] at hp
  have hs := Nat.mul_le_mul_left
    (Nat.card (MulAction.orbit generatedSixthCo1SpatialStabilizer sixthFrameOrbitBase))
    sixthFrameOrbit_spatial_stabilizer_card_lower
  rw [hp, generatedSixthCo1SpatialStabilizer_card] at hs
  have ho := sixthFrameOrbit_spatial_card_lower
  omega

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
