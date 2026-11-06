/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTwelveCatalogue
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationNinthActualLocalOrbit
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisRootEightActualLocalCount

/-! The closed Ninth and Root8 local counts discharge their catalogue inputs.
Eleven of the twelve actual local orbit lengths are therefore unconditional; the Tenth
stabilizer order remains the only explicit counting input. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
set_option backward.isDefEq.respectTransparency false

/-- Every listed local orbit other than Tenth has its exact source length. -/
theorem generatedAxisGlobalTwelve_card_unconditional (i : Fin 12) (hi : i ≠ 11) :
    Nat.card (generatedAxisGlobalTwelveOrbit i) = generatedAxisGlobalTwelveCount i :=
  generatedAxisGlobalTwelve_card_of_ne_tenth generatedNinth_actual_local_axis_orbit_card
    generatedRootEight_actual_local_axis_orbit_card i hi

/-- The Tenth stabilizer order is the only remaining input for all twelve lengths. -/
theorem generatedAxisGlobalTwelveCounted_of_tenth
    (htenth : Nat.card (MulAction.stabilizer H generatedTenthAxis) = 2903040) :
    GeneratedAxisGlobalTwelveCounted :=
  generatedAxisGlobalTwelveCounted_of generatedNinth_actual_local_axis_orbit_card
    generatedRootEight_actual_local_axis_orbit_card htenth

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
