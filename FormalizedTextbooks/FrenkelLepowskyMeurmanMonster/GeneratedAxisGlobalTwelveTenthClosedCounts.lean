/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTwelveCounts
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationTenthCCLocalOrbit

/-! All twelve actual local orbit lengths of the global catalogue are unconditional: the closed
stabilizer order of the original Tenth axis discharges the last counting input. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
set_option backward.isDefEq.respectTransparency false

/-- The catalogue Tenth representative is the original Tenth axis, of stabilizer order 2903040. -/
theorem generatedAxisGlobalTwelve_tenth_stabilizer_card_closed :
    Nat.card (MulAction.stabilizer H (generatedAxisGlobalTwelveRepresentative 11)) = 2903040 :=
  generatedTenth_actual_local_axis_stabilizer_card

/-- The catalogue Tenth orbit has its exact source length, with no remaining input. -/
theorem generatedAxisGlobalTwelve_tenth_orbit_card_closed :
    Nat.card (generatedAxisGlobalTwelveOrbit 11) = generatedAxisGlobalTwelveCount 11 :=
  generatedAxisGlobalTwelve_tenth_orbit_card generatedTenth_actual_local_axis_stabilizer_card

/-- All twelve listed local orbits have their exact source lengths, with no remaining input. -/
theorem generatedAxisGlobalTwelveCounted_closed : GeneratedAxisGlobalTwelveCounted :=
  generatedAxisGlobalTwelveCounted_of_tenth generatedTenth_actual_local_axis_stabilizer_card

/-- Each of the twelve listed local orbit lengths, unconditionally. -/
theorem generatedAxisGlobalTwelve_card_closed (i : Fin 12) :
    Nat.card (generatedAxisGlobalTwelveOrbit i) = generatedAxisGlobalTwelveCount i :=
  generatedAxisGlobalTwelveCounted_closed i

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
