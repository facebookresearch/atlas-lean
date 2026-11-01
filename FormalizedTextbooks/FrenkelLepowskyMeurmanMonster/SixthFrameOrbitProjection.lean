/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.SixthFrameOrbitStabilizer
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.LeechRootedA2SixthProjectionOrbitLower

/-! The actual frame tree and counted monomial subgroup exhaust the sixth spatial projection. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster

/-- Genuine corrected full-axis memberships imply the actual 891-element frame orbit bound. -/
theorem sixthFrameOrbit_projected_card_lower_of_corrected
    (h : ∀ j : Fin 5, projH (localFiberIntoH (generatedSixthCorrectedGenerator j)) ∈
      generatedSixthProjectedAxisStabilizer) :
    891 ≤ Nat.card (MulAction.orbit generatedSixthProjectedAxisStabilizer
      sixthFrameOrbitBase) :=
  sixthFrameOrbit_card_lower _ _ (sixthFrameOrbit_generators_mem_of_corrected h)
    sixthFrameOrbitOriginalGenerator_binary

/-- The same genuine memberships supply the counted monomial restricted stabilizer bound. -/
theorem sixthFrameOrbit_projected_stabilizer_lower_of_corrected
    (h : ∀ j : Fin 5, projH (localFiberIntoH (generatedSixthCorrectedGenerator j)) ∈
      generatedSixthProjectedAxisStabilizer) :
    20643840 ≤ Nat.card (MulAction.stabilizer generatedSixthProjectedAxisStabilizer
      sixthFrameOrbitBase) :=
  sixthFrameOrbit_stabilizer_card_lower _
    (fun k => sixthFrameOrbit_generators_mem_of_corrected h (Fin.castAdd 1 k))

/-- Once those five actual memberships are supplied, the actual counted projection is exhausted. -/
theorem sixthFrameOrbit_projection_eq_of_corrected
    (h : ∀ j : Fin 5, projH (localFiberIntoH (generatedSixthCorrectedGenerator j)) ∈
      generatedSixthProjectedAxisStabilizer) :
    generatedSixthProjectedAxisStabilizer = generatedSixthCo1SpatialStabilizer :=
  generatedSixthProjectedAxisStabilizer_eq_of_orbit_lower sixthFrameOrbitBase
    (sixthFrameOrbit_projected_card_lower_of_corrected h)
    (sixthFrameOrbit_projected_stabilizer_lower_of_corrected h)

/-- The full actual local order follows from precisely those five remaining memberships. -/
theorem sixthFrameOrbit_local_card_of_corrected
    (h : ∀ j : Fin 5, projH (localFiberIntoH (generatedSixthCorrectedGenerator j)) ∈
      generatedSixthProjectedAxisStabilizer) :
    Nat.card generatedSixthLocalAxisStabilizer = 73574645760 :=
  generatedSixthLocalAxisStabilizer_card_of_projection
    (sixthFrameOrbit_projection_eq_of_corrected h)

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
