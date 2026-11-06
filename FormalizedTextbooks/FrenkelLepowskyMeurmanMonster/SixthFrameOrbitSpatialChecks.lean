/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.SixthFrameOrbitSpatialData

/-! Integer certificates for genuine spatial fixation, without full spin fixation assumptions. -/

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open scoped Matrix

set_option maxHeartbeats 12000000 in
-- Check the source physical conjugate before relating it to the actual operator.
/-- The displayed Xi numerator is the exact inverse-C, source-Xi, C integer product. -/
theorem sixthFrameOrbit_spatial_xi_product :
    sixthFrameOrbitMonomialNumerator 15 * co1XiNumerator *
      sixthFrameOrbitMonomialNumerator 14 = sixthFrameOrbitSpatialNumerator 14 := by
  decide +kernel

set_option maxHeartbeats 20000000 in
-- Check all fifteen full physical commutators against the original axis matrix numerator.
/-- Every original spatial generator commutes with the literal actual sixth-axis matrix. -/
theorem sixthFrameOrbit_spatial_commute : ∀ k : Fin 15,
    sixthFrameOrbitSpatialNumerator k * sixthFrameOrbitAxisNumerator =
      sixthFrameOrbitAxisNumerator * sixthFrameOrbitSpatialNumerator k := by
  decide +kernel

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
