/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.SixthFrameOrbitDataIntegral

/-! Exact integer certificates on the original integral Leech basis. -/

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open scoped Matrix

set_option maxRecDepth 10000 in
set_option maxHeartbeats 40000000 in
-- Check sixteen complete 24-dimensional original integral basis actions.
/-- Every certified integer basis matrix realizes the displayed physical signed permutation. -/
theorem sixthFrameOrbit_integral_check : ∀ k : Fin 16, ∀ i j : Fin 24,
    (leechBasisMatrix * sixthFrameOrbitIntegral k) i j =
      sixthFrameOrbitSpatialSign k i * leechBasisMatrix (sixthFrameOrbitSpatialInput k i) j := by
  decide +kernel

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
