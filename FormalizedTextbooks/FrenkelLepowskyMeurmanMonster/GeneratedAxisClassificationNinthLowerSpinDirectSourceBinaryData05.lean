/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationNinthLowerSpinDirectCompactBinaryData05
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationNinthAffineLowerFiberActions

/-! Complete original binary intertwining for the oriented lattice candidate 5. -/

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open scoped Matrix
set_option backward.isDefEq.respectTransparency false

set_option maxRecDepth 100000 in
set_option maxHeartbeats 16000000 in
-- Compare complete actual source columns with two single finite matrix products.
private theorem source_intertwining :
    sixthFrameOrbitColumnMatrix generatedNinthAffineTransportBinaryColumns *
      generatedNinthLowerSpinDirectCompactBinaryMatrix 5 =
      sixthFrameOrbitColumnMatrix (generatedNinthAffineLowerSourceColumns 5) *
        sixthFrameOrbitColumnMatrix generatedNinthAffineTransportBinaryColumns := by
  decide +kernel

/-- The complete candidate action is conjugate to the original whole source action. -/
theorem generatedNinth_lower_spin_direct_source_binary_certificate_05 :
    sixthFrameOrbitColumnMatrix generatedNinthAffineTransportBinaryColumns *
      (leechHyperbolicInverse *
        generatedNinthLowerSpinDirectIntegralMatrix05.map (Int.castRingHom (ZMod 2)) *
          leechHyperbolicMatrix) =
      sixthFrameOrbitColumnMatrix (generatedNinthAffineLowerSourceColumns 5) *
        sixthFrameOrbitColumnMatrix generatedNinthAffineTransportBinaryColumns := by
  rw [generatedNinth_lower_spin_direct_compact_binary_matrix_05]
  exact source_intertwining

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
