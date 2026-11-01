/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationNinthSpreadSystemColumns

/-! Compact ordinary-kernel source-system action for original section letter 5. -/

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open scoped Matrix
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 100000

set_option maxHeartbeats 100000000 in
-- Compare the original eight-bit images of 270 bases, each with four columns.
/-- Every source basis label has its stated original-letter image and target coefficients. -/
theorem generatedNinth_spread_system_packet_05 : ∀ k : Fin 270, ∀ j : Fin 4,
    sixthFrameOrbitMaskApply (generatedNinthSpreadColumns 5)
      (generatedAxisE8FrameSystemBasisLabels k j).val =
        (generatedAxisE8FrameSystemCandidateLabel (generatedNinthSpreadSystemTarget 5 k)
          (generatedNinthSpreadSystemCoefficient 5 k j)).val := by
  decide +kernel

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
