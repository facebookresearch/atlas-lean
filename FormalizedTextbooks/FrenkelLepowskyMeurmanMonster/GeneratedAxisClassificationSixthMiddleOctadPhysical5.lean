/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationSixthMiddleOctadData

/-! Bounded original-coordinate certificate for octad image batch 5. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 100000

set_option maxHeartbeats 8000000 in
-- Check 39 actual octad images on all 24 original physical coordinates.
/-- Every batch-5 image equals the actual frame-column sum with its physical sign. -/
theorem generatedSixth_middle_octad_physical_certificate5 : ∀ k : Fin 39, ∀ i : Fin 24,
    let n : Fin 273 := ⟨195 + k.val, by omega⟩
    generatedSixthFrameVectorData 8 (generatedSixthMiddleOctadSourceCoordinates n).2.1 i +
      (if (generatedSixthMiddleOctadSourceCoordinates n).1 = 0 then -1 else 1) *
        generatedSixthFrameVectorData 8 (generatedSixthMiddleOctadSourceCoordinates n).2.2 i =
      2 * generatedSixthMiddleOctadPhysicalSign n *
        generatedSixthMiddleOctadIntegral n i := by
  decide +kernel

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
