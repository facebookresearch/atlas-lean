/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationFifthEvenRootData

/-! Exact kernel checks of the 56 transformed octad-root physical vectors. -/

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open scoped Matrix

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
-- Verify all 1344 actual integer coordinates of the inverse physical images.
/-- The listed octad roots have the exact original inverse integer images. -/
theorem generatedFifth_even_inverse_integral_certificate : ∀ j : Fin 56, ∀ i : Fin 24,
    (generatedFifthInverseNumerator *ᵥ generatedFifthEvenRootIntegral j) i =
      4 * generatedFifthEvenRootPhysicalSign j *
        generatedFourthInputIntegral (generatedFifthEvenRootInputData j) i := by
  decide +kernel

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
