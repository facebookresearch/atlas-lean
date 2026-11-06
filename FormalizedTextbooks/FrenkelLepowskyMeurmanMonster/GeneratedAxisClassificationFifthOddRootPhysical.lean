/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationFifthOddRootData

/-! Kernel checks of the 64 actual transformed odd-root physical vectors. -/

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open scoped Matrix

set_option maxRecDepth 10000 in
set_option maxHeartbeats 12000000 in
-- Check all 1,536 integer coordinates of the inverse images of the 64 odd roots.
/-- Every listed odd root has exactly the listed physical inverse image. -/
theorem generatedFifth_odd_inverse_integral_certificate : ∀ j : Fin 64, ∀ i : Fin 24,
    (generatedFifthInverseNumerator *ᵥ
      griessShortIntegral (generatedFifthOddRootOutputLabel j)) i =
        4 * generatedFifthOddRootPhysicalSign j * generatedFifthOddRootInputIntegral j i := by
  decide +kernel

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
