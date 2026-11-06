/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationFourthLiftShortFastImage

/-! A bounded full preferred-Q certificate using the unchanged literal phase matrices. -/

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
set_option maxRecDepth 100000

set_option maxHeartbeats 8000000 in
-- Include every central phase of the actual corrected y82, permutation and Xi factors.
/-- A literal-matrix check of the first actual preferred octad image. -/
theorem generatedFourth_lift_short_fast_first_image :
    generatedFourthLiftShortQFast (generatedFourthLiftShortSourceQ 0 0) =
      generatedFourthLiftShortSourceQ 0 33 := by
  apply NormalizedCocycleExtension.Extension.ext
  · apply Multiplicative.toAdd.injective
    decide +kernel
  · apply Multiplicative.toAdd.injective
    decide +kernel

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
