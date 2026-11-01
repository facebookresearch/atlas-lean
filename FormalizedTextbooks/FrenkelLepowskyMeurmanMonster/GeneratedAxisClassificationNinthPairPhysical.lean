/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationNinthPairData

/-! Every denominator-cleared inverse pair row follows the original source matrix. -/

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open scoped Matrix
set_option backward.isDefEq.respectTransparency false

set_option maxRecDepth 20000 in
set_option maxHeartbeats 16000000 in
-- Check every original inverse pair against its genuine preferred source coordinates.
/-- The complete 552 inverse-pair certificates preserve the full physical sign. -/
theorem generatedNinth_pair_inverse_certificate : ∀ r : Fin 552, ∀ i : Fin 24,
    4 * generatedNinthInverseNumerator i (generatedNinthPairTarget r).2.1 +
      (if (generatedNinthPairTarget r).1 = 0 then -4 else 4) *
        generatedNinthInverseNumerator i (generatedNinthPairTarget r).2.2 =
      8 * generatedNinthPairPhysicalSign r *
        generatedNinthInputShortIntegral (generatedNinthPairSource r) i := by
  decide +kernel

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
