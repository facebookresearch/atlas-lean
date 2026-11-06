/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.LeechNormEightCountTypes

/-! The final counting weights, summed over the actual Golay encoding. -/

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open scoped BigOperators

/-- The five actual Golay weights. -/
def leechNormEightGolayWeights : Fin 5 → Fin 25 := ![0, 8, 12, 16, 24]

/-- Even-source counts for one word of the indicated weight. -/
def leechNormEightEvenContribution (w : ℕ) : ℕ :=
  if w = 0 then 170064 else if w = 8 then 62464 else if w = 12 then 49152
  else if w = 16 then 32768 else 0

/-- Each allowed odd-source word has the same number of norm-eight solutions. -/
def leechNormEightWordContribution (m : Bool) (w : ℕ) : ℕ :=
  if m then 48576 else leechNormEightEvenContribution w

set_option maxRecDepth 100000 in
set_option maxHeartbeats 80000000 in
-- The finite sum checks all4096 words of the actual Golay encoder.
/-- Exact sum over all4096 words from the actual Golay encoding. -/
theorem leechNormEightContribution_sum :
    (∑ d : Fin 4096,
      (leechNormEightEvenContribution (golayMaskWeight (golayEncodedMask d.val)) + 48576)) =
      398034000 := by
  decide +kernel

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
