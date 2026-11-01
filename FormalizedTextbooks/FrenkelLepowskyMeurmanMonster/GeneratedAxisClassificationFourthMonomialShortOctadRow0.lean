/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationFourthMonomialShortPacked
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationFourthMonomialShortTargets0

/-! Exact original full-phase checks on the first genuine octad family for monomial word zero. -/

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster

set_option maxRecDepth 20000 in
set_option maxHeartbeats 16000000 in
-- Bound the first check to the64 actual preferred signs of one short family.
/-- The first actual family has its full intrinsic Q images and signed coefficients verified. -/
theorem generatedFourth_monomial_short_octad_row0 : ∀ e : Fin 64,
    generatedFourthMonomialShortMatchPacked 0 (generatedFourthLiftShortOctadQPacked 0 e)
      (generatedFourthLiftShortOctadNumerator 0 e)
      (generatedFourthMonomialShortOctadTargets0 0 e) := by
  decide +kernel

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
