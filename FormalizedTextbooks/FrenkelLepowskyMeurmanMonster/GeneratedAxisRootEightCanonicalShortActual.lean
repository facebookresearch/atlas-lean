/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisRootEightPositiveFinalShortSourceActual
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisRootEightCanonicalShortSupportActual
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisRootEightShortSupportCountActual

/-! Unconditional complete original canonical short coordinates. -/
@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster

/-- Every actual canonical short coordinate equals the exact integer cache, including every zero. -/
theorem generatedRootEight_canonical_short_actual (r : GriessShortIndex) :
    (griessConwayEncode generatedRootEightCanonicalPositiveAxis).2.1 r =
      (generatedRootEightCanonicalShortCachedNumerator r : ℝ) / 256 := by
  exact generatedRootEight_canonical_short_cache_of_support
    generatedRootEight_positive_final_short_source_actual
    generatedRootEight_short_support_cards_equal
    generatedRootEight_canonical_short_support_actual r

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
