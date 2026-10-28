/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationFourthLiftShortBinaryData

/-! Bounded actual preferred-Q binary-cache certificate block 4. -/

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster

set_option maxRecDepth 100000 in
set_option maxHeartbeats 32000000 in
-- All twenty-four intrinsic coordinates are compared at every original sign in seven families.
/-- Genuine preferred-Q binary coordinates for listed rows 28 through 34. -/
theorem generatedFourth_lift_short_binary_certificate_4 :
    ∀ k : Fin 7, ∀ e : Fin 64,
      let j : Fin 63 := ⟨28 + k.val, by omega⟩
      Multiplicative.toAdd (generatedFourthLiftShortOctadQFast j e).base =
        Multiplicative.toAdd (generatedFourthLiftShortOctadQPacked j e).base := by
  decide +kernel

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
