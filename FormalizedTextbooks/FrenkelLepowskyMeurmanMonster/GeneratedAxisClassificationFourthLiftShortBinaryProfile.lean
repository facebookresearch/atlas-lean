/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationFourthLiftShortBinaryData

/-! A bounded actual preferred-Q binary-cache certificate. -/

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster

set_option maxRecDepth 100000 in
set_option maxHeartbeats 16000000 in
-- All twenty-four intrinsic coordinates are compared at every original sign.
/-- Every first-family packed binary coordinate equals the genuine preferred coordinate. -/
theorem generatedFourth_lift_short_binary_profile :
    ∀ e : Fin 64, Multiplicative.toAdd (generatedFourthLiftShortOctadQFast 0 e).base =
      Multiplicative.toAdd (generatedFourthLiftShortOctadQPacked 0 e).base := by
  decide +kernel

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
