/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/- Exact original-E7 letter restrictions for finite local table-edge coefficients. -/
module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.Y555LocalPresentationTCIndexCoefficientCheck

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster

set_option maxRecDepth 100000 in
set_option maxHeartbeats 8000000 in
-- The kernel checks finite literal coefficient alphabets and separates the last padding positions.
/-- All actual coefficient letters in edge block 67 belong to the E7 source prefix. -/
theorem y322TCIndexCoefficientAllowed67 (i : Fin 256) :
    y322TCIndexCoefficientAllowedAt (17152 + i.val) := by
  revert i
  decide +kernel

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
