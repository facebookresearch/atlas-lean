/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTransitionsOddComparisonPairingData

/-! Complete exact original matrix pairing certificate for comparison 1. -/

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster

set_option maxHeartbeats 20000000 in
set_option maxRecDepth 10000 in
/-- The entire genuine matrix constituent has its exact original source pairing. -/
theorem generatedAxisGlobalOddComparison01MatrixPairing :
    generatedAxisGlobalOddComparisonMatrixPairingQ 1 = (13 / 2 : ℚ) := by
  decide +kernel

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
