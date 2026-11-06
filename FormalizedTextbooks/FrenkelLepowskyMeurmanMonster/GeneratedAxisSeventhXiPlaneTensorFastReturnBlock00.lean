/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisSeventhXiPlaneTensorReturnData

/-! The first complete source return block with every original Gaussian and spatial term. -/

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- All twenty-four columns and every original full-phase Pauli summand are retained.
/-- The first sixteen original spin labels satisfy the exact full tensor return. -/
theorem generatedSeventhXiPlaneTensorFastReturn_block00 : ∀ b : Fin 16, ∀ j : Fin 24,
    let d : Fin 4096 := ⟨b.val, by omega⟩
    generatedSeventhXiPlaneTensorReturnLeft d j = generatedSeventhXiPlaneTensorReturnRight d j := by
  decide +kernel

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
