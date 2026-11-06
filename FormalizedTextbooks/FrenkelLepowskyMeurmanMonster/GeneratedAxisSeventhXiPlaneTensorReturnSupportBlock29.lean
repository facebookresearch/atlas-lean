/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisSeventhXiPlaneTensorReturnData
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisSeventhXiPlaneTensorSupportParameters

/-! Exact original tensor returns for free support parameters 464 through 479. -/

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Every physical column and every genuine Pauli phase is retained in this block.
/-- All sixteen actual support labels in block 29 satisfy the complete original tensor return. -/
theorem generatedSeventhXiPlaneTensorReturnSupport_block29 : ∀ r : Fin 16, ∀ j : Fin 24,
    let d := generatedSeventhXiTensorSupportLabel ⟨464 + r.val, by omega⟩
    generatedSeventhXiPlaneTensorReturnLeft d j = generatedSeventhXiPlaneTensorReturnRight d j := by
  decide +kernel

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
