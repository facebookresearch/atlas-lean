/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTransitionsOddComparisonTensorFactors
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTransitionsOddComparison00TensorData
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTransitionsOddRoot00SpinStateData

/-! Bounded original source spin coefficients for comparison 0, physical block 2. -/

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster

set_option maxHeartbeats 20000000 in
set_option maxRecDepth 10000 in
/-- Every coordinate in this bounded block has its full original source correction phase. -/
theorem generatedAxisGlobalOddComparison00FactorBlock02 (i : Fin 256) :
    generatedAxisGlobalOddComparisonSpinInteger 0
        generatedAxisGlobalOddRoot00Spin12
        ⟨256 * 2 + i.val, by omega⟩ =
      generatedAxisGlobalOddComparison00Spin ⟨256 * 2 + i.val, by omega⟩ := by
  revert i
  decide +kernel

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
