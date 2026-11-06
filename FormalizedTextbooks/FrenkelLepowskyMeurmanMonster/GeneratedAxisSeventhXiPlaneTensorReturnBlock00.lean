/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisSeventhXiPlaneGaussianBitAction
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisSeventhXiPlaneTensorSparse
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisSeventhXiPlaneIntegerTensor

/-! The first finite coordinate block of the original seventh-axis tensor return. -/

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open scoped BigOperators

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Every column is retained, using the complete source-bound signed Gaussian.
/-- The first sixteen spin labels satisfy the full original tensor column return. -/
theorem generatedSeventhXiPlaneTensorReturn_block00 : ∀ b : Fin 16, ∀ j : Fin 24,
    let d : Fin 4096 := ⟨b.val, by omega⟩
    generatedSeventhXiPlaneGaussianBit (fun x => generatedSeventhXiPlaneTensorSparse x j) d =
      4 * ∑ i : Fin 24, generatedSeventhXiPlaneTensorSpatialNumerator i j *
        generatedSeventhXiPlaneTensorSparse d i := by
  decide +kernel

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
