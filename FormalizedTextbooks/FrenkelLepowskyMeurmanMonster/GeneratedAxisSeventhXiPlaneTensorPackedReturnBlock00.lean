/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisSeventhXiPlaneGaussianPackedAction
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisSeventhXiPlaneTensorPackedCoordinates
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisSeventhXiPlaneIntegerTensor

/-! The first complete column-return block using source-bound packed evaluations. -/

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open scoped BigOperators

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- All twenty-four columns and every original Gaussian phase are retained.
/-- The first sixteen original spin labels satisfy the exact packed tensor return. -/
theorem generatedSeventhXiPlaneTensorPackedReturn_block00 : ∀ b : Fin 16, ∀ j : Fin 24,
    let d : Fin 4096 := ⟨b.val, by omega⟩
    generatedSeventhXiPlaneGaussianPacked (fun x => generatedSeventhXiPlaneTensorPacked x j) d =
      4 * ∑ i : Fin 24, generatedSeventhXiPlaneTensorSpatialNumerator i j *
        generatedSeventhXiPlaneTensorPacked d i := by
  decide +kernel

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
