/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisRootEightMoverTensorLowPairCondition

/-! Complete original corrected mover low-pair word checks, including every signed slot. -/
@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open scoped BigOperators
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 100000

set_option maxHeartbeats 64000000 in
-- Check every original word prefix in this physical column.
private theorem row_00 : ∀ a : Fin 256,
    generatedRootEightMoverTensorLowPairCondition 1 2 3 0 a := by
  unfold generatedRootEightMoverTensorLowPairCondition
  decide +kernel

set_option maxHeartbeats 64000000 in
-- Check every original word prefix in this physical column.
private theorem row_01 : ∀ a : Fin 256,
    generatedRootEightMoverTensorLowPairCondition 1 2 3 1 a := by
  unfold generatedRootEightMoverTensorLowPairCondition
  decide +kernel

set_option maxHeartbeats 64000000 in
-- Check every original word prefix in this physical column.
private theorem row_02 : ∀ a : Fin 256,
    generatedRootEightMoverTensorLowPairCondition 1 2 3 2 a := by
  unfold generatedRootEightMoverTensorLowPairCondition
  decide +kernel

set_option maxHeartbeats 64000000 in
-- Check every original word prefix in this physical column.
private theorem row_03 : ∀ a : Fin 256,
    generatedRootEightMoverTensorLowPairCondition 1 2 3 3 a := by
  unfold generatedRootEightMoverTensorLowPairCondition
  decide +kernel

set_option maxHeartbeats 64000000 in
-- Check every original word prefix in this physical column.
private theorem row_04 : ∀ a : Fin 256,
    generatedRootEightMoverTensorLowPairCondition 1 2 3 4 a := by
  unfold generatedRootEightMoverTensorLowPairCondition
  decide +kernel

set_option maxHeartbeats 64000000 in
-- Check every original word prefix in this physical column.
private theorem row_05 : ∀ a : Fin 256,
    generatedRootEightMoverTensorLowPairCondition 1 2 3 5 a := by
  unfold generatedRootEightMoverTensorLowPairCondition
  decide +kernel

/-- All six physical columns retain every original prefix and signed coordinate guard. -/
theorem generatedRootEight_mover_tensor_low_pair_01_block_00
    (j : Fin 6) (a : Fin 256) :
    generatedRootEightMoverTensorLowPairCondition 1 2 3
      ⟨j.val + 0, by omega⟩ a := by
  fin_cases j
  · exact row_00 a
  · exact row_01 a
  · exact row_02 a
  · exact row_03 a
  · exact row_04 a
  · exact row_05 a

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
