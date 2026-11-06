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
private theorem row_06 : ∀ a : Fin 256,
    generatedRootEightMoverTensorLowPairCondition 2 0 1 6 a := by
  unfold generatedRootEightMoverTensorLowPairCondition
  decide +kernel

set_option maxHeartbeats 64000000 in
-- Check every original word prefix in this physical column.
private theorem row_07 : ∀ a : Fin 256,
    generatedRootEightMoverTensorLowPairCondition 2 0 1 7 a := by
  unfold generatedRootEightMoverTensorLowPairCondition
  decide +kernel

set_option maxHeartbeats 64000000 in
-- Check every original word prefix in this physical column.
private theorem row_08 : ∀ a : Fin 256,
    generatedRootEightMoverTensorLowPairCondition 2 0 1 8 a := by
  unfold generatedRootEightMoverTensorLowPairCondition
  decide +kernel

set_option maxHeartbeats 64000000 in
-- Check every original word prefix in this physical column.
private theorem row_09 : ∀ a : Fin 256,
    generatedRootEightMoverTensorLowPairCondition 2 0 1 9 a := by
  unfold generatedRootEightMoverTensorLowPairCondition
  decide +kernel

set_option maxHeartbeats 64000000 in
-- Check every original word prefix in this physical column.
private theorem row_10 : ∀ a : Fin 256,
    generatedRootEightMoverTensorLowPairCondition 2 0 1 10 a := by
  unfold generatedRootEightMoverTensorLowPairCondition
  decide +kernel

set_option maxHeartbeats 64000000 in
-- Check every original word prefix in this physical column.
private theorem row_11 : ∀ a : Fin 256,
    generatedRootEightMoverTensorLowPairCondition 2 0 1 11 a := by
  unfold generatedRootEightMoverTensorLowPairCondition
  decide +kernel

/-- All six physical columns retain every original prefix and signed coordinate guard. -/
theorem generatedRootEight_mover_tensor_low_pair_02_block_01
    (j : Fin 6) (a : Fin 256) :
    generatedRootEightMoverTensorLowPairCondition 2 0 1
      ⟨j.val + 6, by omega⟩ a := by
  fin_cases j
  · exact row_06 a
  · exact row_07 a
  · exact row_08 a
  · exact row_09 a
  · exact row_10 a
  · exact row_11 a

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
