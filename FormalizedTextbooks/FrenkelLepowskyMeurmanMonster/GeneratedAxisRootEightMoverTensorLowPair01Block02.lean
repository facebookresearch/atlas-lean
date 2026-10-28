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
private theorem row_12 : ∀ a : Fin 256,
    generatedRootEightMoverTensorLowPairCondition 1 2 3 12 a := by
  unfold generatedRootEightMoverTensorLowPairCondition
  decide +kernel

set_option maxHeartbeats 64000000 in
-- Check every original word prefix in this physical column.
private theorem row_13 : ∀ a : Fin 256,
    generatedRootEightMoverTensorLowPairCondition 1 2 3 13 a := by
  unfold generatedRootEightMoverTensorLowPairCondition
  decide +kernel

set_option maxHeartbeats 64000000 in
-- Check every original word prefix in this physical column.
private theorem row_14 : ∀ a : Fin 256,
    generatedRootEightMoverTensorLowPairCondition 1 2 3 14 a := by
  unfold generatedRootEightMoverTensorLowPairCondition
  decide +kernel

set_option maxHeartbeats 64000000 in
-- Check every original word prefix in this physical column.
private theorem row_15 : ∀ a : Fin 256,
    generatedRootEightMoverTensorLowPairCondition 1 2 3 15 a := by
  unfold generatedRootEightMoverTensorLowPairCondition
  decide +kernel

set_option maxHeartbeats 64000000 in
-- Check every original word prefix in this physical column.
private theorem row_16 : ∀ a : Fin 256,
    generatedRootEightMoverTensorLowPairCondition 1 2 3 16 a := by
  unfold generatedRootEightMoverTensorLowPairCondition
  decide +kernel

set_option maxHeartbeats 64000000 in
-- Check every original word prefix in this physical column.
private theorem row_17 : ∀ a : Fin 256,
    generatedRootEightMoverTensorLowPairCondition 1 2 3 17 a := by
  unfold generatedRootEightMoverTensorLowPairCondition
  decide +kernel

/-- All six physical columns retain every original prefix and signed coordinate guard. -/
theorem generatedRootEight_mover_tensor_low_pair_01_block_02
    (j : Fin 6) (a : Fin 256) :
    generatedRootEightMoverTensorLowPairCondition 1 2 3
      ⟨j.val + 12, by omega⟩ a := by
  fin_cases j
  · exact row_12 a
  · exact row_13 a
  · exact row_14 a
  · exact row_15 a
  · exact row_16 a
  · exact row_17 a

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
