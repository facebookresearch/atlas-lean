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
private theorem row_18 : ∀ a : Fin 256,
    generatedRootEightMoverTensorLowPairCondition 2 0 1 18 a := by
  unfold generatedRootEightMoverTensorLowPairCondition
  decide +kernel

set_option maxHeartbeats 64000000 in
-- Check every original word prefix in this physical column.
private theorem row_19 : ∀ a : Fin 256,
    generatedRootEightMoverTensorLowPairCondition 2 0 1 19 a := by
  unfold generatedRootEightMoverTensorLowPairCondition
  decide +kernel

set_option maxHeartbeats 64000000 in
-- Check every original word prefix in this physical column.
private theorem row_20 : ∀ a : Fin 256,
    generatedRootEightMoverTensorLowPairCondition 2 0 1 20 a := by
  unfold generatedRootEightMoverTensorLowPairCondition
  decide +kernel

set_option maxHeartbeats 64000000 in
-- Check every original word prefix in this physical column.
private theorem row_21 : ∀ a : Fin 256,
    generatedRootEightMoverTensorLowPairCondition 2 0 1 21 a := by
  unfold generatedRootEightMoverTensorLowPairCondition
  decide +kernel

set_option maxHeartbeats 64000000 in
-- Check every original word prefix in this physical column.
private theorem row_22 : ∀ a : Fin 256,
    generatedRootEightMoverTensorLowPairCondition 2 0 1 22 a := by
  unfold generatedRootEightMoverTensorLowPairCondition
  decide +kernel

set_option maxHeartbeats 64000000 in
-- Check every original word prefix in this physical column.
private theorem row_23 : ∀ a : Fin 256,
    generatedRootEightMoverTensorLowPairCondition 2 0 1 23 a := by
  unfold generatedRootEightMoverTensorLowPairCondition
  decide +kernel

/-- All six physical columns retain every original prefix and signed coordinate guard. -/
theorem generatedRootEight_mover_tensor_low_pair_02_block_03
    (j : Fin 6) (a : Fin 256) :
    generatedRootEightMoverTensorLowPairCondition 2 0 1
      ⟨j.val + 18, by omega⟩ a := by
  fin_cases j
  · exact row_18 a
  · exact row_19 a
  · exact row_20 a
  · exact row_21 a
  · exact row_22 a
  · exact row_23 a

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
