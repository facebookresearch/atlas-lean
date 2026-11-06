/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisRootEightMoverPackedSpatialCondition

/-! Exact original mover tensor boundaries and positive spatial coefficients. -/
@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open scoped BigOperators
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 100000

set_option maxHeartbeats 64000000 in
-- Check every original word prefix with all24 genuine physical coefficients.
private theorem row_06 : ∀ a : Fin 256,
    generatedRootEightMoverPackedSpatialCondition 6 a := by
  unfold generatedRootEightMoverPackedSpatialCondition
  decide +kernel

set_option maxHeartbeats 64000000 in
-- Check every original word prefix with all24 genuine physical coefficients.
private theorem row_07 : ∀ a : Fin 256,
    generatedRootEightMoverPackedSpatialCondition 7 a := by
  unfold generatedRootEightMoverPackedSpatialCondition
  decide +kernel

set_option maxHeartbeats 64000000 in
-- Check every original word prefix with all24 genuine physical coefficients.
private theorem row_08 : ∀ a : Fin 256,
    generatedRootEightMoverPackedSpatialCondition 8 a := by
  unfold generatedRootEightMoverPackedSpatialCondition
  decide +kernel

set_option maxHeartbeats 64000000 in
-- Check every original word prefix with all24 genuine physical coefficients.
private theorem row_09 : ∀ a : Fin 256,
    generatedRootEightMoverPackedSpatialCondition 9 a := by
  unfold generatedRootEightMoverPackedSpatialCondition
  decide +kernel

set_option maxHeartbeats 64000000 in
-- Check every original word prefix with all24 genuine physical coefficients.
private theorem row_10 : ∀ a : Fin 256,
    generatedRootEightMoverPackedSpatialCondition 10 a := by
  unfold generatedRootEightMoverPackedSpatialCondition
  decide +kernel

set_option maxHeartbeats 64000000 in
-- Check every original word prefix with all24 genuine physical coefficients.
private theorem row_11 : ∀ a : Fin 256,
    generatedRootEightMoverPackedSpatialCondition 11 a := by
  unfold generatedRootEightMoverPackedSpatialCondition
  decide +kernel

/-- Every prefix and signed spatial equation for six complete physical output rows is checked. -/
theorem generatedRootEight_mover_packed_spatial_block_01 (i : Fin 6) (a : Fin 256) :
    generatedRootEightMoverPackedSpatialCondition ⟨i.val + 6, by omega⟩ a := by
  fin_cases i
  · exact row_06 a
  · exact row_07 a
  · exact row_08 a
  · exact row_09 a
  · exact row_10 a
  · exact row_11 a

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
