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
private theorem row_12 : ∀ a : Fin 256,
    generatedRootEightMoverPackedSpatialCondition 12 a := by
  unfold generatedRootEightMoverPackedSpatialCondition
  decide +kernel

set_option maxHeartbeats 64000000 in
-- Check every original word prefix with all24 genuine physical coefficients.
private theorem row_13 : ∀ a : Fin 256,
    generatedRootEightMoverPackedSpatialCondition 13 a := by
  unfold generatedRootEightMoverPackedSpatialCondition
  decide +kernel

set_option maxHeartbeats 64000000 in
-- Check every original word prefix with all24 genuine physical coefficients.
private theorem row_14 : ∀ a : Fin 256,
    generatedRootEightMoverPackedSpatialCondition 14 a := by
  unfold generatedRootEightMoverPackedSpatialCondition
  decide +kernel

set_option maxHeartbeats 64000000 in
-- Check every original word prefix with all24 genuine physical coefficients.
private theorem row_15 : ∀ a : Fin 256,
    generatedRootEightMoverPackedSpatialCondition 15 a := by
  unfold generatedRootEightMoverPackedSpatialCondition
  decide +kernel

set_option maxHeartbeats 64000000 in
-- Check every original word prefix with all24 genuine physical coefficients.
private theorem row_16 : ∀ a : Fin 256,
    generatedRootEightMoverPackedSpatialCondition 16 a := by
  unfold generatedRootEightMoverPackedSpatialCondition
  decide +kernel

set_option maxHeartbeats 64000000 in
-- Check every original word prefix with all24 genuine physical coefficients.
private theorem row_17 : ∀ a : Fin 256,
    generatedRootEightMoverPackedSpatialCondition 17 a := by
  unfold generatedRootEightMoverPackedSpatialCondition
  decide +kernel

/-- Every prefix and signed spatial equation for six complete physical output rows is checked. -/
theorem generatedRootEight_mover_packed_spatial_block_02 (i : Fin 6) (a : Fin 256) :
    generatedRootEightMoverPackedSpatialCondition ⟨i.val + 12, by omega⟩ a := by
  fin_cases i
  · exact row_12 a
  · exact row_13 a
  · exact row_14 a
  · exact row_15 a
  · exact row_16 a
  · exact row_17 a

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
