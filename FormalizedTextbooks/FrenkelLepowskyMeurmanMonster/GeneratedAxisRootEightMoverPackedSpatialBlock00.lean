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
private theorem row_00 : ∀ a : Fin 256,
    generatedRootEightMoverPackedSpatialCondition 0 a := by
  unfold generatedRootEightMoverPackedSpatialCondition
  decide +kernel

set_option maxHeartbeats 64000000 in
-- Check every original word prefix with all24 genuine physical coefficients.
private theorem row_01 : ∀ a : Fin 256,
    generatedRootEightMoverPackedSpatialCondition 1 a := by
  unfold generatedRootEightMoverPackedSpatialCondition
  decide +kernel

set_option maxHeartbeats 64000000 in
-- Check every original word prefix with all24 genuine physical coefficients.
private theorem row_02 : ∀ a : Fin 256,
    generatedRootEightMoverPackedSpatialCondition 2 a := by
  unfold generatedRootEightMoverPackedSpatialCondition
  decide +kernel

set_option maxHeartbeats 64000000 in
-- Check every original word prefix with all24 genuine physical coefficients.
private theorem row_03 : ∀ a : Fin 256,
    generatedRootEightMoverPackedSpatialCondition 3 a := by
  unfold generatedRootEightMoverPackedSpatialCondition
  decide +kernel

set_option maxHeartbeats 64000000 in
-- Check every original word prefix with all24 genuine physical coefficients.
private theorem row_04 : ∀ a : Fin 256,
    generatedRootEightMoverPackedSpatialCondition 4 a := by
  unfold generatedRootEightMoverPackedSpatialCondition
  decide +kernel

set_option maxHeartbeats 64000000 in
-- Check every original word prefix with all24 genuine physical coefficients.
private theorem row_05 : ∀ a : Fin 256,
    generatedRootEightMoverPackedSpatialCondition 5 a := by
  unfold generatedRootEightMoverPackedSpatialCondition
  decide +kernel

/-- Every prefix and signed spatial equation for six complete physical output rows is checked. -/
theorem generatedRootEight_mover_packed_spatial_block_00 (i : Fin 6) (a : Fin 256) :
    generatedRootEightMoverPackedSpatialCondition ⟨i.val + 0, by omega⟩ a := by
  fin_cases i
  · exact row_00 a
  · exact row_01 a
  · exact row_02 a
  · exact row_03 a
  · exact row_04 a
  · exact row_05 a

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
