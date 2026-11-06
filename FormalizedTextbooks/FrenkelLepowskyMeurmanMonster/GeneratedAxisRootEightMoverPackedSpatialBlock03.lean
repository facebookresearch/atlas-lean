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
private theorem row_18 : ∀ a : Fin 256,
    generatedRootEightMoverPackedSpatialCondition 18 a := by
  unfold generatedRootEightMoverPackedSpatialCondition
  decide +kernel

set_option maxHeartbeats 64000000 in
-- Check every original word prefix with all24 genuine physical coefficients.
private theorem row_19 : ∀ a : Fin 256,
    generatedRootEightMoverPackedSpatialCondition 19 a := by
  unfold generatedRootEightMoverPackedSpatialCondition
  decide +kernel

set_option maxHeartbeats 64000000 in
-- Check every original word prefix with all24 genuine physical coefficients.
private theorem row_20 : ∀ a : Fin 256,
    generatedRootEightMoverPackedSpatialCondition 20 a := by
  unfold generatedRootEightMoverPackedSpatialCondition
  decide +kernel

set_option maxHeartbeats 64000000 in
-- Check every original word prefix with all24 genuine physical coefficients.
private theorem row_21 : ∀ a : Fin 256,
    generatedRootEightMoverPackedSpatialCondition 21 a := by
  unfold generatedRootEightMoverPackedSpatialCondition
  decide +kernel

set_option maxHeartbeats 64000000 in
-- Check every original word prefix with all24 genuine physical coefficients.
private theorem row_22 : ∀ a : Fin 256,
    generatedRootEightMoverPackedSpatialCondition 22 a := by
  unfold generatedRootEightMoverPackedSpatialCondition
  decide +kernel

set_option maxHeartbeats 64000000 in
-- Check every original word prefix with all24 genuine physical coefficients.
private theorem row_23 : ∀ a : Fin 256,
    generatedRootEightMoverPackedSpatialCondition 23 a := by
  unfold generatedRootEightMoverPackedSpatialCondition
  decide +kernel

/-- Every prefix and signed spatial equation for six complete physical output rows is checked. -/
theorem generatedRootEight_mover_packed_spatial_block_03 (i : Fin 6) (a : Fin 256) :
    generatedRootEightMoverPackedSpatialCondition ⟨i.val + 18, by omega⟩ a := by
  fin_cases i
  · exact row_18 a
  · exact row_19 a
  · exact row_20 a
  · exact row_21 a
  · exact row_22 a
  · exact row_23 a

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
