/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationTenthAxisLowerRecoveryTwoFixerTensorCircuitData
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationTenthAxisLowerRecoveryCompactSpatialPhysicalAll
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationTenthAxisLowerRecoveryJointSpatialPhysical

/-! Ungated reuse of the complete actual physical matrix certificates for both tensor fixers. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
set_option backward.isDefEq.respectTransparency false

/-- Both actual fibers retain exactly the certified spatial representative and denominator. -/
theorem generatedTenth_two_fixer_tensor_physical_actual :
    GeneratedTenthTwoFixerTensorPhysicalCondition := by
  intro g
  fin_cases g
  · change generatedTenthAxisLowerRecoveryJointCompactPhysicalCondition 0
    exact generatedTenth_joint_spatial_physical_zero
  · change generatedTenthAxisLowerRecoveryCompactPhysicalCondition 10
    exact generatedTenth_compact_spatial_physical_all 10

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
