/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationTenthAxisLowerRecoveryCompactSpatialPhysicalAll
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationTenthAxisLowerRecoveryLatticeBasisData03
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationTenthAxisLowerRecoveryLatticeBinaryBridge

/-! Ungated actual spatial binary proof drafts; no declaration has passed Lean. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster

/-- Physical source and complete existing lattice witnesses bind all actual binary columns. -/
theorem generatedTenth_compact_spatial_binary_03 :
    generatedTenthAxisLowerRecoveryCompactSpatialBinaryCondition 3 := by
  exact generatedTenth_axis_lower_recovery_spatial_binary_of_basis 3
    generatedTenthAxisLowerRecoveryLatticeBasisData03Matrix
    (generatedTenth_compact_spatial_physical_all 3)
    generatedTenth_axis_lower_recovery_lattice_basis_03
    generatedTenth_axis_lower_recovery_lattice_binary_03

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
