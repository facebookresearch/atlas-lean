/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationTenthAxisLowerRecoveryCompactSpatialPhysicalAll
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationTenthAxisLowerRecoveryLatticeBasisData05
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationTenthAxisLowerRecoveryLatticeBinaryBridge

/-! Ungated actual spatial binary proof drafts; no declaration has passed Lean. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster

/-- Physical source and complete existing lattice witnesses bind all actual binary columns. -/
theorem generatedTenth_compact_spatial_binary_05 :
    generatedTenthAxisLowerRecoveryCompactSpatialBinaryCondition 5 := by
  exact generatedTenth_axis_lower_recovery_spatial_binary_of_basis 5
    generatedTenthAxisLowerRecoveryLatticeBasisData05Matrix
    (generatedTenth_compact_spatial_physical_all 5)
    generatedTenth_axis_lower_recovery_lattice_basis_05
    generatedTenth_axis_lower_recovery_lattice_binary_05

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
