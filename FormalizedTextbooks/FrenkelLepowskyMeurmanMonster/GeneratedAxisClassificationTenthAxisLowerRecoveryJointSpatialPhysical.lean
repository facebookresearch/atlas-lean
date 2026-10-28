/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationTenthAxisLowerRecoveryJointCompactFoundation
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationTenthAxisLowerRecoveryCompactSpatialPhysical09
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationTenthAxisLowerRecoveryCompactSpatialPhysical01

/-! Prospective physical binding proof draft. No declaration has passed Lean. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster

open scoped Matrix

set_option maxRecDepth 100000 in
/-- Prospective full integer source product certificate, in literal order nine times one. -/
theorem generatedTenth_joint_spatial_physical_integer :
    generatedTenthAxisLowerRecoveryCompactSpatialNumerator 9 *
      generatedTenthAxisLowerRecoveryCompactSpatialNumerator 1 =
        generatedTenthAxisLowerRecoveryJointCompactSpatialNumerator 0 := by
  decide +kernel

/-- The actual literal spatial product has the entire retained joint physical numerator. -/
theorem generatedTenth_joint_spatial_physical_zero :
    generatedTenthAxisLowerRecoveryJointCompactPhysicalCondition 0 := by
  have h9 : (4 : ℝ) •
      leechIsomMatrix (generatedTenthAxisLowerRecoveryCompactSpatial 9) =
        (generatedTenthAxisLowerRecoveryCompactSpatialNumerator 9).map (Int.castRingHom ℝ) := by
    simpa [generatedTenthAxisLowerRecoveryCompactPhysicalCondition,
      generatedTenthAxisLowerRecoveryCompactSpatialDenominator] using
      generatedTenth_compact_spatial_physical_09
  have h1 : leechIsomMatrix (generatedTenthAxisLowerRecoveryCompactSpatial 1) =
      (generatedTenthAxisLowerRecoveryCompactSpatialNumerator 1).map (Int.castRingHom ℝ) := by
    simpa [generatedTenthAxisLowerRecoveryCompactPhysicalCondition,
      generatedTenthAxisLowerRecoveryCompactSpatialDenominator] using
      generatedTenth_compact_spatial_physical_01
  change (4 : ℝ) • leechIsomMatrix
    (generatedTenthAxisLowerRecoveryCompactSpatial 9 *
      generatedTenthAxisLowerRecoveryCompactSpatial 1) =
        (generatedTenthAxisLowerRecoveryJointCompactSpatialNumerator 0).map (Int.castRingHom ℝ)
  rw [generatedTenth_spatial_physical_matrix_mul, ← Matrix.smul_mul,
    h9, h1, ← Matrix.map_mul, generatedTenth_joint_spatial_physical_integer]

/-- Exhaustive actual binding for the one retained joint spatial constructor. -/
theorem generatedTenth_joint_spatial_physical_all (g : Fin 1) :
    generatedTenthAxisLowerRecoveryJointCompactPhysicalCondition g := by
  fin_cases g
  exact generatedTenth_joint_spatial_physical_zero

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
