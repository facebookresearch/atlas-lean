/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationTenthAxisLowerRecoveryJointCompactFoundation
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationTenthAxisLowerRecoveryCompactSpatialBinary09
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationTenthAxisLowerRecoveryCompactSpatialBinary01
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTransitionsQFastMasks

/-! Ungated actual spatial binary proof drafts; no declaration has passed Lean. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster

set_option backward.isDefEq.respectTransparency false

/-- Actual source nine acts on every standard binary basis vector by its retained columns. -/
theorem generatedTenth_joint_spatial_binary_nine_basis (j : Fin 24) :
    leechBinaryAction (generatedTenthAxisLowerRecoveryCompactSpatial 9) (Pi.single j 1) =
      monsterCo1GeometryBinaryMaskDecode
        (generatedTenthAxisLowerRecoveryCompactBinaryColumns 9 j) := by
  simpa only [generatedTwelfth_spin_compact_binary_basis] using
    generatedTenth_compact_spatial_binary_09 j

/-- Prospective complete finite columns for the literal source product nine times one. -/
theorem generatedTenth_joint_spatial_binary_columns : ∀ j : Fin 24,
    generatedAxisGlobalQMaskVector (generatedTenthAxisLowerRecoveryCompactBinaryColumns 9)
      (generatedTenthAxisLowerRecoveryCompactBinaryColumns 1 j) =
        generatedTenthAxisLowerRecoveryJointCompactBinaryColumns 0 j := by
  decide +kernel

/-- The genuine joint product preserves literal multiplication order and every binary column. -/
theorem generatedTenth_joint_spatial_binary_zero :
    generatedTenthAxisLowerRecoveryJointCompactSpatialBinaryCondition 0 := by
  intro j
  change leechBinaryAction
    (generatedTenthAxisLowerRecoveryCompactSpatial 9 *
      generatedTenthAxisLowerRecoveryCompactSpatial 1)
      (monsterCo1GeometryBinaryMaskDecode (n := 24) (2 ^ j.val)) = _
  rw [map_mul]
  change leechBinaryAction (generatedTenthAxisLowerRecoveryCompactSpatial 9)
    (leechBinaryAction (generatedTenthAxisLowerRecoveryCompactSpatial 1)
      (monsterCo1GeometryBinaryMaskDecode (n := 24) (2 ^ j.val))) = _
  rw [generatedTenth_compact_spatial_binary_01 j]
  have hm := generatedAxisGlobalQMaskVector_actual
    (leechBinaryAction (generatedTenthAxisLowerRecoveryCompactSpatial 9))
    (generatedTenthAxisLowerRecoveryCompactBinaryColumns 9)
    generatedTenth_joint_spatial_binary_nine_basis
    (generatedTenthAxisLowerRecoveryCompactBinaryColumns 1 j)
  rw [← hm, generatedTenth_joint_spatial_binary_columns j]

/-- Exhaustive actual binary binding for the one retained joint spatial constructor. -/
theorem generatedTenth_joint_spatial_binary_all (g : Fin 1) :
    generatedTenthAxisLowerRecoveryJointCompactSpatialBinaryCondition g := by
  fin_cases g
  exact generatedTenth_joint_spatial_binary_zero

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
