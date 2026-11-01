/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationTenthAxisLowerRecoveryJointCompactFoundation

/-! Complete original full-Q source certificates. All finite proof bodies remain uncompiled. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open Multiplicative
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 100000

set_option maxHeartbeats 4000000 in
-- Scope the source-coordinate computation budget to this theorem.
/-- The complete base and central bit of original basis image9 match the source cache. -/
theorem generatedTenth_joint_q_certificates_image_09 :
    generatedTenthAxisLowerRecoveryJointCompactQImage 0 (qCoordinateGenerator 9) =
      generatedTenthAxisLowerRecoveryJointCompactFullQCache 0 9 := by
  apply NormalizedCocycleExtension.Extension.ext
  · apply toAdd.injective
    funext k
    have hb : ∀ k : Fin 24,
        toAdd (generatedTenthAxisLowerRecoveryJointCompactQImage 0 (qCoordinateGenerator 9)).base k
          =
          toAdd (generatedTenthAxisLowerRecoveryJointCompactFullQCache 0 9).base k := by
      decide +kernel
    exact hb k
  · apply toAdd.injective
    have hc : toAdd (generatedTenthAxisLowerRecoveryJointCompactQImage 0 (qCoordinateGenerator
      9)).coeff =
        toAdd (generatedTenthAxisLowerRecoveryJointCompactFullQCache 0 9).coeff := by
      decide +kernel
    exact hc

set_option maxHeartbeats 4000000 in
-- Scope the source-coordinate computation budget to this theorem.
/-- The actual genuine compact conjugation has this full original basis image. -/
theorem generatedTenth_joint_q_certificates_actual_09 :
    spinConjugation (generatedTenthAxisLowerRecoveryJointCompactSpin 0)
      (qCoordinateGenerator 9) = generatedTenthAxisLowerRecoveryJointCompactFullQCache 0 9 := by
  rw [generatedTenth_axis_lower_recovery_joint_compact_conjugation]
  exact generatedTenth_joint_q_certificates_image_09

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
