/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationTenthAxisLowerRecoveryCompactFoundation

/-! Complete original full-Q source certificates. All finite proof bodies remain uncompiled. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open Multiplicative
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 100000

set_option maxHeartbeats 4000000 in
-- Scope the source-coordinate computation budget to this theorem.
/-- The complete base and central bit of original basis image3 match the source cache. -/
theorem generatedTenth_compact10_q_certificates_image_03 :
    generatedTenthAxisLowerRecoveryCompactQImage 10 (qCoordinateGenerator 3) =
      generatedTenthAxisLowerRecoveryCompactFullQCache 10 3 := by
  apply NormalizedCocycleExtension.Extension.ext
  · apply toAdd.injective
    funext k
    have hb : ∀ k : Fin 24,
        toAdd (generatedTenthAxisLowerRecoveryCompactQImage 10 (qCoordinateGenerator 3)).base k =
          toAdd (generatedTenthAxisLowerRecoveryCompactFullQCache 10 3).base k := by
      decide +kernel
    exact hb k
  · apply toAdd.injective
    have hc : toAdd (generatedTenthAxisLowerRecoveryCompactQImage 10 (qCoordinateGenerator 3)).coeff
      =
        toAdd (generatedTenthAxisLowerRecoveryCompactFullQCache 10 3).coeff := by
      decide +kernel
    exact hc

set_option maxHeartbeats 4000000 in
-- Scope the source-coordinate computation budget to this theorem.
/-- The actual genuine compact conjugation has this full original basis image. -/
theorem generatedTenth_compact10_q_certificates_actual_03 :
    spinConjugation (generatedTenthAxisLowerRecoveryCompactSpin 10)
      (qCoordinateGenerator 3) = generatedTenthAxisLowerRecoveryCompactFullQCache 10 3 := by
  rw [generatedTenth_axis_lower_recovery_compact_conjugation]
  exact generatedTenth_compact10_q_certificates_image_03

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
