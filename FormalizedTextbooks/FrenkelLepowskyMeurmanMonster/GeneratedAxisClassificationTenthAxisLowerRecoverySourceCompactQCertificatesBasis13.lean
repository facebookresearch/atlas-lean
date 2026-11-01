/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationTenthAxisLowerRecoverySourceCompactFoundation
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTransitionsFifthQCache02

/-! Complete original full-Q source certificates. All finite proof bodies remain uncompiled. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open Multiplicative
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 100000

set_option maxHeartbeats 4000000 in
-- Scope the source-coordinate computation budget to this theorem.
/-- The complete base and central bit of original basis image13 match the source cache. -/
theorem generatedTenth_source_q_certificates_image_13 :
    generatedTenthAxisLowerRecoverySourceCompactQImage 0 (qCoordinateGenerator 13) =
      generatedAxisGlobalFifthQCache 2 13 := by
  apply NormalizedCocycleExtension.Extension.ext
  · apply toAdd.injective
    funext k
    have hb : ∀ k : Fin 24,
        toAdd (generatedTenthAxisLowerRecoverySourceCompactQImage 0 (qCoordinateGenerator 13)).base
          k =
          toAdd (generatedAxisGlobalFifthQCache 2 13).base k := by
      decide +kernel
    exact hb k
  · apply toAdd.injective
    have hc : toAdd (generatedTenthAxisLowerRecoverySourceCompactQImage 0 (qCoordinateGenerator
      13)).coeff =
        toAdd (generatedAxisGlobalFifthQCache 2 13).coeff := by
      decide +kernel
    exact hc

set_option maxHeartbeats 4000000 in
-- Scope the source-coordinate computation budget to this theorem.
/-- The actual genuine compact conjugation has this full original basis image. -/
theorem generatedTenth_source_q_certificates_actual_13 :
    spinConjugation (generatedTenthAxisLowerRecoverySourceCompactSpin 0)
      (qCoordinateGenerator 13) = generatedAxisGlobalFifthQCache 2 13 := by
  rw [generatedTenth_axis_lower_recovery_source_compact_conjugation]
  exact generatedTenth_source_q_certificates_image_13

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
