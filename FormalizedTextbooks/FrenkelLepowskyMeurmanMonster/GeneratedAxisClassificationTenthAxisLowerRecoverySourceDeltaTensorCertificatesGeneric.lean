/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationTenthAxisLowerRecoverySourceDeltaTensorInterface

/-! Canonical source-factor arithmetic retains all original signed coordinates. All proof bodies are
  uncompiled drafts. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 100000

/-- One original Fin256 block of the canonical source spin numerator equation. -/
def generatedTenthSourceDeltaTensorSpinBlock (j : Fin 7) (b : Fin 16)
    (u : Fin 256) : Prop :=
  (generatedTenthAxisLowerRecoverySourceDeltaTensorSpinDenominator j.succ : ℤ) *
      generatedTwelfthTensorSourceStageSpin 2 j
        (generatedTenthAxisLowerRecoverySourceDeltaTensorSpin j.castSucc)
        ⟨256 * b.val + u.val, by omega⟩ =
    (generatedTwelfthTensorSourceStageSpinDenominator 2 j
      (generatedTenthAxisLowerRecoverySourceDeltaTensorSpinDenominator j.castSucc) : ℤ) *
        generatedTenthAxisLowerRecoverySourceDeltaTensorSpin j.succ ⟨256 * b.val + u.val, by omega⟩

/-- The true canonical source scales are all nonzero. -/
theorem generatedTenth_source_delta_tensor_stage_denominator_ne_zero (j : Fin 7) :
    generatedTwelfthTensorSourceStageSpinDenominator 2 j
      (generatedTenthAxisLowerRecoverySourceDeltaTensorSpinDenominator j.castSucc) *
        generatedTwelfthTensorSourceStageSpatialDenominator 2 j
          (generatedTenthAxisLowerRecoverySourceDeltaTensorSpatialDenominator j.castSucc) ≠ 0 := by
  have h : ∀ j : Fin 7, generatedTwelfthTensorSourceStageSpinDenominator 2 j
      (generatedTenthAxisLowerRecoverySourceDeltaTensorSpinDenominator j.castSucc) *
        generatedTwelfthTensorSourceStageSpatialDenominator 2 j
          (generatedTenthAxisLowerRecoverySourceDeltaTensorSpatialDenominator j.castSucc) ≠ 0 := by
    decide +kernel
  exact h j

/-- Every normalized retained packet has its genuine nonzero denominator. -/
theorem generatedTenth_source_delta_tensor_packet_denominator_ne_zero (n : Fin 8) :
    generatedTenthAxisLowerRecoverySourceDeltaTensorSpinDenominator n *
      generatedTenthAxisLowerRecoverySourceDeltaTensorSpatialDenominator n ≠ 0 := by
  have h : ∀ n : Fin 8, generatedTenthAxisLowerRecoverySourceDeltaTensorSpinDenominator n *
      generatedTenthAxisLowerRecoverySourceDeltaTensorSpatialDenominator n ≠ 0 := by
    decide +kernel
  exact h n

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
