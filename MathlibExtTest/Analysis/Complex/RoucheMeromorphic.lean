/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Analysis.Complex.Rouche

open Set Metric MeromorphicOn
open MathlibExt.Analysis.RoucheWanted.ComplexAnalysis (rouche_zero_count_eq)

noncomputable section

private def reciprocal : ℂ → ℂ := fun z => z⁻¹
private def perturbation : ℂ → ℂ := fun _ => 1 / 2

/-- The meromorphic example has a genuine pole in the disc. -/
example : meromorphicOrderAt reciprocal (0 : ℂ) = (-1 : WithTop ℤ) := by
  change meromorphicOrderAt ((id : ℂ → ℂ)⁻¹) 0 = _
  rw [meromorphicOrderAt_inv, meromorphicOrderAt_id]

/-- Adding the constant `1/2` preserves the zero count of `1/z` on the unit disc. -/
example :
    (∑ᶠ z, ((divisor (reciprocal + perturbation) (closedBall 0 1))⁺) z) =
      (∑ᶠ z, ((divisor reciprocal (closedBall 0 1))⁺) z) := by
  apply rouche_zero_count_eq zero_lt_one
  · intro z _
    exact meromorphicNFAt_inv.mpr analyticAt_id.meromorphicNFAt
  · exact analyticOn_const
  · intro z hz
    change ‖(1 : ℂ) / 2‖ < ‖z⁻¹‖
    rw [norm_inv, hz, inv_one, norm_div, norm_one]
    norm_num
