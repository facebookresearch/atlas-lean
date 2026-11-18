/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import PhyslibExt.Mechanics.LinearPressurePanel

/-!
# Rankine active earth pressure on a unit-length wall

For dry horizontal backfill with supplied positive active
coefficient `K_a`, unit weight `γ`, and wall height `H`, the active
pressure at depth `z` is `K_a * γ * z`. Specializing the linear
pressure panel (`PhyslibExt.Mechanics.LinearPressurePanel`) to unit
width over `[0, H]`: the resultant force per unit wall length is
`K_a * γ * H ^ 2 / 2`, its first moment about the surface datum is
`K_a * γ * H ^ 3 / 3`, and the resultant acts at depth `2 * H / 3`,
that is, at height `H / 3` above the base.

## Main results

- `PhyslibExt.Mechanics.LinearPressurePanel.rankine_force`
- `PhyslibExt.Mechanics.LinearPressurePanel.rankine_moment`
- `PhyslibExt.Mechanics.LinearPressurePanel.rankine_resultant_height`
-/

@[expose] public section

namespace PhyslibExt.Mechanics.LinearPressurePanel

/-- Resultant Rankine force per unit wall length. -/
theorem rankine_force (Ka γ H : ℝ) :
    linearPressureForce (Ka * γ) 1 0 H = Ka * γ * H ^ 2 / 2 := by
  rw [linearPressureForce_eq]
  ring

/-- First moment of the Rankine pressure about the surface. -/
theorem rankine_moment (Ka γ H : ℝ) :
    linearPressureMoment (Ka * γ) 1 0 H = Ka * γ * H ^ 3 / 3 := by
  rw [linearPressureMoment_eq]
  ring

/-- The resultant acts at height `H / 3` above the base. -/
theorem rankine_resultant_height {Ka γ H : ℝ} (hKa : 0 < Ka)
    (hγ : 0 < γ) (hH : 0 < H) :
    H - linearPressureMoment (Ka * γ) 1 0 H
        / linearPressureForce (Ka * γ) 1 0 H = H / 3 := by
  rw [rankine_moment, rankine_force]
  have hKaγ : Ka * γ ≠ 0 := ne_of_gt (mul_pos hKa hγ)
  have hH' : H ≠ 0 := ne_of_gt hH
  have hH2 : H ^ 2 ≠ 0 := pow_ne_zero 2 hH'
  have hforce : Ka * γ * H ^ 2 / 2 ≠ 0 :=
    div_ne_zero (mul_ne_zero hKaγ hH2) (by norm_num)
  field_simp
  ring

end PhyslibExt.Mechanics.LinearPressurePanel
