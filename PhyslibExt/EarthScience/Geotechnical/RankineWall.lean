/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import PhyslibExt.Mechanics.LinearPressurePanel
import Mathlib.Tactic.FieldSimp

/-!
# Rankine active earth pressure on a unit-length wall

## i. Overview

For dry, cohesionless, homogeneous, horizontal and unsurcharged
backfill against a smooth vertical wall at the active limit
state, with supplied positive active coefficient `K_a`, unit
weight `γ`, and wall height `H`, the Rankine active pressure at
depth `z` is `K_a * γ * z`. (Cohesion, surcharge, wall friction
or inclination, and non-active failure states all change the
pressure law; the result below is conditional on the supplied
linear law.) Reading that law through the linear pressure panel
(`PhyslibExt.Mechanics.LinearPressurePanel`) at unit width over
`[0, H]`, whose resultant force and first moment are
`K_a * γ * H ^ 2 / 2` and `K_a * γ * H ^ 3 / 3` by the generic
panel equations, the resultant acts at depth `2 * H / 3`, that
is, at height `H / 3` above the base.

## ii. Key results

- `EarthScience.rankineActivePressure`: the Rankine active
  pressure law at a depth.
- `EarthScience.rankine_resultant_height`: resultant height
  `H / 3` above the base, from the generic panel force and
  moment equations.

## iii. Table of contents

- A. Rankine resultant height

## iv. References

- R. F. Craig, *Craig's Soil Mechanics*, 8th edition, 2012
  (Rankine active earth pressure and its resultant).
-/

@[expose] public section

namespace EarthScience

/-! ## A. Rankine resultant height -/

/-- Rankine active earth pressure at depth `z` for supplied
active coefficient `Ka` and unit weight `γ`: `Ka * γ * z`, the
linear pressure law conditional on the hypotheses in the module
overview. -/
noncomputable def rankineActivePressure (Ka γ z : ℝ) : ℝ :=
  Ka * γ * z

/-- The Rankine resultant acts at height `H / 3` above the base:
with the unit-width panel force and moment for the linear law
`rankineActivePressure` (pressure gradient `Ka * γ`), the
resultant depth `moment / force` is `2 * H / 3`. -/
theorem rankine_resultant_height {Ka γ H : ℝ} (hKa : 0 < Ka)
    (hγ : 0 < γ) (hH : 0 < H) :
    H - PhyslibExt.Mechanics.LinearPressurePanel.linearPressureMoment
          (Ka * γ) 1 0 H
        / PhyslibExt.Mechanics.LinearPressurePanel.linearPressureForce
          (Ka * γ) 1 0 H = H / 3 := by
  rw [PhyslibExt.Mechanics.LinearPressurePanel.linearPressureMoment_eq,
    PhyslibExt.Mechanics.LinearPressurePanel.linearPressureForce_eq]
  have hKaγ : Ka * γ ≠ 0 := ne_of_gt (mul_pos hKa hγ)
  have hH' : H ≠ 0 := ne_of_gt hH
  field_simp
  ring

end EarthScience
