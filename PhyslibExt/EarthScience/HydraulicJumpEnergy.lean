/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import PhyslibExt.EarthScience.HydraulicJump
public import PhyslibExt.EarthScience.OpenChannelSpecificEnergy
import Mathlib.Tactic

/-!
# Hydraulic-jump energy loss

## i. Overview

For a rectangular open channel, the specific energy at depth `h`
with discharge per unit width `q` and gravity `g` is
`h + q ^ 2 / (2 * g * h ^ 2)`. Between conjugate depths `h1`, `h2`
of a hydraulic jump (equal specific force, as in
`EarthScience.specific_force_conjugate_depths`), the energy loss
is `(h2 - h1) ^ 3 / (4 * h1 * h2)`, positive when `h2 > h1`.

## ii. Key results

- `EarthScience.rectangularSpecificEnergy` (in
  `OpenChannelSpecificEnergy`): specific energy per unit weight.
- `EarthScience.specific_energy_jump_loss`: the energy-loss
  identity between conjugate depths.
- `EarthScience.specific_energy_jump_loss_pos`: positivity of the
  loss for `h2 > h1`.

## iii. Table of contents

- A. Specific energy and jump loss

## iv. References

- V. T. Chow, *Open-Channel Hydraulics*, 1959 (specific energy
  and hydraulic-jump energy loss).
-/

@[expose] public section

namespace EarthScience

/-! ## A. Specific energy and jump loss -/

/-- Energy loss between conjugate depths of a hydraulic jump. -/
theorem specific_energy_jump_loss {q g h1 h2 : ℝ} (hg : 0 < g)
    (hh1 : 0 < h1) (hh2 : 0 < h2)
    (hM : rectangularSpecificForce q g h1
      = rectangularSpecificForce q g h2) :
    rectangularSpecificEnergy q g h1 - rectangularSpecificEnergy q g h2
      = (h2 - h1) ^ 3 / (4 * h1 * h2) := by
  by_cases hne : h1 = h2
  · subst hne
    simp
  · have hq := specific_force_conjugate_depths hg hh1 hh2 hne hM
    have h2g1 : (2 : ℝ) * g * h1 ^ 2 ≠ 0 := by positivity
    have h2g2 : (2 : ℝ) * g * h2 ^ 2 ≠ 0 := by positivity
    have h4h : (4 : ℝ) * h1 * h2 ≠ 0 := by positivity
    unfold rectangularSpecificEnergy
    rw [hq]
    field_simp
    ring

/-- The jump dissipates energy when the downstream depth is the
larger conjugate depth. -/
theorem specific_energy_jump_loss_pos {q g h1 h2 : ℝ} (hg : 0 < g)
    (hh1 : 0 < h1) (hh2 : 0 < h2) (h : h1 < h2)
    (hM : rectangularSpecificForce q g h1
      = rectangularSpecificForce q g h2) :
    0 < rectangularSpecificEnergy q g h1
      - rectangularSpecificEnergy q g h2 := by
  have hloss := specific_energy_jump_loss hg hh1 hh2 hM
  rw [hloss]
  have hsub : 0 < h2 - h1 := sub_pos.mpr h
  have hden : 0 < (4 : ℝ) * h1 * h2 := by positivity
  exact div_pos (pow_pos hsub 3) hden

end EarthScience
