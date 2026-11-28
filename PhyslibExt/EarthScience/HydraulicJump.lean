/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import Mathlib.Basic.Real.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Ring

/-!
# Rectangular hydraulic jump: conjugate depths

## i. Overview

For a rectangular prismatic channel with fixed discharge per unit width `q`
and gravity `g > 0`, the specific force (momentum function) per unit width
at depth `h > 0` is `M(h) = h ^ 2 / 2 + q ^ 2 / (g * h)`: the hydrostatic
pressure-force term plus the momentum-flux term, each per unit width and
specific weight. Across a hydraulic jump in such a channel, with hydrostatic
pressure away from the jump, equal bed elevation, and negligible friction
over the jump control volume, the two (conjugate) depths have equal
specific force; this module proves the resulting discharge relation.
Turbulence inside the jump and the associated energy loss are not modelled
here.

## ii. Key results

- `EarthScience.rectangularSpecificForce`: the specific force per unit
  width for a rectangular channel.
- `EarthScience.specific_force_conjugate_depths`: unequal positive depths
  with equal specific force satisfy `q ^ 2 = g * h1 * h2 * (h1 + h2) / 2`
  (the relation behind Bélanger's conjugate-depth ratio).

## iii. Table of contents

- A. Specific force and the conjugate-depth relation

## iv. References

- V. T. Chow, *Open-Channel Hydraulics*, McGraw-Hill, 1959, ch. 3
  (specific force) and ch. 15 (hydraulic jump).
-/

@[expose] public section

namespace EarthScience

/-! ## A. Specific force and the conjugate-depth relation -/

/-- Specific force (momentum function) per unit width for a rectangular
open channel: at depth `h`, with discharge per unit width `q` and gravity
`g`, it is `h ^ 2 / 2 + q ^ 2 / (g * h)`, the sum of the hydrostatic
pressure-force term and the momentum-flux term, each divided by the
specific weight and the channel width. It is physically meaningful for
`0 < g` and `0 < h`; outside that range the formula uses Lean's totalized
division and carries no physical meaning. With the convention `x / 0 = 0`,
it is `h ^ 2 / 2` when `g = 0` or `h = 0`. -/
noncomputable def rectangularSpecificForce (q g h : ℝ) : ℝ :=
  h ^ 2 / 2 + q ^ 2 / (g * h)

/-- **Conjugate depths of a hydraulic jump.** In a rectangular prismatic
channel (hydrostatic pressure away from the jump, equal bed elevation, no
friction over the jump control volume: the momentum closure assumed here),
two unequal positive depths `h1` and `h2` with the same specific force for
a fixed discharge per unit width `q` satisfy
`q ^ 2 = g * h1 * h2 * (h1 + h2) / 2`. Only `q ^ 2` enters, so no sign
hypothesis on `q` is needed. -/
theorem specific_force_conjugate_depths {q g h1 h2 : ℝ} (hg : 0 < g)
    (hh1 : 0 < h1) (hh2 : 0 < h2) (hne : h1 ≠ h2)
    (hM : rectangularSpecificForce q g h1
      = rectangularSpecificForce q g h2) :
    q ^ 2 = g * h1 * h2 * (h1 + h2) / 2 := by
  have hg' : g ≠ 0 := ne_of_gt hg
  have hh1' : h1 ≠ 0 := ne_of_gt hh1
  have hh2' : h2 ≠ 0 := ne_of_gt hh2
  have hgh1 : g * h1 ≠ 0 := mul_ne_zero hg' hh1'
  have hgh2 : g * h2 ≠ 0 := mul_ne_zero hg' hh2'
  have hgh12 : g * h1 * h2 ≠ 0 := mul_ne_zero (mul_ne_zero hg' hh1') hh2'
  have hsub : h1 - h2 ≠ 0 := sub_ne_zero.mpr hne
  unfold rectangularSpecificForce at hM
  have hdiff : h1 ^ 2 / 2 - h2 ^ 2 / 2
      = q ^ 2 / (g * h2) - q ^ 2 / (g * h1) := by
    linear_combination hM
  have hlhs : h1 ^ 2 / 2 - h2 ^ 2 / 2 = (h1 - h2) * ((h1 + h2) / 2) := by
    ring
  have hrhs : q ^ 2 / (g * h2) - q ^ 2 / (g * h1)
      = (h1 - h2) * (q ^ 2 / (g * h1 * h2)) := by
    field_simp
  rw [hlhs, hrhs] at hdiff
  have hcancel : (h1 + h2) / 2 = q ^ 2 / (g * h1 * h2) :=
    mul_left_cancel₀ hsub hdiff
  have hq : q ^ 2 = (h1 + h2) / 2 * (g * h1 * h2) := by
    rw [hcancel, div_mul_cancel₀ _ hgh12]
  rw [hq]
  ring

end EarthScience
