/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

import PhyslibExt.Mechanics.ImpactAndDeployment
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

/-!
# Impact event checks

Concrete consumers of `PhyslibExt.Mechanics.ImpactAndDeployment`: two bodies of masses `1` and
`3` with incoming velocities `2` and `0`, at the restitution coefficients `1 / 2`, `1` and `2`; a
body of mass `2` meeting a fixed wall at `v⁻ = -3` with `e = 1 / 2`; and the event and flight
lemmas applied to those states.

## i. Overview

These are elaboration and non-vacuity checks, not new results.

## ii. Key results

No new definitions or results are introduced here.

## iii. Table of contents

- A. Two-body fixtures
- B. Two-body lemmas on the fixture state
- C. Fixed-wall fixture
- D. Fixed-wall lemmas on the fixture state

## iv. References

None.
-/

namespace PhyslibExtTest.Mechanics.ImpactAndDeployment

open PhyslibExt.Mechanics.PowerPorts
open PhyslibExt.Mechanics.ImpactAndDeployment

/-! ## A. Two-body fixtures -/

/-- Unequal masses and a nonzero relative incoming velocity: `m₁ = 1`, `m₂ = 3`, `v₁ = 2`,
`v₂ = 0`, `e = 1 / 2`. After the event `u₁ = -1 / 4` and `u₂ = 3 / 4`; the momentum `2` is kept
and the kinetic energy drops from `2` to `7 / 8`, a loss of `9 / 8`. -/
example :
    impactVelocity₁ 1 3 (1 / 2) 2 0 = -1 / 4 ∧ impactVelocity₂ 1 3 (1 / 2) 2 0 = 3 / 4 ∧
      pairKineticEnergy 1 3 2 0 = 2 ∧ pairKineticEnergy 1 3 (-1 / 4) (3 / 4) = 7 / 8 := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;>
    simp only [impactVelocity₁, impactVelocity₂, pairKineticEnergy] <;> norm_num

/-- The restitution boundary on the same incoming state: `e = 1` gives `u = (-1, 1)` and keeps
the kinetic energy `2`, while `e = 2` would give `u = (-5 / 2, 3 / 2)` and raise it to `13 / 2`. -/
example :
    impactVelocity₁ 1 3 1 2 0 = -1 ∧ impactVelocity₂ 1 3 1 2 0 = 1 ∧
      pairKineticEnergy 1 3 (-1) 1 = 2 ∧
      impactVelocity₁ 1 3 2 2 0 = -5 / 2 ∧ impactVelocity₂ 1 3 2 2 0 = 3 / 2 ∧
      pairKineticEnergy 1 3 (-5 / 2) (3 / 2) = 13 / 2 := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
    simp only [impactVelocity₁, impactVelocity₂, pairKineticEnergy] <;> norm_num

/-! ## B. Two-body lemmas on the fixture state -/

/-- The event loss on the fixture is `9 / 8`, from the general loss formula. -/
example :
    pairKineticEnergy 1 3 2 0 -
        pairKineticEnergy 1 3 (impactVelocity₁ 1 3 (1 / 2) 2 0) (impactVelocity₂ 1 3 (1 / 2) 2 0) =
      9 / 8 := by
  rw [impact_energy_loss (by norm_num) (by norm_num)]
  norm_num

/-- The fixture's event impulses are `-9 / 4` on body 1 and `9 / 4` on body 2. -/
example :
    1 * impactVelocity₁ 1 3 (1 / 2) 2 0 - 1 * 2 = -9 / 4 ∧
      3 * impactVelocity₂ 1 3 (1 / 2) 2 0 - 3 * 0 = 9 / 4 := by
  obtain ⟨h₁, h₂⟩ := impact_impulse (m₁ := 1) (m₂ := 3) (by norm_num) (by norm_num) (1 / 2) 2 0
  rw [h₁, h₂]
  norm_num

/-- With equal and opposite forces `1` and `-1` after the event, the total momentum stays at the
pre-impact value `2` at every later time. -/
example (t : ℝ) :
    1 * constForceVelocity 1 (impactVelocity₁ 1 3 (1 / 2) 2 0) 1 t +
        3 * constForceVelocity 3 (impactVelocity₂ 1 3 (1 / 2) 2 0) (-1) t = 2 := by
  rw [impact_then_flight_momentum (by norm_num) (by norm_num)]
  ring

/-- The coefficient `e = 2` would raise the kinetic energy of the fixture state. -/
example :
    pairKineticEnergy 1 3 2 0 <
      pairKineticEnergy 1 3 (impactVelocity₁ 1 3 2 2 0) (impactVelocity₂ 1 3 2 2 0) :=
  impact_energy_lt_of_one_lt (by norm_num) (by norm_num) (by norm_num) (by norm_num)


/-! ## C. Fixed-wall fixture -/

/-- `m = 2`, `v⁻ = -3`, `e = 1 / 2`: `v⁺ = 3 / 2` and the wall impulse is `9`. The momentum is `-6`
before and `3` after, so treating the body alone as momentum-conserving is false. The kinetic
energy drops from `9` to `9 / 4`, a loss of `27 / 4`; with `e = 0` the body stops. -/
example :
    wallReboundVelocity (1 / 2) (-3) = 3 / 2 ∧ wallImpulse 2 (1 / 2) (-3) = 9 ∧
      2 * wallReboundVelocity (1 / 2) (-3) ≠ 2 * (-3) ∧ bodyKineticEnergy 2 (-3) = 9 ∧
      bodyKineticEnergy 2 (wallReboundVelocity (1 / 2) (-3)) = 9 / 4 ∧
      bodyKineticEnergy 2 (wallReboundVelocity 0 (-3)) = 0 := by
  unfold wallImpulse bodyKineticEnergy wallReboundVelocity
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;> norm_num

/-! ## D. Fixed-wall lemmas on the fixture state -/

/-- The wall impulse on the fixture body points out of the wall. -/
example : 0 < wallImpulse 2 (1 / 2) (-3) :=
  wallImpulse_pos (by norm_num) (by norm_num) (by norm_num)

/-- The fixture body alone does not conserve momentum. -/
example : 2 * wallReboundVelocity (1 / 2) (-3) ≠ 2 * (-3) :=
  body_momentum_ne (by norm_num) (by norm_num) (by norm_num)

/-- With `e = 1 / 2 < 1` the fixture body loses kinetic energy. -/
example : bodyKineticEnergy 2 (wallReboundVelocity (1 / 2) (-3)) < bodyKineticEnergy 2 (-3) :=
  (wall_energy_cases (by norm_num) (by norm_num) (by norm_num)).1.2 (by norm_num)

/-- After the rebound the fixture body flies under its weight `-20` (`g = 10`): its momentum at
time `t` is `-6 + 9 - 20 t`. -/
example (t : ℝ) : 2 * constForceVelocity 2 (wallReboundVelocity (1 / 2) (-3)) (-20) t = 3 - 20 * t := by
  rw [rebound_then_flight_momentum (by norm_num), wallImpulse_eq]
  ring

end PhyslibExtTest.Mechanics.ImpactAndDeployment
