/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

import PhyslibExt.Mechanics.ImpactAndDeployment
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

/-!
# Impact event checks

Concrete consumers of `PhyslibExt.Mechanics.ImpactAndDeployment`: two bodies of masses `1` and
`3` with incoming velocities `2` and `0`, at the restitution coefficients `1 / 2`, `1` and `2`; a
body of mass `2` meeting a fixed wall at `v⁻ = -3` with `e = 1 / 2`; a ball bouncing on a floor
with take-off speed `5`, `g = 10` and `e = 1 / 2`, whose flights last `(1 / 2) ^ n` and accumulate
at `t = 2`, together with the elastic (`e = 1`) and inelastic (`e = 0`) boundaries; and the event,
flight and bouncing-ball lemmas applied to those states.

## i. Overview

These are elaboration and non-vacuity checks, not new results.

## ii. Key results

No new definitions or results are introduced here.

## iii. Table of contents

- A. Two-body fixtures
- B. Two-body lemmas on the fixture state
- C. Fixed-wall fixture
- D. Fixed-wall lemmas on the fixture state
- E. Bouncing-ball fixture
- F. Bouncing-ball lemmas on the fixture state

## iv. References

None.
-/

namespace PhyslibExtTest.Mechanics.ImpactAndDeployment

open PhyslibExt.Mechanics.PowerPorts
open PhyslibExt.Mechanics.ImpactAndDeployment
open Robotics.Hybrid

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

/-! ## E. Bouncing-ball fixture -/

/-- Fixture: `u₀ = 5`, `g = 10`, `e = 1 / 2`. The first arc (mass `2`) returns after `1` with
velocity `-5` and rebounds at `5 / 2`; the flight durations are `(1 / 2) ^ n`, the third contact
is at `7 / 4`, and the durations sum to `t_∞ = 2`. -/
example :
    constForceVelocity 2 (5 : ℝ) (-(2 * 10)) (flightDuration 10 (1 / 2) 5 0) = -5 ∧
      wallReboundVelocity (1 / 2) (-5) = 5 / 2 ∧ bounceSpeed (1 / 2) 5 2 = 5 / 4 ∧
      (∀ n, flightDuration 10 (1 / 2) 5 n = (1 / 2) ^ n) ∧
      dwellElapsed (flightDuration 10 (1 / 2) 5) 3 = 7 / 4 ∧
      zenoTime 10 (1 / 2) 5 = 2 ∧ HasSum (flightDuration 10 (1 / 2) 5) 2 := by
  have hT0 : flightDuration 10 (1 / 2) 5 0 = 1 := by
    norm_num [flightDuration, bounceSpeed]
  have hdur : ∀ n, flightDuration 10 (1 / 2) 5 n = (1 / 2) ^ n := by
    intro n
    rw [flightDuration_eq]
    norm_num
  have hzeno : zenoTime 10 (1 / 2) 5 = 2 := by
    norm_num [zenoTime]
  refine ⟨?_, ?_, ?_, hdur, ?_, hzeno, ?_⟩
  · rw [hT0]
    norm_num [constForceVelocity, smul_eq_mul]
  · norm_num [wallReboundVelocity]
  · norm_num [bounceSpeed, wallReboundVelocity]
  · simp only [dwellElapsed, Finset.sum_range_succ, Finset.sum_range_zero, hdur]
    norm_num
  · have h := hasSum_flightDuration (g := 10) (e := 1 / 2) (u₀ := 5)
      (by norm_num) (by norm_num)
    rwa [hzeno] at h

/-! ## F. Bouncing-ball lemmas on the fixture state -/

/-- The fixture's first arc is above the floor at mid-flight `t = 1 / 2` and back on it at `t = 1`,
and the second take-off speed is `5 / 2`. -/
example :
    0 < constForcePosition 2 0 (5 : ℝ) (-(2 * 10)) (1 / 2) ∧
      constForcePosition 2 0 (5 : ℝ) (-(2 * 10)) 1 = 0 ∧ bounceSpeed (1 / 2) 5 1 = 5 / 2 := by
  obtain ⟨-, hland, habove, -, -⟩ := bounce_arc (m := 2) (g := 10) (by norm_num) (by norm_num)
    (isActiveArc_of_pos (e := 1 / 2) (u₀ := 5) (by norm_num) (by norm_num) 0)
  have hT : flightDuration 10 (1 / 2) 5 0 = 1 := by norm_num [flightDuration, bounceSpeed]
  have hu : bounceSpeed (1 / 2) 5 0 = 5 := by simp [bounceSpeed]
  rw [hT, hu] at hland habove
  refine ⟨habove (1 / 2) ⟨by norm_num, by norm_num⟩, hland, ?_⟩
  rw [bounceSpeed_eq]
  norm_num

/-- Zeno accumulation of the fixture: its contact times stay below `t_∞ = 2` and tend to it. -/
example :
    (∀ N, dwellElapsed (flightDuration 10 (1 / 2) 5) N < 2) ∧
      Filter.Tendsto (dwellElapsed (flightDuration 10 (1 / 2) 5)) Filter.atTop (nhds 2) := by
  obtain ⟨-, hlt, htend, -⟩ := zeno_accumulation (g := 10) (e := 1 / 2) (u₀ := 5)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have hz : zenoTime 10 (1 / 2) 5 = 2 := by norm_num [zenoTime]
  rw [hz] at hlt htend
  exact ⟨hlt, htend⟩

/-- The fixture's flight durations are summable, since `e = 1 / 2 < 1`, and no positive dwell
time bounds them from below. -/
example :
    Summable (flightDuration 10 (1 / 2) 5) ∧ ¬ ∃ δ > 0, ∀ k, δ ≤ flightDuration 10 (1 / 2) 5 k :=
  ⟨(summable_flightDuration_iff (by norm_num) (by norm_num) (by norm_num)).2 (by norm_num),
    zeno_no_dwell (by norm_num) (by norm_num) (by norm_num) (by norm_num)⟩

/-- The elastic boundary `e = 1`: the fixture's flights all last `1`, the durations are not
summable, and only finitely many impacts occur before `t = 10`. -/
example :
    ¬ Summable (flightDuration 10 1 5) ∧
      {n : ℕ | dwellElapsed (flightDuration 10 1 5) n ≤ 10}.Finite := by
  obtain ⟨hns, hfin⟩ := elastic_events_finite (g := 10) (u₀ := 5) (by norm_num) (by norm_num)
  exact ⟨hns, hfin 10⟩

/-- The finite-event criterion with the dwell time `1` of the elastic flights: at most `10`
impacts occur before `t = 10`. -/
example (n : ℕ) (hn : dwellElapsed (flightDuration 10 1 5) n ≤ 10) : n ≤ 10 := by
  have h := (Robotics.Hybrid.events_finite_of_dwell (δ := 1) (by norm_num)
    (fun k => by rw [flightDuration_eq]; norm_num) 10).2 n hn
  exact_mod_cast (by linarith : (n : ℝ) ≤ 10)

/-- The inelastic boundary `e = 0`: the fixture's ball has one active arc, the first, which ends
at `t = 1`; it then rests on the floor, every later flight lasting `0` and the elapsed time staying
at `1`. -/
example :
    {n : ℕ | IsActiveArc 0 5 n} = {0} ∧ dwellElapsed (flightDuration 10 0 5) 1 = 1 ∧
      ∀ n, flightDuration 10 0 5 (n + 1) = 0 ∧
        dwellElapsed (flightDuration 10 0 5) (n + 1) = 1 := by
  obtain ⟨hact, -, hrest⟩ := inelastic_stops (g := 10) (u₀ := 5) (by norm_num) (by norm_num)
  have h1 : ∀ n, dwellElapsed (flightDuration 10 0 5) (n + 1) = 1 := fun n => by
    rw [(hrest n).2.2]
    norm_num
  exact ⟨hact, h1 0, fun n => ⟨(hrest n).2.1, h1 n⟩⟩

/-- In contrast, with `e = 1 / 2` every arc of the fixture is active: the bounces never stop. -/
example (n : ℕ) : IsActiveArc (1 / 2) 5 n :=
  isActiveArc_of_pos (by norm_num) (by norm_num) n

/-- The first inelastic arc is a ballistic flight: with `e = 0` the fixture's ball has one active
arc, the first; it lasts `1`, is above the floor at `t = 1 / 2`, lands at `t = 1` with velocity
`-5`, and the wall event with `e = 0` leaves the take-off speed `0`. -/
example :
    0 < flightDuration 10 0 5 0 ∧ 0 < constForcePosition 2 0 (5 : ℝ) (-(2 * 10)) (1 / 2) ∧
      constForcePosition 2 0 (5 : ℝ) (-(2 * 10)) 1 = 0 ∧
      constForceVelocity 2 (5 : ℝ) (-(2 * 10)) 1 = -5 ∧ bounceSpeed 0 5 1 = 0 := by
  have hact : IsActiveArc 0 5 0 := by
    have hone := (inelastic_stops (g := 10) (u₀ := 5) (by norm_num) (by norm_num)).1
    have h0 : (0 : ℕ) ∈ {n : ℕ | IsActiveArc 0 5 n} := by
      rw [hone]
      exact Set.mem_singleton 0
    exact h0
  obtain ⟨hpos, hland, habove, hvel, hreb⟩ :=
    bounce_arc (m := 2) (g := 10) (by norm_num) (by norm_num) hact
  have hT : flightDuration 10 0 5 0 = 1 := by norm_num [flightDuration, bounceSpeed]
  have hu : bounceSpeed 0 5 0 = 5 := by simp [bounceSpeed]
  rw [hT, hu] at hland habove hvel hreb
  rw [hvel] at hreb
  refine ⟨hpos, habove (1 / 2) ⟨by norm_num, by norm_num⟩, hland, hvel, ?_⟩
  rw [← hreb]
  norm_num [wallReboundVelocity]

end PhyslibExtTest.Mechanics.ImpactAndDeployment
