/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import PhyslibExt.Mechanics.SpaceTrajectoryModels
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum

/-!
# Space trajectory model checks

Concrete consumers of `PhyslibExt.Mechanics.SpaceTrajectoryModels`: the nonzero burn, with its
displacement `1 - log 2` and final speed `log 2`; the mid-burn thrust; and the depletion time
`t = 2`, outside the burn interval, where the velocity formula takes a junk value. For the
restricted three-body problem: both triangular points for the mass ratio `1/10`; the collision
boundary, where the effective potential takes a junk value; the particle at rest at a triangular
point, which meets every hypothesis of the rotating equations; and a point between the primaries
where the gradient of the effective potential does not vanish.

## i. Overview

These are elaboration and non-vacuity checks, not new results.

## ii. Key results

No new definitions or results are introduced here.

## iii. Table of contents

- A. The burn and the depletion boundary
- B. Restricted three-body equilibria

## iv. References

- `PhyslibExt.Mechanics.SpaceTrajectoryModels`
-/

@[expose] public section

namespace PhyslibExtTest.Mechanics.SpaceTrajectoryModels

open Set PhyslibExt.Mechanics.SpaceTrajectoryModels

/-! ## A. The burn and the depletion boundary -/

/-- Nonzero burn: the mass falls from `2` to `1`; the displacement `x 1 - x 0 = ∫₀¹ v` is
`1 - log 2` (about `0.307`) and the final speed is `log 2` (about `0.693`), both positive. -/
example :
    burnMass 1 < burnMass 0 ∧ burnPosition 1 - burnPosition 0 = 1 - Real.log 2 ∧
      ∫ t in (0 : ℝ)..1, burnVelocity t = 1 - Real.log 2 ∧ 0 < 1 - Real.log 2 ∧
      burnVelocity 1 = Real.log 2 ∧ 0 < Real.log 2 := by
  have hm10 : burnMass 1 < burnMass 0 := by unfold burnMass; norm_num
  have hx : burnPosition 1 - burnPosition 0 = 1 - Real.log 2 := by
    have hx0 := (burn_initial).1
    have hr := rendezvous.1
    have ht1 : targetPosition 1 = 1 - Real.log 2 := by unfold targetPosition; ring
    have hx1 : burnPosition 1 = 1 - Real.log 2 := hr.trans ht1
    rw [hx1, hx0, sub_zero]
  have hint_eq : ∫ t in (0 : ℝ)..1, burnVelocity t = 1 - Real.log 2 := by
    rw [←burnPosition_sub_eq_integral]
    exact hx
  have hlog2_lt : Real.log 2 < 1 := by
    have h := Real.log_lt_sub_one_of_pos (show (0 : ℝ) < 2 by norm_num)
      (show (2 : ℝ) ≠ 1 by norm_num)
    linarith
  have hpos1 : (0 : ℝ) < 1 - Real.log 2 := by linarith
  have hv1 : burnVelocity 1 = Real.log 2 := rendezvous.2.1
  have hlog2_pos : (0 : ℝ) < Real.log 2 := Real.log_pos (show (1 : ℝ) < 2 by norm_num)
  exact ⟨hm10, hx, hint_eq, hpos1, hv1, hlog2_pos⟩

/-- Fuel depletion: the mass vanishes at `t = 2`, which lies outside the burn interval `[0, 1]`.
There the velocity formula is outside the model: Lean's `2 / 0 = 0` and `log 0 = 0` give the junk
value `burnVelocity 2 = 0`, not a terminal speed. -/
example :
    burnMass 2 = 0 ∧ (2 : ℝ) ∉ Icc (0 : ℝ) 1 ∧ burnVelocity 2 = 0 := by
  have hm2 : burnMass 2 = 0 := by unfold burnMass; norm_num
  have hmem : (2 : ℝ) ∉ Icc (0 : ℝ) 1 := by
    intro h
    rw [mem_Icc] at h
    norm_num at h
  have hv2 : burnVelocity 2 = 0 := by
    unfold burnVelocity
    have h0 : (2 : ℝ) / ((2 : ℝ) - 2) = 0 := by
      have h22 : (2 : ℝ) - 2 = 0 := by norm_num
      rw [h22, div_zero]
    rw [h0, Real.log_zero]
  exact ⟨hm2, hmem, hv2⟩

/-- Mid-burn, `t = 1 / 2`: the mass is `3 / 2`, the velocity rate is `v' = 1 / (2 - t) = 2 / 3`,
and the law gives the thrust `m v' = 1`. -/
example :
    burnMass (1 / 2) = 3 / 2 ∧ HasDerivAt burnVelocity (2 / 3) (1 / 2) ∧
      burnMass (1 / 2) * (1 / (2 - 1 / 2)) = 1 := by
  have hv := hasDerivAt_burnVelocity (t := 1 / 2) (by norm_num)
  refine ⟨by norm_num [burnMass], ?_, (burn_law ⟨by norm_num, by norm_num⟩).2⟩
  convert hv using 1
  norm_num

/-! ## B. Restricted three-body equilibria -/

/-- A mass ratio strictly between zero and one, `μ = 1/10`: both triangular points `(2/5, ±√3/2)`
are equilibria. -/
example :
    (0 : ℝ) < 1 / 10 ∧ (1 / 10 : ℝ) < 1 ∧
      ∀ s : ℝ, s = 1 ∨ s = -1 →
        HasDerivAt (fun ξ => effectivePotential (1 / 10) ξ (s * (Real.sqrt 3 / 2))) 0 (2 / 5) ∧
          HasDerivAt (fun η => effectivePotential (1 / 10) (2 / 5) η) 0
            (s * (Real.sqrt 3 / 2)) := by
  refine ⟨by norm_num, by norm_num, fun s hs => ?_⟩
  obtain ⟨-, -, h1, h2⟩ := triangular_equilibrium (1 / 10) hs
  rw [show (2 / 5 : ℝ) = 1 / 2 - 1 / 10 by norm_num]
  exact ⟨h1, h2⟩

/-- Collisions are excluded explicitly: at the larger primary `r₁ = 0`, and the effective potential
returns the finite junk value `μ² / 2 + μ`, where the physical potential is unbounded. -/
example (μ : ℝ) :
    primaryDistOne μ (-μ) 0 = 0 ∧ effectivePotential μ (-μ) 0 = μ ^ 2 / 2 + μ := by
  have h1 : primaryDistOne μ (-μ) 0 = 0 := by
    simp [primaryDistOne]
  have h2 : primaryDistTwo μ (-μ) 0 = 1 := by
    unfold primaryDistTwo
    rw [show (-μ - (1 - μ)) ^ 2 + (0 : ℝ) ^ 2 = 1 by ring]
    exact Real.sqrt_one
  refine ⟨h1, ?_⟩
  unfold effectivePotential
  rw [h1, h2]
  ring

/-- The rotating equations apply to an actual motion: the particle at rest at the triangular
point `(1/2 - μ, √3/2)` of the rotating frame has constant, hence `C²`, coordinates, unit distances
to the primaries and an inertial motion that obeys Newton's law (`triangular_inertial_orbit`), so
`rotating_equations` applies, and both partial derivatives of `Ω` vanish there. -/
example (μ t : ℝ) :
    deriv (fun ξ => effectivePotential μ ξ (1 * (Real.sqrt 3 / 2))) (1 / 2 - μ) = 0 ∧
      deriv (fun η => effectivePotential μ (1 / 2 - μ) η) (1 * (Real.sqrt 3 / 2)) = 0 := by
  obtain ⟨hd1, hd2, -, -⟩ := triangular_equilibrium μ (s := 1) (Or.inl rfl)
  obtain ⟨h1, h2⟩ := rotating_equations (μ := μ) (t := t) (x := fun _ => 1 / 2 - μ)
    (y := fun _ => 1 * (Real.sqrt 3 / 2)) contDiff_const contDiff_const
    (by rw [hd1]; norm_num) (by rw [hd2]; norm_num) (triangular_inertial_orbit μ (Or.inl rfl) t)
  simp only [deriv_const', deriv_const, mul_zero, sub_zero, add_zero] at h1 h2
  exact ⟨h1.symm, h2.symm⟩

/-- Away from the triangular points the gradient need not vanish: with `μ = 1/10`, the point
`(2/5, 0)` between the primaries is at distance `1/2` from both, and
`Ω_x = 2/5 - (9/10)(1/2)/(1/8) - (1/10)(-1/2)/(1/8) = -14/5`. -/
example : HasDerivAt (fun ξ => effectivePotential (1 / 10) ξ 0) (-14 / 5) (2 / 5) := by
  have h1 : primaryDistOne (1 / 10) (2 / 5) 0 = 1 / 2 := by
    unfold primaryDistOne
    rw [show ((2 / 5 : ℝ) + 1 / 10) ^ 2 + 0 ^ 2 = (1 / 2) ^ 2 by norm_num,
      Real.sqrt_sq (by norm_num)]
  have h2 : primaryDistTwo (1 / 10) (2 / 5) 0 = 1 / 2 := by
    unfold primaryDistTwo
    rw [show ((2 / 5 : ℝ) - (1 - 1 / 10)) ^ 2 + 0 ^ 2 = (1 / 2) ^ 2 by norm_num,
      Real.sqrt_sq (by norm_num)]
  have h := hasDerivAt_effectivePotential_fst (μ := 1 / 10) (x := 2 / 5) (y := 0)
    (by rw [h1]; norm_num) (by rw [h2]; norm_num)
  rw [h1, h2] at h
  convert h using 1
  norm_num

end PhyslibExtTest.Mechanics.SpaceTrajectoryModels
