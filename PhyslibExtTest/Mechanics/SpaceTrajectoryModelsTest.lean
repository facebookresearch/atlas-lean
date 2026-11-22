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
where the gradient of the effective potential does not vanish. For the Jacobi integral: for equal
masses, the Jacobi constant `3` of the barycenter state with velocity `(1, 0)`, which forbids the
triangular point `(0, √3/2)`, where `2 Ω = 11/4`, to every unforced trajectory through that
state; a thrusting path that reaches that point; and the particle at rest at a triangular point,
whose Jacobi function is constant.

## i. Overview

These are elaboration and non-vacuity checks, not new results.

## ii. Key results

No new definitions or results are introduced here.

## iii. Table of contents

- A. The burn and the depletion boundary
- B. Restricted three-body equilibria
- C. The Jacobi integral and the forbidden region

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

/-- Collisions are excluded explicitly: at the first primary `r₁ = 0`, and the effective potential
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

/-! ## C. The Jacobi integral and the forbidden region -/

/-- **A nonzero-velocity state.** For equal masses, `μ = 1/2`, the barycenter `(0, 0)` is at
distance `1/2` from both primaries, and the state there with velocity `(1, 0)` has the Jacobi
constant `C = 2 · 2 - 1 = 3`. The triangular point `(1/2 - μ, √3/2) = (0, √3/2)` has
`2 Ω = 11/4 < 3`, so it is forbidden to the unforced trajectory through that state. -/
lemma jacobi_nonzero_velocity_fixture :
    0 < primaryDistOne (1 / 2) 0 0 ∧ 0 < primaryDistTwo (1 / 2) 0 0 ∧
      jacobiConstant (1 / 2) 0 0 1 0 = 3 ∧
      2 * effectivePotential (1 / 2) 0 (Real.sqrt 3 / 2) = 11 / 4 := by
  have hr1 : primaryDistOne (1 / 2) 0 0 = 1 / 2 := by
    have h : ((0 : ℝ) + 1 / 2) ^ 2 + (0 : ℝ) ^ 2 = (1 / 2) ^ 2 := by norm_num
    unfold primaryDistOne
    rw [h]
    exact Real.sqrt_sq (by norm_num)
  have hr2 : primaryDistTwo (1 / 2) 0 0 = 1 / 2 := by
    have h : ((0 : ℝ) - (1 - 1 / 2)) ^ 2 + (0 : ℝ) ^ 2 = (1 / 2) ^ 2 := by norm_num
    unfold primaryDistTwo
    rw [h]
    exact Real.sqrt_sq (by norm_num)
  have hC : jacobiConstant (1 / 2) 0 0 1 0 = 3 := by
    unfold jacobiConstant effectivePotential
    rw [hr1, hr2]
    norm_num
  have hsq3 : (Real.sqrt 3 / 2) ^ 2 = 3 / 4 := by
    have h3 : Real.sqrt 3 ^ 2 = 3 := Real.sq_sqrt (by norm_num)
    rw [div_pow, h3]
    norm_num
  have hr1t : primaryDistOne (1 / 2) 0 (Real.sqrt 3 / 2) = 1 := by
    have h : ((0 : ℝ) + 1 / 2) ^ 2 + (Real.sqrt 3 / 2) ^ 2 = 1 := by
      rw [hsq3]; norm_num
    unfold primaryDistOne
    rw [h]
    exact Real.sqrt_one
  have hr2t : primaryDistTwo (1 / 2) 0 (Real.sqrt 3 / 2) = 1 := by
    have h : ((0 : ℝ) - (1 - 1 / 2)) ^ 2 + (Real.sqrt 3 / 2) ^ 2 = 1 := by
      rw [hsq3]; norm_num
    unfold primaryDistTwo
    rw [h]
    exact Real.sqrt_one
  have hT : 2 * effectivePotential (1 / 2) 0 (Real.sqrt 3 / 2) = 11 / 4 := by
    unfold effectivePotential
    rw [hsq3, hr1t, hr2t]
    norm_num
  refine ⟨by rw [hr1]; norm_num, by rw [hr2]; norm_num, hC, hT⟩

/-- **Thrust breaks the forbidden region.** For `μ = 1/2` the `C²` path
`(x, y) = (t - t², (√3/2) t²)` avoids both primaries on `[0, 1]`, starts at the barycenter with
velocity `(1, 0)` (Jacobi constant `3`) and ends at the triangular point `(0, √3/2)`, where
`2 Ω = 11/4 < 3`. It obeys the rotating equations with the thrust acceleration it needs, so a
thrusting trajectory reaches a point that no unforced trajectory from the same state reaches. -/
lemma thrust_reaches_forbidden_point :
    ∃ x y ax ay : ℝ → ℝ, ContDiff ℝ 2 x ∧ ContDiff ℝ 2 y ∧
      (∀ t ∈ Icc (0 : ℝ) 1, 0 < primaryDistOne (1 / 2) (x t) (y t) ∧
        0 < primaryDistTwo (1 / 2) (x t) (y t) ∧
        deriv (deriv x) t - 2 * deriv y t =
          deriv (fun ξ => effectivePotential (1 / 2) ξ (y t)) (x t) + ax t ∧
        deriv (deriv y) t + 2 * deriv x t =
          deriv (fun η => effectivePotential (1 / 2) (x t) η) (y t) + ay t) ∧
      x 0 = 0 ∧ y 0 = 0 ∧ deriv x 0 = 1 ∧ deriv y 0 = 0 ∧ x 1 = 0 ∧ y 1 = Real.sqrt 3 / 2 ∧
      2 * effectivePotential (1 / 2) (x 1) (y 1) <
        jacobiConstant (1 / 2) (x 0) (y 0) (deriv x 0) (deriv y 0) := by
  have hXc : ContDiff ℝ 2 (fun s : ℝ => s - s ^ 2) := by fun_prop
  have hYc : ContDiff ℝ 2 (fun s : ℝ => (Real.sqrt 3 / 2) * s ^ 2) := by fun_prop
  have hdx : ∀ s, HasDerivAt (fun s : ℝ => s - s ^ 2) (1 - 2 * s) s := by
    intro s
    have h := (hasDerivAt_id' s).sub ((hasDerivAt_id' s).pow 2)
    convert h using 1; simp
  have hdy : ∀ s, HasDerivAt (fun s : ℝ => (Real.sqrt 3 / 2) * s ^ 2)
      ((Real.sqrt 3 / 2) * (2 * s)) s := by
    intro s
    have h := ((hasDerivAt_id' s).pow 2).const_mul (Real.sqrt 3 / 2)
    convert h using 1; simp
  have hdx0 : deriv (fun s : ℝ => s - s ^ 2) 0 = 1 := by
    rw [(hdx 0).deriv]; norm_num
  have hdy0 : deriv (fun s : ℝ => (Real.sqrt 3 / 2) * s ^ 2) 0 = 0 := by
    rw [(hdy 0).deriv]; norm_num
  have hx0 : (fun s : ℝ => s - s ^ 2) 0 = 0 := by norm_num
  have hy0 : (fun s : ℝ => (Real.sqrt 3 / 2) * s ^ 2) 0 = 0 := by norm_num
  have hx1 : (fun s : ℝ => s - s ^ 2) 1 = 0 := by norm_num
  have hy1 : (fun s : ℝ => (Real.sqrt 3 / 2) * s ^ 2) 1 = Real.sqrt 3 / 2 := by norm_num
  refine ⟨fun s : ℝ => s - s ^ 2, fun s : ℝ => (Real.sqrt 3 / 2) * s ^ 2,
    (fun u : ℝ => deriv (deriv fun s : ℝ => s - s ^ 2) u -
      2 * deriv (fun s : ℝ => (Real.sqrt 3 / 2) * s ^ 2) u -
      deriv (fun ξ => effectivePotential (1 / 2) ξ ((Real.sqrt 3 / 2) * u ^ 2)) (u - u ^ 2)),
    (fun u : ℝ => deriv (deriv fun s : ℝ => (Real.sqrt 3 / 2) * s ^ 2) u +
      2 * deriv (fun s : ℝ => s - s ^ 2) u -
      deriv (fun η => effectivePotential (1 / 2) (u - u ^ 2) η) ((Real.sqrt 3 / 2) * u ^ 2)),
    hXc, hYc, ?_, hx0, hy0, hdx0, hdy0, hx1, hy1, ?_⟩
  · intro t ht
    obtain ⟨ht0, ht1⟩ := ht
    have hxlo : (0 : ℝ) ≤ t - t ^ 2 :=
      by nlinarith [mul_nonneg ht0 (show (0 : ℝ) ≤ 1 - t by linarith)]
    have hxhi : t - t ^ 2 ≤ (1 : ℝ) / 4 := by nlinarith [sq_nonneg (t - 1 / 2)]
    have hXlo : (1 / 2 : ℝ) ≤ (t - t ^ 2) + 1 / 2 := by linarith
    have hsq1 : (1 / 4 : ℝ) ≤ ((t - t ^ 2) + 1 / 2) ^ 2 := by
      nlinarith [sq_nonneg (((t - t ^ 2) + 1 / 2) - 1 / 2), hXlo]
    have hr1 : (0 : ℝ) < ((t - t ^ 2) + 1 / 2) ^ 2 + ((Real.sqrt 3 / 2) * t ^ 2) ^ 2 := by
      have hnn : (0 : ℝ) ≤ ((Real.sqrt 3 / 2) * t ^ 2) ^ 2 := sq_nonneg _
      linarith
    have hX2hi : (t - t ^ 2) - 1 / 2 ≤ (-1 / 4 : ℝ) := by linarith [hxhi]
    have hsq2 : (1 / 16 : ℝ) ≤ ((t - t ^ 2) - (1 - 1 / 2)) ^ 2 := by
      have hsub : (t - t ^ 2) - (1 - 1 / 2) = (t - t ^ 2) - 1 / 2 := by ring
      rw [hsub]
      nlinarith [sq_nonneg (((t - t ^ 2) - 1 / 2) + 1 / 4), hX2hi]
    have hr2 : (0 : ℝ) < ((t - t ^ 2) - (1 - 1 / 2)) ^ 2 + ((Real.sqrt 3 / 2) * t ^ 2) ^ 2 := by
      have hnn : (0 : ℝ) ≤ ((Real.sqrt 3 / 2) * t ^ 2) ^ 2 := sq_nonneg _
      linarith
    refine ⟨?_, ?_, ?_, ?_⟩
    · simp only []
      unfold primaryDistOne
      exact Real.sqrt_pos.mpr hr1
    · simp only []
      unfold primaryDistTwo
      exact Real.sqrt_pos.mpr hr2
    · simp only []
      ring
    · simp only []
      ring
  · rw [hx1, hy1, hx0, hy0, hdx0, hdy0]
    have hfix := jacobi_nonzero_velocity_fixture
    rw [hfix.2.2.2, hfix.2.2.1]
    norm_num

/-- No unforced trajectory from the barycenter state with velocity `(1, 0)` reaches the
triangular point `(0, √3/2)` for equal masses: its Jacobi constant `3` exceeds `2 Ω = 11/4`
there. -/
example {t₁ : ℝ} {x y : ℝ → ℝ} (hx : ContDiff ℝ 2 x) (hy : ContDiff ℝ 2 y)
    (h₁ : ∀ t ∈ Icc 0 t₁, 0 < primaryDistOne (1 / 2) (x t) (y t))
    (h₂ : ∀ t ∈ Icc 0 t₁, 0 < primaryDistTwo (1 / 2) (x t) (y t))
    (hrot : ∀ t ∈ Icc 0 t₁,
      deriv (deriv x) t - 2 * deriv y t =
          deriv (fun ξ => effectivePotential (1 / 2) ξ (y t)) (x t) ∧
        deriv (deriv y) t + 2 * deriv x t =
          deriv (fun η => effectivePotential (1 / 2) (x t) η) (y t))
    (hx0 : x 0 = 0) (hy0 : y 0 = 0) (hvx : deriv x 0 = 1) (hvy : deriv y 0 = 0) :
    ∀ t ∈ Icc 0 t₁, ¬ (x t = 0 ∧ y t = Real.sqrt 3 / 2) := by
  obtain ⟨-, -, hC, hL⟩ := jacobi_nonzero_velocity_fixture
  apply not_reach_of_two_effectivePotential_lt hx hy h₁ h₂ hrot
  rw [hx0, hy0, hvx, hvy, hC, hL]
  norm_num

/-- The Jacobi integral along an actual unforced solution: the particle at rest at the triangular
point `(1/2 - μ, √3/2)` avoids both primaries and obeys the unforced rotating equations at every
time, so its Jacobi function is constant on every interval. -/
example (μ t₀ t₁ : ℝ) :
    ∀ t ∈ Icc t₀ t₁,
      jacobiConstant μ (1 / 2 - μ) (1 * (Real.sqrt 3 / 2)) (deriv (fun _ => 1 / 2 - μ) t)
          (deriv (fun _ => 1 * (Real.sqrt 3 / 2)) t) =
        jacobiConstant μ (1 / 2 - μ) (1 * (Real.sqrt 3 / 2)) (deriv (fun _ => 1 / 2 - μ) t₀)
          (deriv (fun _ => 1 * (Real.sqrt 3 / 2)) t₀) := by
  obtain ⟨hd1, hd2, -, -⟩ := triangular_equilibrium μ (s := 1) (Or.inl rfl)
  have hp1 : 0 < primaryDistOne μ (1 / 2 - μ) (1 * (Real.sqrt 3 / 2)) := by rw [hd1]; norm_num
  have hp2 : 0 < primaryDistTwo μ (1 / 2 - μ) (1 * (Real.sqrt 3 / 2)) := by rw [hd2]; norm_num
  refine jacobiConstant_eq_of_rotating_equations (x := fun _ => 1 / 2 - μ)
    (y := fun _ => 1 * (Real.sqrt 3 / 2)) contDiff_const contDiff_const (fun _ _ => hp1)
    (fun _ _ => hp2) fun t _ => ?_
  obtain ⟨h1, h2⟩ := rotating_equations (μ := μ) (t := t) (x := fun _ => 1 / 2 - μ)
    (y := fun _ => 1 * (Real.sqrt 3 / 2)) contDiff_const contDiff_const hp1 hp2
    (triangular_inertial_orbit μ (Or.inl rfl) t)
  exact ⟨h1, h2⟩

end PhyslibExtTest.Mechanics.SpaceTrajectoryModels
