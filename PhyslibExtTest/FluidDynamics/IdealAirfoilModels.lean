/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import PhyslibExt.FluidDynamics.IdealAirfoilModels

/-!
# Tests for ideal airfoil models

Checked consumers:

- the far-field branch inverts the Joukowski map at `z = 3` for
  `a = 1`, and lands outside the unit circle there;
- the circle parametrization at `θ = 0` gives the slit endpoint `2`;
- the Kutta condition with `Γ = 0` and `α = 0` is consistent, with the
  forced circulation `-4πaU sin α = 0`;
- the Blasius force of a pure far-field field (`e = 0`) at radius `3`
  is the Kutta-Joukowski expression.
-/

@[expose] public section

namespace FluidDynamics.IdealAirfoilModels

/-- At `θ = 0` the circle point `a * exp 0 = a` maps to `2a`. -/
example : JoukowskiBranch.joukowski 1 (1 * Complex.exp (0 * Complex.I)) =
    (2 * 1 * Real.cos 0 : ℂ) :=
  JoukowskiBranch.joukowski_circle

/-- The far-field branch at `z = 3`, `a = 1` inverts the Joukowski
map and lands outside the unit circle. -/
example : JoukowskiBranch.joukowski 1 (JoukowskiBranch.farFieldZeta 1 ((3 : ℝ) : ℂ)) =
    ((3 : ℝ) : ℂ) :=
  JoukowskiBranch.joukowski_farFieldZeta one_pos (by
    rw [Complex.norm_real]
    norm_num)

example : (1 : ℝ) < ‖JoukowskiBranch.farFieldZeta 1 ((3 : ℝ) : ℂ)‖ :=
  JoukowskiBranch.abs_farFieldZeta_gt one_pos (by
    rw [Complex.norm_real]
    norm_num)

/-- With `Γ = 0` and `α = 0` the Kutta numerator vanishes at `ζ = a`,
and the forced circulation `-4πaU sin α` is indeed `0`. -/
example : ((0 : ℝ) : ℂ) = ((-4 * Real.pi * 1 * 2 * Real.sin 0 : ℝ) : ℂ) :=
  JoukowskiBranch.kutta_cancellation (a := 1) (U := 2) (Γ := 0) (α := 0)
    one_pos (by simp)

/-- The Blasius force of the pure far-field field
`W z = U exp(-αI) + (Γ / 2πI) / z` (zero remainder) at radius `3` is
`I ρ U Γ exp(-αI)`. -/
example {ρ U Γ α : ℝ} (hρ : 0 < ρ) (hU : 0 < U) :
    BlasiusForce.blasiusForce ρ
        (fun z => (U : ℂ) * Complex.exp (-α * Complex.I) +
          ((Γ : ℂ) / (2 * Real.pi * Complex.I)) / z) 3 =
      Complex.I * ρ * U * Γ * Complex.exp (-α * Complex.I) := by
  have hW : DifferentiableOn ℂ
      (fun z => (U : ℂ) * Complex.exp (-α * Complex.I) +
        ((Γ : ℂ) / (2 * Real.pi * Complex.I)) / z) {z : ℂ | (1 : ℝ) < ‖z‖} := by
    intro z hz
    have hz0 : z ≠ 0 := by
      intro h
      subst h
      simp only [Set.mem_ofPred_eq, norm_zero] at hz
      norm_num at hz
    exact ((differentiableAt_const _).add
      ((differentiableAt_const _).div differentiableAt_id hz0)).differentiableWithinAt
  have hdecomp : ∀ z : ℂ, (2 : ℝ) ≤ ‖z‖ →
      (fun z => (U : ℂ) * Complex.exp (-α * Complex.I) +
        ((Γ : ℂ) / (2 * Real.pi * Complex.I)) / z) z =
        (U : ℂ) * Complex.exp (-α * Complex.I) +
          ((Γ : ℂ) / (2 * Real.pi * Complex.I)) / z + (fun _ => (0 : ℂ)) z := by
    intro z _
    simp
  have he : ∀ z : ℂ, (2 : ℝ) ≤ ‖z‖ → DifferentiableAt ℂ (fun _ => (0 : ℂ)) z :=
    fun _ _ => differentiableAt_const 0
  have hbound : ∀ z : ℂ, (2 : ℝ) ≤ ‖z‖ → ‖(fun _ => (0 : ℂ)) z‖ ≤ (0 : ℝ) / ‖z‖ ^ 2 := by
    intro z _
    simp
  exact BlasiusForce.blasiusForce_eq (R0 := 1) (R1 := 2) (K := 0) hρ hU
    (by norm_num) (by norm_num) hW hdecomp he hbound (by norm_num)

end FluidDynamics.IdealAirfoilModels
