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
- the signed-lift composite at any contour radius `R > 2a`, with the
  force hypothesis discharged by the bridge lemma, and its
  `π / 6` fixture at radius `3`.
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

/-- The far-field branch at `z = 3`, `a = 1` lies beyond half the
radius: `‖z‖ / 2 < ‖ζ(z)‖`. -/
example : ‖((3 : ℝ) : ℂ)‖ / 2 <
    ‖JoukowskiBranch.farFieldZeta 1 ((3 : ℝ) : ℂ)‖ :=
  JoukowskiBranch.norm_farFieldZeta_gt_half one_pos (by
    rw [Complex.norm_real]
    norm_num)

/-- Holomorphy of the physical velocity on the far-field exterior,
at `a = 1`, `U = 2`, `Γ = α = 0`. -/
example : DifferentiableOn ℂ (JoukowskiBranch.physicalVelocity 1 2 0 0)
    {z : ℂ | 2 * (1 : ℝ) < ‖z‖} :=
  JoukowskiBranch.differentiableOn_physicalVelocity one_pos 2 0 0

/-- Nonzero-circulation fixture: `a = 1`, `U = 1`, `Γ = 1`, `α = 0` has a
nonzero `1 / z` tail coefficient and a finite bound with `R1 = 4`, `K = 13`. -/
example :
    (1 : ℂ) / (2 * Real.pi * Complex.I) ≠ 0 ∧
      ∀ z : ℂ, 4 ≤ ‖z‖ →
        ‖JoukowskiBranch.physicalVelocity 1 1 1 0 z - 1 - 1 / (2 * Real.pi * Complex.I * z)‖ ≤
          13 / ‖z‖ ^ 2 := by
  constructor
  · exact div_ne_zero one_ne_zero
      (mul_ne_zero (mul_ne_zero (by norm_num) (by exact_mod_cast Real.pi_ne_zero))
        Complex.I_ne_zero)
  · intro z hz
    have h1 : (0 : ℝ) < 1 := by norm_num
    have h2 : 4 * 1 ≤ ‖z‖ := by rwa [mul_one]
    have h := JoukowskiBranch.physicalVelocity_farField_bound h1 1 1 0 h2
    have hU : ((1 : ℝ) : ℂ) * Complex.exp (-(0 : ℝ) * Complex.I) = 1 := by
      rw [Complex.ofReal_one, Complex.ofReal_zero, neg_zero, zero_mul,
        Complex.exp_zero, one_mul]
    have hK : (12 * |(1 : ℝ)| * (1 : ℝ) ^ 2 + 1 * |(1 : ℝ)|) = 13 := by norm_num
    rw [hU, hK, Complex.ofReal_one] at h
    exact h

/-- Invalid-point fixture: the leading edge `z = -2a` maps to `ζ = -a`, where
the conformal denominator vanishes, and it lies outside the bound region. -/
example {a : ℝ} (ha : 0 < a) :
    JoukowskiBranch.farFieldZeta a (-(2 * a : ℂ)) = -(a : ℂ) ∧
      1 - (a : ℂ) ^ 2 / (JoukowskiBranch.farFieldZeta a (-(2 * a : ℂ))) ^ 2 = 0 ∧
      ¬ (4 * a ≤ ‖(-(2 * a : ℂ))‖) := by
  have ha0 : (a : ℂ) ≠ 0 := by exact_mod_cast ne_of_gt ha
  have hz2 : (-(2 * a : ℂ)) ^ 2 = 4 * (a : ℂ) ^ 2 := by ring
  have h4a : (4 : ℂ) * (a : ℂ) ^ 2 ≠ 0 :=
    mul_ne_zero (by norm_num) (pow_ne_zero 2 ha0)
  have hrad : (1 - 4 * (a : ℂ) ^ 2 / (-(2 * a : ℂ)) ^ 2 : ℂ) = 0 := by
    rw [hz2, div_self h4a, sub_self]
  have hζ : JoukowskiBranch.farFieldZeta a (-(2 * a : ℂ)) = -(a : ℂ) := by
    unfold JoukowskiBranch.farFieldZeta
    rw [hrad, Complex.sqrt_zero, add_zero, mul_one]
    ring
  have hD : (1 - (a : ℂ) ^ 2 / (JoukowskiBranch.farFieldZeta a (-(2 * a : ℂ))) ^ 2 : ℂ) = 0 := by
    rw [hζ]
    have hsq : (-(a : ℂ)) ^ 2 = (a : ℂ) ^ 2 := by ring
    rw [hsq, div_self (pow_ne_zero 2 ha0), sub_self]
  have hnorm : ‖(-(2 * a : ℂ))‖ = 2 * a := by
    rw [norm_neg, norm_mul, show ‖(2 : ℂ)‖ = 2 by simp, Complex.norm_real,
      Real.norm_eq_abs, abs_of_pos ha]
  have hneg : ¬ (4 * a ≤ ‖(-(2 * a : ℂ))‖) := by
    intro hcon
    rw [hnorm] at hcon
    linarith [hcon, ha]
  exact ⟨hζ, hD, hneg⟩

/-- The existential far-field package at `a = 1`: holomorphy on the
exterior plus some radius and constant with the `K / ‖z‖^2` bound. -/
example {U Γ α : ℝ} :
    DifferentiableOn ℂ (JoukowskiBranch.physicalVelocity 1 U Γ α)
        {z : ℂ | 2 * (1 : ℝ) < ‖z‖} ∧
      ∃ R1 K : ℝ, 2 * (1 : ℝ) < R1 ∧ 0 ≤ K ∧ ∀ z : ℂ, R1 ≤ ‖z‖ →
        ‖JoukowskiBranch.physicalVelocity 1 U Γ α z -
            (U : ℂ) * Complex.exp (-α * Complex.I) -
            (Γ : ℂ) / (2 * Real.pi * Complex.I * z)‖ ≤ K / ‖z‖ ^ 2 :=
  JoukowskiBranch.exists_physicalVelocity_farField one_pos U Γ α

/-- Seam discharge: at any contour radius `R > 2a`, the composite
signed-lift conclusions hold for the physical velocity with no force
hypothesis left open: the far-field package supplies the expansion
hypothesis and the bridge lemma supplies the Blasius force value. -/
example {a ρ U α R : ℝ} (ha : 0 < a) (hρ : 0 < ρ) (hU : 0 < U)
    (hR : 2 * a < R) :
    KuttaJoukowski.signedLift (BlasiusForce.blasiusForce ρ
        (JoukowskiBranch.physicalVelocity a U
          (-4 * Real.pi * a * U * Real.sin α) α) R) α =
        -ρ * U * (-4 * Real.pi * a * U * Real.sin α) ∧
      KuttaJoukowski.liftCoefficient (KuttaJoukowski.signedLift
        (BlasiusForce.blasiusForce ρ
          (JoukowskiBranch.physicalVelocity a U
            (-4 * Real.pi * a * U * Real.sin α) α) R) α)
          ρ U (4 * a) =
        2 * Real.pi * Real.sin α ∧
      |KuttaJoukowski.liftCoefficient (KuttaJoukowski.signedLift
        (BlasiusForce.blasiusForce ρ
          (JoukowskiBranch.physicalVelocity a U
            (-4 * Real.pi * a * U * Real.sin α) α) R) α)
          ρ U (4 * a) -
        2 * Real.pi * α| ≤ Real.pi * |α| ^ 3 / 3 :=
  KuttaJoukowski.signedLift_liftCoefficient_kutta ha hρ hU
    (JoukowskiBranch.exists_physicalVelocity_farField ha U
      (-4 * Real.pi * a * U * Real.sin α) α)
    (KuttaJoukowski.blasiusForce_physicalVelocity ha hρ hU hR)

/-- The `π / 6` fixture at contour radius `3`, with its force
hypothesis discharged by the bridge lemma: signed lift `2π` and lift
coefficient `π`, both positive. -/
example :
    KuttaJoukowski.signedLift (BlasiusForce.blasiusForce 1
        (JoukowskiBranch.physicalVelocity 1 1
          (-4 * Real.pi * 1 * 1 * Real.sin (Real.pi / 6))
          (Real.pi / 6)) 3) (Real.pi / 6) = 2 * Real.pi ∧
      0 < KuttaJoukowski.signedLift (BlasiusForce.blasiusForce 1
        (JoukowskiBranch.physicalVelocity 1 1
          (-4 * Real.pi * 1 * 1 * Real.sin (Real.pi / 6))
          (Real.pi / 6)) 3) (Real.pi / 6) ∧
      KuttaJoukowski.liftCoefficient (KuttaJoukowski.signedLift
        (BlasiusForce.blasiusForce 1
          (JoukowskiBranch.physicalVelocity 1 1
            (-4 * Real.pi * 1 * 1 * Real.sin (Real.pi / 6))
            (Real.pi / 6)) 3) (Real.pi / 6)) 1 1 (4 * 1) = Real.pi ∧
      0 < KuttaJoukowski.liftCoefficient (KuttaJoukowski.signedLift
        (BlasiusForce.blasiusForce 1
          (JoukowskiBranch.physicalVelocity 1 1
            (-4 * Real.pi * 1 * 1 * Real.sin (Real.pi / 6))
            (Real.pi / 6)) 3) (Real.pi / 6)) 1 1 (4 * 1) :=
  KuttaJoukowski.fixture_pi_div_six
    (KuttaJoukowski.blasiusForce_physicalVelocity one_pos one_pos one_pos
      (by norm_num))

end FluidDynamics.IdealAirfoilModels
