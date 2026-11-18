/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Analysis.Complex.CauchyIntegral
public import Mathlib.Analysis.Complex.SqrtDeriv
public import Mathlib.Analysis.SpecialFunctions.Complex.Circle
public import Mathlib.MeasureTheory.Integral.CircleIntegral
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Ring

/-!
# Ideal airfoil models: Joukowski branch and Blasius force

## i. Overview

Two classical ideal-flow models for a circular-cylinder airfoil. The
Joukowski map `J(ζ) = ζ + a^2 / ζ` sends the circle `|ζ| = a` to the
real slit `[-2a, 2a]`; on the exterior region `2a < ‖z‖` the far-field
inverse branch `ζ(z) = (z/2)(1 + sqrt(1 - 4a^2/z^2))`, with the principal
square root, is a holomorphic right inverse landing outside `|ζ| = a`,
and the Kutta condition at the trailing edge `ζ = a` forces
`Γ = -4πaU sin α`. For a complex velocity `W` holomorphic outside a
circle with far-field expansion `W = U exp(-αI) + (Γ / 2πI)/z + e`,
`‖e z‖ ≤ K/‖z‖^2`, the Blasius force per unit span at every larger
radius is `I ρ U Γ exp(-αI)` (the Kutta-Joukowski lift, in complex
form). These are conditional model identities: holomorphy and the
far-field expansion are hypotheses, not derived from flow equations.

## ii. Key results

- `FluidDynamics.IdealAirfoilModels.JoukowskiBranch.joukowski_circle`:
  the circle maps to the slit point `2a cos θ`.
- `FluidDynamics.IdealAirfoilModels.JoukowskiBranch.joukowski_farFieldZeta`:
  the far-field branch inverts the Joukowski map on `2a < ‖z‖`.
- `FluidDynamics.IdealAirfoilModels.JoukowskiBranch.kutta_cancellation`:
  the Kutta condition gives `Γ = -4πaU sin α`.
- `FluidDynamics.IdealAirfoilModels.JoukowskiBranch.exists_physicalVelocity_farField`:
  the physical velocity `circleVelocity ζ(z) / (1 - a^2 / ζ(z)^2)` is
  holomorphic on `2a < ‖z‖` and differs from
  `U exp(-αI) + Γ / (2πI z)` by at most `K / ‖z‖^2` for `4a ≤ ‖z‖`,
  with `K = 12|U| a^2 + a|Γ|`.
- `FluidDynamics.IdealAirfoilModels.BlasiusForce.blasiusForce_eq`:
  the Blasius force from a far-field expansion.

## iii. Table of contents

- A. The Joukowski far-field branch
- B. Blasius force from a far-field expansion

## iv. References

- The Joukowski transform and the Kutta condition are classical in
  ideal-flow aerodynamics; the Blasius force formula and its
  Kutta-Joukowski consequence are standard (e.g. Batchelor,
  *An Introduction to Fluid Dynamics*, §§6.4-6.5, for the force on a
  cylinder from the complex potential).

## A. The Joukowski far-field branch
-/

@[expose] public section

namespace FluidDynamics.IdealAirfoilModels

namespace JoukowskiBranch

/-- The Joukowski map `J(ζ) = ζ + a^2 / ζ` (totalized at `ζ = 0`). -/
noncomputable def joukowski (a ζ : ℂ) : ℂ := ζ + a ^ 2 / ζ

/-- The far-field inverse branch
`ζ(z) = (z / 2) * (1 + sqrt (1 - 4 * a^2 / z^2))` with the principal
square root. -/
noncomputable def farFieldZeta (a z : ℂ) : ℂ :=
  (z / 2) * (1 + Complex.sqrt (1 - 4 * a ^ 2 / z ^ 2))

/-- The principal square root squared is the identity on the slit plane. -/
private theorem sq_sqrt_of_mem_slitPlane {w : ℂ} (hw : w ∈ Complex.slitPlane) :
    (Complex.sqrt w) ^ 2 = w := by
  have hw0 : w ≠ 0 := by
    rintro rfl
    rcases hw with h | h <;> simp at h
  rw [sqrt_eq_exp hw0, sq, ← Complex.exp_add]
  have hlog : Complex.log w / 2 + Complex.log w / 2 = Complex.log w := by ring
  rw [hlog, Complex.exp_log hw0]

/-- Boundary parametrization: the circle point `a * exp (θ * I)`
maps to the real slit point `2 * a * cos θ`. -/
theorem joukowski_circle {a θ : ℝ} :
    joukowski a (a * Complex.exp (θ * Complex.I)) =
      (2 * a * Real.cos θ : ℂ) := by
  unfold joukowski
  by_cases ha0 : (a : ℂ) = 0
  · have ha0' : a = 0 := Complex.ofReal_eq_zero.mp ha0
    subst ha0'
    simp
  · have hE : Complex.exp ((θ : ℂ) * Complex.I) ≠ 0 := Complex.exp_ne_zero _
    have h2 : (a : ℂ) ^ 2 / ((a : ℂ) * Complex.exp ((θ : ℂ) * Complex.I))
        = (a : ℂ) * Complex.exp (-((θ : ℂ) * Complex.I)) := by
      rw [div_eq_iff (mul_ne_zero ha0 hE)]
      have hexp : Complex.exp (-((θ : ℂ) * Complex.I))
          * Complex.exp ((θ : ℂ) * Complex.I) = 1 := by
        rw [← Complex.exp_add, neg_add_cancel, Complex.exp_zero]
      linear_combination (-(a : ℂ) ^ 2) * hexp
    have hcos := Complex.two_cos ((θ : ℝ) : ℂ)
    have hneg : (-(θ : ℂ)) * Complex.I = -((θ : ℂ) * Complex.I) := by ring
    rw [hneg] at hcos
    have hfac : (a : ℂ) * Complex.exp ((θ : ℂ) * Complex.I)
          + (a : ℂ) * Complex.exp (-((θ : ℂ) * Complex.I))
        = (a : ℂ) * (2 * Complex.cos (θ : ℂ)) := by
      linear_combination (-(a : ℂ)) * hcos
    rw [h2, hfac, ← Complex.ofReal_cos]
    push_cast
    ring

/-- The radicand `1 - 4 * a^2 / z^2` lies in the principal slit
plane whenever `2 * a < ‖z‖` and `0 < a`. -/
theorem radicand_mem_slitPlane {a : ℝ} (ha : 0 < a) {z : ℂ}
    (hz : 2 * a < ‖z‖) :
    (1 - 4 * a ^ 2 / z ^ 2) ∈ Complex.slitPlane := by
  have hzz : (0 : ℝ) < ‖z‖ := by linarith [hz, ha]
  have hnorm : ‖(4 * a ^ 2 / z ^ 2 : ℂ)‖ < 1 := by
    simp only [norm_div, norm_mul, norm_pow, Complex.norm_ofNat, Complex.norm_real,
      Real.norm_eq_abs, abs_of_pos ha]
    rw [div_lt_one (pow_pos hzz 2)]
    have h2 : (2 * a) ^ 2 < ‖z‖ ^ 2 :=
      pow_lt_pow_left₀ hz (show (0 : ℝ) ≤ 2 * a by linarith) (show 2 ≠ 0 by norm_num)
    have heq : (4 : ℝ) * a ^ 2 = (2 * a) ^ 2 := by ring
    rw [heq]
    exact h2
  refine Or.inl ?_
  rw [Complex.sub_re, Complex.one_re]
  have hle : (4 * a ^ 2 / z ^ 2 : ℂ).re ≤ ‖(4 * a ^ 2 / z ^ 2 : ℂ)‖ :=
    Complex.re_le_norm _
  linarith [hnorm, hle]

/-- The far-field branch is a right inverse of the Joukowski map
on the exterior region `2 * a < ‖z‖`. -/
theorem joukowski_farFieldZeta {a : ℝ} (ha : 0 < a) {z : ℂ}
    (hz : 2 * a < ‖z‖) :
    joukowski a (farFieldZeta a z) = z := by
  have hzz : (0 : ℝ) < ‖z‖ := by linarith [hz, ha]
  have hz0 : z ≠ 0 := norm_pos_iff.mp hzz
  have hz2 : z ^ 2 ≠ 0 := pow_ne_zero 2 hz0
  have hmem : (1 - 4 * a ^ 2 / z ^ 2 : ℂ) ∈ Complex.slitPlane :=
    radicand_mem_slitPlane ha hz
  have hs2 : (Complex.sqrt (1 - 4 * a ^ 2 / z ^ 2 : ℂ)) ^ 2
      = 1 - 4 * a ^ 2 / z ^ 2 :=
    sq_sqrt_of_mem_slitPlane hmem
  have hζne : farFieldZeta (a : ℂ) z ≠ 0 := by
    intro hcon
    unfold farFieldZeta at hcon
    have hz2' : (z : ℂ) / 2 ≠ 0 := div_ne_zero hz0 (by norm_num)
    rw [mul_eq_zero] at hcon
    cases hcon with
    | inl h => exact hz2' h
    | inr h =>
      have hs1 : Complex.sqrt (1 - 4 * a ^ 2 / z ^ 2 : ℂ) = -1 := by
        linear_combination h
      have hsq := congrArg (fun w : ℂ => w ^ 2) hs1
      rw [hs2] at hsq
      have hw1 : (1 - 4 * a ^ 2 / z ^ 2 : ℂ) = 1 := by
        linear_combination hsq
      have h40 : (4 : ℂ) * (a : ℂ) ^ 2 / z ^ 2 = 0 := by
        linear_combination -hw1
      rw [div_eq_zero_iff] at h40
      cases h40 with
      | inl h40 =>
        have hsq0 : (a : ℂ) ^ 2 = 0 := by
          linear_combination (1 / 4 : ℂ) * h40
        have hmul : (a : ℂ) * (a : ℂ) = 0 := by
          simpa [sq] using hsq0
        rcases mul_eq_zero.mp hmul with h' | h' <;>
          exact absurd (Complex.ofReal_eq_zero.mp h') (ne_of_gt ha)
      | inr h40 => exact hz2 h40
  have hs2' : (Complex.sqrt (1 - 4 * a ^ 2 / z ^ 2 : ℂ)) ^ 2 * z ^ 2
      = z ^ 2 - 4 * (a : ℂ) ^ 2 := by
    have h := congrArg (fun w : ℂ => w * z ^ 2) hs2
    rw [sub_mul, one_mul, div_mul_cancel₀ _ hz2] at h
    exact h
  have hquad : (farFieldZeta (a : ℂ) z) ^ 2
      - z * farFieldZeta (a : ℂ) z + (a : ℂ) ^ 2 = 0 := by
    unfold farFieldZeta
    linear_combination (1 / 4 : ℂ) * hs2'
  unfold joukowski
  have e : (a : ℂ) ^ 2 / farFieldZeta (a : ℂ) z
      = z - farFieldZeta (a : ℂ) z := by
    rw [div_eq_iff hζne]
    linear_combination hquad
  linear_combination e

/-- The far-field branch lands outside the circle of radius `a`:
`a < ‖ζ(z)‖` whenever `2 * a < ‖z‖`. -/
theorem abs_farFieldZeta_gt {a : ℝ} (ha : 0 < a) {z : ℂ}
    (hz : 2 * a < ‖z‖) :
    a < ‖farFieldZeta a z‖ := by
  have hzz : (0 : ℝ) < ‖z‖ := by linarith [hz, ha]
  have hmem : (1 - 4 * a ^ 2 / z ^ 2 : ℂ) ∈ Complex.slitPlane :=
    radicand_mem_slitPlane ha hz
  have hre : 0 < (Complex.sqrt (1 - 4 * a ^ 2 / z ^ 2 : ℂ)).re := by
    have hre_eq : (Complex.sqrt (1 - 4 * a ^ 2 / z ^ 2 : ℂ)).re
        = √((‖(1 - 4 * a ^ 2 / z ^ 2 : ℂ)‖ + (1 - 4 * a ^ 2 / z ^ 2 : ℂ).re) / 2) := by
      have hform := Complex.sqrt_eq_real_add_ite (a := (1 - 4 * a ^ 2 / z ^ 2 : ℂ))
      rw [hform]
      by_cases him : (0 : ℝ) ≤ (1 - 4 * a ^ 2 / z ^ 2 : ℂ).im
      · simp only [him, ite_true]
        simp [Complex.add_re, Complex.mul_re, Complex.ofReal_re,
          Complex.ofReal_im, Complex.I_re, Complex.I_im, Complex.one_re]
      · simp only [him, ite_false]
        simp [Complex.add_re, Complex.mul_re, Complex.ofReal_re,
          Complex.ofReal_im, Complex.I_re, Complex.I_im, Complex.one_re,
          Complex.neg_re]
    rw [hre_eq, Real.sqrt_pos]
    rcases hmem with hpos | hne
    · have hnn := norm_nonneg (1 - 4 * a ^ 2 / z ^ 2 : ℂ)
      linarith [hnn, hpos]
    · have hsq : ‖(1 - 4 * a ^ 2 / z ^ 2 : ℂ)‖ ^ 2
          = (1 - 4 * a ^ 2 / z ^ 2 : ℂ).re * (1 - 4 * a ^ 2 / z ^ 2 : ℂ).re
            + (1 - 4 * a ^ 2 / z ^ 2 : ℂ).im * (1 - 4 * a ^ 2 / z ^ 2 : ℂ).im := by
        rw [Complex.norm_def, Real.sq_sqrt (Complex.normSq_nonneg _),
          Complex.normSq_apply]
      have him2 : (0 : ℝ)
          < (1 - 4 * a ^ 2 / z ^ 2 : ℂ).im * (1 - 4 * a ^ 2 / z ^ 2 : ℂ).im :=
        mul_self_pos.mpr hne
      have hle : (1 - 4 * a ^ 2 / z ^ 2 : ℂ).re ≤ ‖(1 - 4 * a ^ 2 / z ^ 2 : ℂ)‖ :=
        Complex.re_le_norm _
      have hprod : (0 : ℝ)
          < (‖(1 - 4 * a ^ 2 / z ^ 2 : ℂ)‖ + (1 - 4 * a ^ 2 / z ^ 2 : ℂ).re)
            * (‖(1 - 4 * a ^ 2 / z ^ 2 : ℂ)‖ - (1 - 4 * a ^ 2 / z ^ 2 : ℂ).re) := by
        have heq : (‖(1 - 4 * a ^ 2 / z ^ 2 : ℂ)‖ + (1 - 4 * a ^ 2 / z ^ 2 : ℂ).re)
              * (‖(1 - 4 * a ^ 2 / z ^ 2 : ℂ)‖ - (1 - 4 * a ^ 2 / z ^ 2 : ℂ).re)
            = (1 - 4 * a ^ 2 / z ^ 2 : ℂ).im * (1 - 4 * a ^ 2 / z ^ 2 : ℂ).im := by
          linear_combination hsq
        rw [heq]
        exact him2
      have hnn : (0 : ℝ)
          ≤ ‖(1 - 4 * a ^ 2 / z ^ 2 : ℂ)‖ - (1 - 4 * a ^ 2 / z ^ 2 : ℂ).re := by
        linarith [hle]
      have hpos2 : (0 : ℝ)
          < ‖(1 - 4 * a ^ 2 / z ^ 2 : ℂ)‖ + (1 - 4 * a ^ 2 / z ^ 2 : ℂ).re :=
        pos_of_mul_pos_left hprod hnn
      linarith [hpos2]
  have h1s : (1 : ℝ) < ‖(1 + Complex.sqrt (1 - 4 * a ^ 2 / z ^ 2 : ℂ))‖ := by
    have hle : (1 + Complex.sqrt (1 - 4 * a ^ 2 / z ^ 2 : ℂ)).re
        ≤ ‖(1 + Complex.sqrt (1 - 4 * a ^ 2 / z ^ 2 : ℂ))‖ :=
      Complex.re_le_norm _
    have hre1 : (1 + Complex.sqrt (1 - 4 * a ^ 2 / z ^ 2 : ℂ)).re
        = 1 + (Complex.sqrt (1 - 4 * a ^ 2 / z ^ 2 : ℂ)).re := by
      rw [Complex.add_re, Complex.one_re]
    linarith [hle, hre, hre1]
  have hnorm : ‖farFieldZeta (a : ℂ) z‖
      = (‖z‖ / 2) * ‖(1 + Complex.sqrt (1 - 4 * a ^ 2 / z ^ 2 : ℂ))‖ := by
    unfold farFieldZeta
    rw [norm_mul, norm_div, Complex.norm_ofNat]
  rw [hnorm]
  have h2a : (0 : ℝ) < ‖z‖ / 2 := by linarith [hzz]
  have hlt : (‖z‖ / 2) * 1
      < (‖z‖ / 2) * ‖(1 + Complex.sqrt (1 - 4 * a ^ 2 / z ^ 2 : ℂ))‖ :=
    mul_lt_mul_of_pos_left h1s h2a
  have hza : a < ‖z‖ / 2 := by linarith [hz]
  linarith [hlt, hza]

/-- The far-field branch is holomorphic on the exterior region. -/
theorem differentiableAt_farFieldZeta {a : ℝ} (ha : 0 < a) {z : ℂ}
    (hz : 2 * a < ‖z‖) :
    DifferentiableAt ℂ (farFieldZeta a) z := by
  have hzz : (0 : ℝ) < ‖z‖ := by linarith [hz, ha]
  have hz0 : z ≠ 0 := norm_pos_iff.mp hzz
  have hz2 : z ^ 2 ≠ 0 := pow_ne_zero 2 hz0
  have hmem : (1 - 4 * a ^ 2 / z ^ 2 : ℂ) ∈ Complex.slitPlane :=
    radicand_mem_slitPlane ha hz
  have h1 : DifferentiableAt ℂ (fun z : ℂ => z ^ 2) z := differentiableAt_pow 2
  have hdiv : DifferentiableAt ℂ (fun z : ℂ => 4 * (a : ℂ) ^ 2 / z ^ 2) z :=
    (differentiableAt_const ((4 : ℂ) * (a : ℂ) ^ 2)).fun_div h1 hz2
  have hsub : DifferentiableAt ℂ (fun z : ℂ => 1 - 4 * (a : ℂ) ^ 2 / z ^ 2) z :=
    (differentiableAt_const (1 : ℂ)).fun_sub hdiv
  have hcomp : DifferentiableAt ℂ
      (fun z : ℂ => Complex.sqrt (1 - 4 * (a : ℂ) ^ 2 / z ^ 2)) z :=
    DifferentiableAt.comp (g := Complex.sqrt) z (Complex.differentiableAt_sqrt hmem)
      hsub
  have hleft : DifferentiableAt ℂ (fun z : ℂ => z / 2) z :=
    differentiableAt_id.div_const 2
  have hright : DifferentiableAt ℂ
      (fun z : ℂ => 1 + Complex.sqrt (1 - 4 * (a : ℂ) ^ 2 / z ^ 2)) z :=
    hcomp.const_add 1
  unfold farFieldZeta
  exact hleft.fun_mul hright

/-- Kutta cancellation at the trailing edge `ζ = a`: if the
circle-plane numerator
`U * (exp (-α * I) - a^2 * exp (α * I) / ζ^2) + Γ / (2 * π * I * ζ)`
vanishes at `ζ = a`, then `Γ = -4 * π * a * U * sin α`. -/
theorem kutta_cancellation {a U Γ α : ℝ} (ha : 0 < a) :
    (U : ℂ) * (Complex.exp (-α * Complex.I) -
        a ^ 2 * Complex.exp (α * Complex.I) / (a : ℂ) ^ 2) +
      (Γ : ℂ) / (2 * Real.pi * Complex.I * a) = 0 →
    (Γ : ℂ) = (-4 * Real.pi * a * U * Real.sin α : ℝ) := by
  intro h
  have ha0 : (a : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (ne_of_gt ha)
  have ha20 : (a : ℂ) ^ 2 ≠ 0 := pow_ne_zero 2 ha0
  rw [mul_div_cancel_left₀ _ ha20] at h
  have hsin := Complex.two_sin ((α : ℝ) : ℂ)
  have hD : (Complex.exp ((-(α : ℂ)) * Complex.I) - Complex.exp ((α : ℂ) * Complex.I))
      = -(2 * Complex.sin (α : ℂ) * Complex.I) := by
    have h1 := congrArg (· * Complex.I) hsin.symm
    simp only [mul_assoc, Complex.I_mul_I] at h1
    linear_combination -h1
  rw [hD, ← Complex.ofReal_sin] at h
  have h2 : ((2 : ℂ)) ≠ 0 := by norm_num
  have hpi : ((Real.pi : ℝ) : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr Real.pi_ne_zero
  have hM : (2 * Real.pi * Complex.I * (a : ℂ) : ℂ) ≠ 0 :=
    mul_ne_zero (mul_ne_zero (mul_ne_zero h2 hpi) Complex.I_ne_zero) ha0
  have hlin : (Γ : ℂ) / (2 * Real.pi * Complex.I * (a : ℂ))
      = -((U : ℂ) * (-(2 * ((Real.sin α : ℝ) : ℂ) * Complex.I))) := by
    linear_combination h
  rw [div_eq_iff hM] at hlin
  rw [hlin]
  have hcast : ((-4 * Real.pi * a * U * Real.sin α : ℝ) : ℂ)
      = -4 * (Real.pi : ℂ) * (a : ℂ) * (U : ℂ) * ((Real.sin α) : ℂ) := by
    push_cast
    ring
  rw [hcast]
  linear_combination (4 * (U : ℂ) * ((Real.sin α) : ℂ) * (Real.pi : ℂ) * (a : ℂ)) *
    Complex.I_mul_I


private theorem norm_ratio (a : ℝ) (ζ : ℂ) :
    ‖(a : ℂ) ^ 2 / ζ ^ 2‖ = a ^ 2 / ‖ζ‖ ^ 2 := by
  rw [norm_div, norm_pow, norm_pow, Complex.norm_real, Real.norm_eq_abs, sq_abs]

private theorem denominator_ne_zero {a : ℝ} (ha : 0 < a) {z : ℂ}
    (hz : 2 * a < ‖z‖) :
    (1 - (a : ℂ) ^ 2 / (farFieldZeta a z) ^ 2) ≠ 0 := by
  intro hcon
  have hζpos : (0 : ℝ) < ‖farFieldZeta a z‖ := by
    have h := abs_farFieldZeta_gt ha hz
    linarith [h, ha]
  have hw1 : (a : ℂ) ^ 2 / (farFieldZeta a z) ^ 2 = 1 := by
    linear_combination -hcon
  have hsq : a ^ 2 < ‖farFieldZeta a z‖ ^ 2 :=
    pow_lt_pow_left₀ (abs_farFieldZeta_gt ha hz) (le_of_lt ha)
      (show 2 ≠ 0 by norm_num)
  have hζ2pos : (0 : ℝ) < ‖farFieldZeta a z‖ ^ 2 := pow_pos hζpos 2
  have hlt : ‖(a : ℂ) ^ 2 / (farFieldZeta a z) ^ 2‖ < 1 := by
    rw [norm_ratio, div_lt_one hζ2pos]
    exact hsq
  rw [hw1, norm_one] at hlt
  linarith [hlt]


/-! ## Physical complex velocity and its far-field remainder -/

/-- Circle-plane complex velocity (the Kutta numerator):
`U * (exp (-α * I) - a^2 * exp (α * I) / ζ^2) + Γ / (2 * π * I * ζ)`. -/
noncomputable def circleVelocity (a U Γ α : ℝ) (ζ : ℂ) : ℂ :=
  (U : ℂ) * (Complex.exp (-α * Complex.I) -
      a ^ 2 * Complex.exp (α * Complex.I) / ζ ^ 2) +
    (Γ : ℂ) / (2 * Real.pi * Complex.I * ζ)

/-- Physical complex velocity on the far-field branch:
`W(z) = circleVelocity (ζ(z)) / (1 - a^2 / ζ(z)^2)` with `ζ = farFieldZeta a z`
(division totalized; the denominator vanishes only at `ζ = ±a`). -/
noncomputable def physicalVelocity (a U Γ α : ℝ) (z : ℂ) : ℂ :=
  circleVelocity a U Γ α (farFieldZeta a z) /
    (1 - a ^ 2 / (farFieldZeta a z) ^ 2)

/-- Convention check: at the trailing edge `ζ = a` the circle velocity is
exactly the left-hand side of the merged `kutta_cancellation`. -/
theorem circleVelocity_trailingEdge (a U Γ α : ℝ) :
    circleVelocity a U Γ α (a : ℂ) =
      (U : ℂ) * (Complex.exp (-α * Complex.I) -
          a ^ 2 * Complex.exp (α * Complex.I) / (a : ℂ) ^ 2) +
        (Γ : ℂ) / (2 * Real.pi * Complex.I * a) := by
  rfl

/-- Route step: on the exterior region the branch satisfies
`‖z‖ / 2 < ‖ζ(z)‖`. -/
theorem norm_farFieldZeta_gt_half {a : ℝ} (ha : 0 < a) {z : ℂ}
    (hz : 2 * a < ‖z‖) :
    ‖z‖ / 2 < ‖farFieldZeta a z‖ := by
  have hzz : (0 : ℝ) < ‖z‖ := by linarith [hz, ha]
  have hmem : (1 - 4 * a ^ 2 / z ^ 2 : ℂ) ∈ Complex.slitPlane :=
    radicand_mem_slitPlane ha hz
  have hre : 0 < (Complex.sqrt (1 - 4 * a ^ 2 / z ^ 2 : ℂ)).re := by
    have hre_eq : (Complex.sqrt (1 - 4 * a ^ 2 / z ^ 2 : ℂ)).re
        = √((‖(1 - 4 * a ^ 2 / z ^ 2 : ℂ)‖ + (1 - 4 * a ^ 2 / z ^ 2 : ℂ).re) / 2) := by
      have hform := Complex.sqrt_eq_real_add_ite (a := (1 - 4 * a ^ 2 / z ^ 2 : ℂ))
      rw [hform]
      by_cases him : (0 : ℝ) ≤ (1 - 4 * a ^ 2 / z ^ 2 : ℂ).im
      · simp only [him, ite_true]
        simp [Complex.add_re, Complex.mul_re, Complex.ofReal_re,
          Complex.ofReal_im, Complex.I_re, Complex.I_im, Complex.one_re]
      · simp only [him, ite_false]
        simp [Complex.add_re, Complex.mul_re, Complex.ofReal_re,
          Complex.ofReal_im, Complex.I_re, Complex.I_im, Complex.one_re,
          Complex.neg_re]
    rw [hre_eq, Real.sqrt_pos]
    rcases hmem with hpos | hne
    · have hnn := norm_nonneg (1 - 4 * a ^ 2 / z ^ 2 : ℂ)
      linarith [hnn, hpos]
    · have hsq : ‖(1 - 4 * a ^ 2 / z ^ 2 : ℂ)‖ ^ 2
          = (1 - 4 * a ^ 2 / z ^ 2 : ℂ).re * (1 - 4 * a ^ 2 / z ^ 2 : ℂ).re
            + (1 - 4 * a ^ 2 / z ^ 2 : ℂ).im * (1 - 4 * a ^ 2 / z ^ 2 : ℂ).im := by
        rw [Complex.norm_def, Real.sq_sqrt (Complex.normSq_nonneg _),
          Complex.normSq_apply]
      have him2 : (0 : ℝ)
          < (1 - 4 * a ^ 2 / z ^ 2 : ℂ).im * (1 - 4 * a ^ 2 / z ^ 2 : ℂ).im :=
        mul_self_pos.mpr hne
      have hle : (1 - 4 * a ^ 2 / z ^ 2 : ℂ).re ≤ ‖(1 - 4 * a ^ 2 / z ^ 2 : ℂ)‖ :=
        Complex.re_le_norm _
      have hprod : (0 : ℝ)
          < (‖(1 - 4 * a ^ 2 / z ^ 2 : ℂ)‖ + (1 - 4 * a ^ 2 / z ^ 2 : ℂ).re)
            * (‖(1 - 4 * a ^ 2 / z ^ 2 : ℂ)‖ - (1 - 4 * a ^ 2 / z ^ 2 : ℂ).re) := by
        have heq : (‖(1 - 4 * a ^ 2 / z ^ 2 : ℂ)‖ + (1 - 4 * a ^ 2 / z ^ 2 : ℂ).re)
              * (‖(1 - 4 * a ^ 2 / z ^ 2 : ℂ)‖ - (1 - 4 * a ^ 2 / z ^ 2 : ℂ).re)
            = (1 - 4 * a ^ 2 / z ^ 2 : ℂ).im * (1 - 4 * a ^ 2 / z ^ 2 : ℂ).im := by
          linear_combination hsq
        rw [heq]
        exact him2
      have hnn : (0 : ℝ)
          ≤ ‖(1 - 4 * a ^ 2 / z ^ 2 : ℂ)‖ - (1 - 4 * a ^ 2 / z ^ 2 : ℂ).re := by
        linarith [hle]
      have hpos2 : (0 : ℝ)
          < ‖(1 - 4 * a ^ 2 / z ^ 2 : ℂ)‖ + (1 - 4 * a ^ 2 / z ^ 2 : ℂ).re :=
        pos_of_mul_pos_left hprod hnn
      linarith [hpos2]
  have h1s : (1 : ℝ) < ‖(1 + Complex.sqrt (1 - 4 * a ^ 2 / z ^ 2 : ℂ))‖ := by
    have hle : (1 + Complex.sqrt (1 - 4 * a ^ 2 / z ^ 2 : ℂ)).re
        ≤ ‖(1 + Complex.sqrt (1 - 4 * a ^ 2 / z ^ 2 : ℂ))‖ :=
      Complex.re_le_norm _
    have hre1 : (1 + Complex.sqrt (1 - 4 * a ^ 2 / z ^ 2 : ℂ)).re
        = 1 + (Complex.sqrt (1 - 4 * a ^ 2 / z ^ 2 : ℂ)).re := by
      rw [Complex.add_re, Complex.one_re]
    linarith [hle, hre, hre1]
  have hnorm : ‖farFieldZeta (a : ℂ) z‖
      = (‖z‖ / 2) * ‖(1 + Complex.sqrt (1 - 4 * a ^ 2 / z ^ 2 : ℂ))‖ := by
    unfold farFieldZeta
    rw [norm_mul, norm_div, Complex.norm_ofNat]
  rw [hnorm]
  have h2a : (0 : ℝ) < ‖z‖ / 2 := by linarith [hzz]
  have hlt : (‖z‖ / 2) * 1
      < (‖z‖ / 2) * ‖(1 + Complex.sqrt (1 - 4 * a ^ 2 / z ^ 2 : ℂ))‖ :=
    mul_lt_mul_of_pos_left h1s h2a
  rwa [mul_one] at hlt

/-- Route step: for `4 * a ≤ ‖z‖` the conformal denominator is bounded
away from zero, `3 / 4 ≤ ‖1 - a^2 / ζ(z)^2‖`. -/
theorem norm_denominator_ge {a : ℝ} (ha : 0 < a) {z : ℂ}
    (hz : 4 * a ≤ ‖z‖) :
    (3 / 4 : ℝ) ≤ ‖1 - (a : ℂ) ^ 2 / (farFieldZeta a z) ^ 2‖ := by
  have hz2a : 2 * a < ‖z‖ := by linarith [hz, ha]
  have hζ := norm_farFieldZeta_gt_half ha hz2a
  have h2a : 2 * a < ‖farFieldZeta a z‖ := by linarith [hζ, hz]
  have hsq : (2 * a) ^ 2 < ‖farFieldZeta a z‖ ^ 2 :=
    pow_lt_pow_left₀ h2a (by linarith [ha]) (show 2 ≠ 0 by norm_num)
  rw [show (2 * a : ℝ) ^ 2 = 4 * a ^ 2 by ring] at hsq
  have hζpos : (0 : ℝ) < ‖farFieldZeta a z‖ := by linarith [h2a, ha]
  have hζ2pos : (0 : ℝ) < ‖farFieldZeta a z‖ ^ 2 := pow_pos hζpos 2
  have hw : ‖(a : ℂ) ^ 2 / (farFieldZeta a z) ^ 2‖ < 1 / 4 := by
    rw [norm_ratio, div_lt_iff₀ hζ2pos]
    linarith [hsq]
  have h1 := norm_sub_norm_le (1 : ℂ) ((a : ℂ) ^ 2 / (farFieldZeta a z) ^ 2)
  rw [norm_one] at h1
  linarith [h1, hw]

/-- Holomorphy: the physical complex velocity is complex-differentiable on
the whole far-field exterior `2 * a < ‖z‖`. -/
theorem differentiableOn_physicalVelocity {a : ℝ} (ha : 0 < a) (U Γ α : ℝ) :
    DifferentiableOn ℂ (physicalVelocity a U Γ α) {z : ℂ | 2 * a < ‖z‖} := by
  intro z hz
  have hz2a : 2 * a < ‖z‖ := hz
  have hζpos : (0 : ℝ) < ‖farFieldZeta a z‖ := by
    have h := abs_farFieldZeta_gt ha hz2a
    linarith [h, ha]
  have hζ0 : farFieldZeta a z ≠ 0 := norm_pos_iff.mp hζpos
  have hζ2 : (farFieldZeta a z) ^ 2 ≠ 0 := pow_ne_zero 2 hζ0
  have hD0 : (1 - (a : ℂ) ^ 2 / (farFieldZeta a z) ^ 2) ≠ 0 :=
    denominator_ne_zero ha hz2a
  have hζdiff : DifferentiableAt ℂ (farFieldZeta a) z :=
    differentiableAt_farFieldZeta ha hz2a
  have hζ2diff : DifferentiableAt ℂ (fun z : ℂ => (farFieldZeta a z) ^ 2) z :=
    hζdiff.fun_pow 2
  have h2πI0 : (2 * Real.pi * Complex.I : ℂ) ≠ 0 :=
    mul_ne_zero (mul_ne_zero (by norm_num) (by exact_mod_cast Real.pi_ne_zero))
      Complex.I_ne_zero
  have hpow2 : DifferentiableAt ℂ (fun ζ : ℂ => ζ ^ 2) (farFieldZeta a z) :=
    differentiableAt_pow 2
  have hsub : DifferentiableAt ℂ
      (fun ζ : ℂ => Complex.exp (-α * Complex.I) -
        (a : ℂ) ^ 2 * Complex.exp (α * Complex.I) / ζ ^ 2) (farFieldZeta a z) :=
    ((differentiableAt_const ((a : ℂ) ^ 2 * Complex.exp (α * Complex.I))).fun_div
      hpow2 hζ2).const_sub _
  have hfirst : DifferentiableAt ℂ
      (fun ζ : ℂ => (U : ℂ) * (Complex.exp (-α * Complex.I) -
        (a : ℂ) ^ 2 * Complex.exp (α * Complex.I) / ζ ^ 2)) (farFieldZeta a z) :=
    hsub.const_mul _
  have hlin : DifferentiableAt ℂ
      (fun ζ : ℂ => 2 * Real.pi * Complex.I * ζ) (farFieldZeta a z) :=
    differentiableAt_id.const_mul _
  have hsecond : DifferentiableAt ℂ
      (fun ζ : ℂ => (Γ : ℂ) / (2 * Real.pi * Complex.I * ζ)) (farFieldZeta a z) :=
    (differentiableAt_const (Γ : ℂ)).fun_div hlin (mul_ne_zero h2πI0 hζ0)
  have hN : DifferentiableAt ℂ (circleVelocity a U Γ α) (farFieldZeta a z) :=
    hfirst.fun_add hsecond
  have hNcomp : DifferentiableAt ℂ
      (fun z : ℂ => circleVelocity a U Γ α (farFieldZeta a z)) z :=
    hN.comp z hζdiff
  have hD : DifferentiableAt ℂ
      (fun z : ℂ => 1 - (a : ℂ) ^ 2 / (farFieldZeta a z) ^ 2) z :=
    ((differentiableAt_const ((a : ℂ) ^ 2)).fun_div hζ2diff hζ2).const_sub 1
  have hfinal : DifferentiableAt ℂ (physicalVelocity a U Γ α) z :=
    hNcomp.fun_div hD hD0
  exact hfinal.differentiableWithinAt

/-- Explicit far-field remainder: with `R1 = 4 * a` and
`K = 12 * |U| * a^2 + a * |Γ|`,
`‖W(z) - U * exp (-α * I) - Γ / (2 * π * I * z)‖ ≤ K / ‖z‖^2`
for every `z` with `4 * a ≤ ‖z‖`. -/
theorem physicalVelocity_farField_bound {a : ℝ} (ha : 0 < a) (U Γ α : ℝ)
    {z : ℂ} (hz : 4 * a ≤ ‖z‖) :
    ‖physicalVelocity a U Γ α z - (U : ℂ) * Complex.exp (-α * Complex.I) -
        (Γ : ℂ) / (2 * Real.pi * Complex.I * z)‖ ≤
      (12 * |U| * a ^ 2 + a * |Γ|) / ‖z‖ ^ 2 := by
  have hz2a : 2 * a < ‖z‖ := by linarith [hz, ha]
  have hzz : (0 : ℝ) < ‖z‖ := by linarith [hz2a, ha]
  have hz0 : z ≠ 0 := norm_pos_iff.mp hzz
  have hzz2pos : (0 : ℝ) < ‖z‖ ^ 2 := pow_pos hzz 2
  have hζ := norm_farFieldZeta_gt_half ha hz2a
  have hζpos : (0 : ℝ) < ‖farFieldZeta a z‖ := by linarith [hζ, hzz]
  have hζ0 : farFieldZeta a z ≠ 0 := norm_pos_iff.mp hζpos
  have hζ2 : (farFieldZeta a z) ^ 2 ≠ 0 := pow_ne_zero 2 hζ0
  have hζ2pos : (0 : ℝ) < ‖farFieldZeta a z‖ ^ 2 := pow_pos hζpos 2
  have hDge : (3 / 4 : ℝ) ≤ ‖1 - (a : ℂ) ^ 2 / (farFieldZeta a z) ^ 2‖ :=
    norm_denominator_ge ha hz
  have hD0 : (1 - (a : ℂ) ^ 2 / (farFieldZeta a z) ^ 2) ≠ 0 := by
    intro hcon
    rw [hcon, norm_zero] at hDge
    norm_num at hDge
  have hDpos : (0 : ℝ) < ‖1 - (a : ℂ) ^ 2 / (farFieldZeta a z) ^ 2‖ := by
    linarith [hDge]
  have har0 : a ≠ 0 := ne_of_gt ha
  have hP0 : (2 * Real.pi * Complex.I : ℂ) ≠ 0 :=
    mul_ne_zero (mul_ne_zero (by norm_num) (by exact_mod_cast Real.pi_ne_zero))
      Complex.I_ne_zero
  have hPζ0 : ((2 * Real.pi * Complex.I : ℂ) * farFieldZeta a z) ≠ 0 :=
    mul_ne_zero hP0 hζ0
  have hζD0 : (farFieldZeta a z) * (1 - (a : ℂ) ^ 2 / (farFieldZeta a z) ^ 2) ≠ 0 :=
    mul_ne_zero hζ0 hD0
  have hDen0 : (farFieldZeta a z) ^ 2 * (1 - (a : ℂ) ^ 2 / (farFieldZeta a z) ^ 2) * z ≠ 0 :=
    mul_ne_zero (mul_ne_zero hζ2 hD0) hz0
  have hζ2D0 : (farFieldZeta a z) ^ 2 * (1 - (a : ℂ) ^ 2 / (farFieldZeta a z) ^ 2) ≠ 0 :=
    mul_ne_zero hζ2 hD0
  have hJ2 : z * farFieldZeta a z = (farFieldZeta a z) ^ 2 + (a : ℂ) ^ 2 := by
    have hJ := joukowski_farFieldZeta ha hz2a
    unfold joukowski at hJ
    have hmul := congrArg (fun w : ℂ => w * farFieldZeta a z) hJ
    rw [add_mul, div_mul_cancel₀ _ hζ0] at hmul
    linear_combination -hmul
  have hD2 : (1 - (a : ℂ) ^ 2 / (farFieldZeta a z) ^ 2) * (farFieldZeta a z) ^ 2
      = (farFieldZeta a z) ^ 2 - (a : ℂ) ^ 2 := by
    rw [sub_mul, one_mul, div_mul_cancel₀ _ hζ2]
  have hζ2a2 : (farFieldZeta a z) ^ 2 - (a : ℂ) ^ 2 ≠ 0 := by
    have h := mul_ne_zero hD0 hζ2
    rw [hD2] at h
    exact h
  have hBz : ((Γ : ℂ) / (2 * Real.pi * Complex.I)) / z
      = (Γ : ℂ) / (2 * Real.pi * Complex.I * z) := by
    rw [div_div]
  have hE1 : ‖Complex.exp (-α * Complex.I)‖ = 1 := by
    rw [Complex.norm_exp]
    have hre : (-α * Complex.I : ℂ).re = 0 := by simp
    rw [hre, Real.exp_zero]
  have hE2 : ‖Complex.exp (α * Complex.I)‖ = 1 := by
    rw [Complex.norm_exp]
    have hre : (α * Complex.I : ℂ).re = 0 := by simp
    rw [hre, Real.exp_zero]
  have h2pi : ‖(2 * Real.pi * Complex.I : ℂ)‖ = 2 * Real.pi := by
    rw [norm_mul, norm_mul, Complex.norm_I, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos Real.pi_pos, show ‖(2 : ℂ)‖ = 2 by simp, mul_one]
  have hBnorm : ‖(Γ : ℂ) / (2 * Real.pi * Complex.I)‖ = |Γ| / (2 * Real.pi) := by
    rw [norm_div, Complex.norm_real, Real.norm_eq_abs, h2pi]
  have hBalg : ((Γ : ℂ) / (2 * Real.pi * Complex.I))
        / ((farFieldZeta a z) * (1 - (a : ℂ) ^ 2 / (farFieldZeta a z) ^ 2))
      - ((Γ : ℂ) / (2 * Real.pi * Complex.I)) / z
      = 2 * (a : ℂ) ^ 2 * ((Γ : ℂ) / (2 * Real.pi * Complex.I))
        / ((farFieldZeta a z) ^ 2 * (1 - (a : ℂ) ^ 2 / (farFieldZeta a z) ^ 2) * z) := by
    have e1 : ((Γ : ℂ) / (2 * Real.pi * Complex.I))
          / ((farFieldZeta a z) * (1 - (a : ℂ) ^ 2 / (farFieldZeta a z) ^ 2))
          * ((farFieldZeta a z) ^ 2 * (1 - (a : ℂ) ^ 2 / (farFieldZeta a z) ^ 2) * z)
        = ((Γ : ℂ) / (2 * Real.pi * Complex.I)) * (farFieldZeta a z) * z := by
      field_simp
    have e2 : (((Γ : ℂ) / (2 * Real.pi * Complex.I)) / z)
          * ((farFieldZeta a z) ^ 2 * (1 - (a : ℂ) ^ 2 / (farFieldZeta a z) ^ 2) * z)
        = ((Γ : ℂ) / (2 * Real.pi * Complex.I))
          * ((farFieldZeta a z) ^ 2 * (1 - (a : ℂ) ^ 2 / (farFieldZeta a z) ^ 2)) := by
      field_simp
    have hkey : (farFieldZeta a z) * z
          - (farFieldZeta a z) ^ 2 * (1 - (a : ℂ) ^ 2 / (farFieldZeta a z) ^ 2)
        = 2 * (a : ℂ) ^ 2 := by
      linear_combination hJ2 - hD2
    have hexpand : ((Γ : ℂ) / (2 * Real.pi * Complex.I)) * (farFieldZeta a z) * z
          - ((Γ : ℂ) / (2 * Real.pi * Complex.I))
            * ((farFieldZeta a z) ^ 2 * (1 - (a : ℂ) ^ 2 / (farFieldZeta a z) ^ 2))
        = ((Γ : ℂ) / (2 * Real.pi * Complex.I))
          * ((farFieldZeta a z) * z
            - (farFieldZeta a z) ^ 2 * (1 - (a : ℂ) ^ 2 / (farFieldZeta a z) ^ 2)) := by
      ring
    rw [eq_div_iff hDen0, sub_mul, e1, e2, hexpand, hkey]
    ring
  have hdec : circleVelocity a U Γ α (farFieldZeta a z)
        / (1 - (a : ℂ) ^ 2 / (farFieldZeta a z) ^ 2)
        - (U : ℂ) * Complex.exp (-α * Complex.I)
      = ((Γ : ℂ) / (2 * Real.pi * Complex.I))
          / ((farFieldZeta a z) * (1 - (a : ℂ) ^ 2 / (farFieldZeta a z) ^ 2))
        + (((U : ℂ) * Complex.exp (-α * Complex.I) * (a : ℂ) ^ 2
          - (U : ℂ) * (a : ℂ) ^ 2 * Complex.exp (α * Complex.I))
          / ((farFieldZeta a z) ^ 2 * (1 - (a : ℂ) ^ 2 / (farFieldZeta a z) ^ 2))) := by
    unfold circleVelocity
    field_simp
    ring
  have hW : physicalVelocity a U Γ α z - (U : ℂ) * Complex.exp (-α * Complex.I)
        - (Γ : ℂ) / (2 * Real.pi * Complex.I * z)
      = 2 * (a : ℂ) ^ 2 * ((Γ : ℂ) / (2 * Real.pi * Complex.I))
          / ((farFieldZeta a z) ^ 2 * (1 - (a : ℂ) ^ 2 / (farFieldZeta a z) ^ 2) * z)
        + (((U : ℂ) * Complex.exp (-α * Complex.I) * (a : ℂ) ^ 2
          - (U : ℂ) * (a : ℂ) ^ 2 * Complex.exp (α * Complex.I))
          / ((farFieldZeta a z) ^ 2 * (1 - (a : ℂ) ^ 2 / (farFieldZeta a z) ^ 2))) := by
    unfold physicalVelocity
    rw [hdec, ← hBz]
    linear_combination hBalg
  rw [hW]
  have hζ2gt : ‖z‖ ^ 2 / 4 < ‖farFieldZeta a z‖ ^ 2 := by
    have h2 : (‖z‖ / 2) ^ 2 < ‖farFieldZeta a z‖ ^ 2 :=
      pow_lt_pow_left₀ hζ (div_nonneg (norm_nonneg _) (by norm_num))
        (show 2 ≠ 0 by norm_num)
    rw [show (‖z‖ / 2 : ℝ) ^ 2 = ‖z‖ ^ 2 / 4 by ring] at h2
    exact h2
  have hT2norm : ‖(((U : ℂ) * Complex.exp (-α * Complex.I) * (a : ℂ) ^ 2
        - (U : ℂ) * (a : ℂ) ^ 2 * Complex.exp (α * Complex.I))
        / ((farFieldZeta a z) ^ 2 * (1 - (a : ℂ) ^ 2 / (farFieldZeta a z) ^ 2)))‖
      = ‖(U : ℂ) * Complex.exp (-α * Complex.I) * (a : ℂ) ^ 2
        - (U : ℂ) * (a : ℂ) ^ 2 * Complex.exp (α * Complex.I)‖
        / (‖farFieldZeta a z‖ ^ 2 * ‖1 - (a : ℂ) ^ 2 / (farFieldZeta a z) ^ 2‖) := by
    rw [norm_div, norm_mul, norm_pow]
  have hA2 : ‖(U : ℂ) * Complex.exp (-α * Complex.I) * (a : ℂ) ^ 2‖
      = |U| * a ^ 2 := by
    rw [norm_mul, norm_mul, Complex.norm_real, Real.norm_eq_abs, hE1,
      norm_pow, Complex.norm_real, Real.norm_eq_abs, abs_of_pos ha, mul_one]
  have hCnorm : ‖(U : ℂ) * (a : ℂ) ^ 2 * Complex.exp (α * Complex.I)‖
      = |U| * a ^ 2 := by
    rw [norm_mul, norm_mul, Complex.norm_real, Real.norm_eq_abs, hE2,
      norm_pow, Complex.norm_real, Real.norm_eq_abs, abs_of_pos ha, mul_one]
  have hnum2 : ‖(U : ℂ) * Complex.exp (-α * Complex.I) * (a : ℂ) ^ 2
      - (U : ℂ) * (a : ℂ) ^ 2 * Complex.exp (α * Complex.I)‖
      ≤ 2 * |U| * a ^ 2 := by
    calc ‖(U : ℂ) * Complex.exp (-α * Complex.I) * (a : ℂ) ^ 2
          - (U : ℂ) * (a : ℂ) ^ 2 * Complex.exp (α * Complex.I)‖
          ≤ ‖(U : ℂ) * Complex.exp (-α * Complex.I) * (a : ℂ) ^ 2‖
            + ‖(U : ℂ) * (a : ℂ) ^ 2 * Complex.exp (α * Complex.I)‖ :=
            norm_sub_le _ _
      _ = |U| * a ^ 2 + |U| * a ^ 2 := by rw [hA2, hCnorm]
      _ = 2 * |U| * a ^ 2 := by ring
  have hden2 : (‖z‖ ^ 2 / 4) * (3 / 4)
      ≤ ‖farFieldZeta a z‖ ^ 2 * ‖1 - (a : ℂ) ^ 2 / (farFieldZeta a z) ^ 2‖ :=
    mul_le_mul (le_of_lt hζ2gt) hDge (by norm_num) (by positivity)
  have hden2pos : (0 : ℝ)
      < ‖farFieldZeta a z‖ ^ 2 * ‖1 - (a : ℂ) ^ 2 / (farFieldZeta a z) ^ 2‖ :=
    mul_pos hζ2pos hDpos
  have hdd2pos : (0 : ℝ) < (‖z‖ ^ 2 / 4) * (3 / 4) :=
    mul_pos (div_pos hzz2pos (by norm_num)) (by norm_num)
  have hY2nonneg : (0 : ℝ) ≤ 2 * |U| * a ^ 2 := by positivity
  have hT2 : ‖(((U : ℂ) * Complex.exp (-α * Complex.I) * (a : ℂ) ^ 2
        - (U : ℂ) * (a : ℂ) ^ 2 * Complex.exp (α * Complex.I))
        / ((farFieldZeta a z) ^ 2 * (1 - (a : ℂ) ^ 2 / (farFieldZeta a z) ^ 2)))‖
      ≤ 12 * |U| * a ^ 2 / ‖z‖ ^ 2 := by
    rw [hT2norm]
    have hmid : ‖(U : ℂ) * Complex.exp (-α * Complex.I) * (a : ℂ) ^ 2
          - (U : ℂ) * (a : ℂ) ^ 2 * Complex.exp (α * Complex.I)‖
          / (‖farFieldZeta a z‖ ^ 2 * ‖1 - (a : ℂ) ^ 2 / (farFieldZeta a z) ^ 2‖)
        ≤ (2 * |U| * a ^ 2) / ((‖z‖ ^ 2 / 4) * (3 / 4)) := by
      gcongr
    have hX2 : (0 : ℝ) ≤ |U| * a ^ 2 / ‖z‖ ^ 2 :=
      div_nonneg (mul_nonneg (abs_nonneg _) (by positivity)) (le_of_lt hzz2pos)
    have heq1 : (2 * |U| * a ^ 2) / ((‖z‖ ^ 2 / 4) * (3 / 4))
        = (32 / 3) * (|U| * a ^ 2 / ‖z‖ ^ 2) := by
      have hzz20 : ‖z‖ ^ 2 ≠ 0 := ne_of_gt hzz2pos
      have h4 : (4 : ℝ) ≠ 0 := by norm_num
      have h3 : (3 : ℝ) ≠ 0 := by norm_num
      have h34 : ((3 : ℝ) / 4) ≠ 0 := by norm_num
      have hS4 : (‖z‖ ^ 2 / 4 : ℝ) ≠ 0 := div_ne_zero hzz20 h4
      have hprod : ((‖z‖ ^ 2 / 4) * (3 / 4) : ℝ) ≠ 0 := mul_ne_zero hS4 h34
      field_simp
      ring
    have heq2 : 12 * |U| * a ^ 2 / ‖z‖ ^ 2 = 12 * (|U| * a ^ 2 / ‖z‖ ^ 2) := by
      ring
    rw [heq2]
    refine le_trans hmid ?_
    rw [heq1]
    exact mul_le_mul_of_nonneg_right (by norm_num) hX2
  have hT1norm : ‖2 * (a : ℂ) ^ 2 * ((Γ : ℂ) / (2 * Real.pi * Complex.I))
        / ((farFieldZeta a z) ^ 2 * (1 - (a : ℂ) ^ 2 / (farFieldZeta a z) ^ 2) * z)‖
      = 2 * a ^ 2 * (|Γ| / (2 * Real.pi))
        / (‖farFieldZeta a z‖ ^ 2 * ‖1 - (a : ℂ) ^ 2 / (farFieldZeta a z) ^ 2‖ * ‖z‖) := by
    have hnum : ‖2 * (a : ℂ) ^ 2 * ((Γ : ℂ) / (2 * Real.pi * Complex.I))‖
        = 2 * a ^ 2 * (|Γ| / (2 * Real.pi)) := by
      rw [norm_mul, norm_mul, norm_pow, Complex.norm_real, Real.norm_eq_abs,
        abs_of_pos ha, hBnorm, show ‖(2 : ℂ)‖ = 2 by simp]
    rw [norm_div, hnum, norm_mul, norm_mul, norm_pow]
  have hden1 : ((‖z‖ ^ 2 / 4) * (3 / 4)) * (4 * a)
      ≤ (‖farFieldZeta a z‖ ^ 2 * ‖1 - (a : ℂ) ^ 2 / (farFieldZeta a z) ^ 2‖) * ‖z‖ :=
    mul_le_mul hden2 hz (by positivity) (by positivity)
  have hden1pos : (0 : ℝ)
      < (‖farFieldZeta a z‖ ^ 2 * ‖1 - (a : ℂ) ^ 2 / (farFieldZeta a z) ^ 2‖) * ‖z‖ :=
    mul_pos hden2pos hzz
  have hdd1pos : (0 : ℝ) < ((‖z‖ ^ 2 / 4) * (3 / 4)) * (4 * a) :=
    mul_pos hdd2pos (by linarith [ha])
  have h2pipos : (0 : ℝ) < 2 * Real.pi := mul_pos (by norm_num) Real.pi_pos
  have hY1nonneg : (0 : ℝ) ≤ 2 * a ^ 2 * (|Γ| / (2 * Real.pi)) :=
    mul_nonneg (by positivity) (div_nonneg (abs_nonneg _) (le_of_lt h2pipos))
  have hT1 : ‖2 * (a : ℂ) ^ 2 * ((Γ : ℂ) / (2 * Real.pi * Complex.I))
        / ((farFieldZeta a z) ^ 2 * (1 - (a : ℂ) ^ 2 / (farFieldZeta a z) ^ 2) * z)‖
      ≤ a * |Γ| / ‖z‖ ^ 2 := by
    rw [hT1norm]
    have hmid : 2 * a ^ 2 * (|Γ| / (2 * Real.pi))
          / ((‖farFieldZeta a z‖ ^ 2 * ‖1 - (a : ℂ) ^ 2 / (farFieldZeta a z) ^ 2‖) * ‖z‖)
        ≤ 2 * a ^ 2 * (|Γ| / (2 * Real.pi)) / (((‖z‖ ^ 2 / 4) * (3 / 4)) * (4 * a)) := by
      gcongr
    have hX1 : (0 : ℝ) ≤ a * |Γ| / ‖z‖ ^ 2 :=
      div_nonneg (mul_nonneg (le_of_lt ha) (abs_nonneg _)) (le_of_lt hzz2pos)
    have hfrac : (4 : ℝ) / (3 * Real.pi) ≤ 1 := by
      have h3p : (0 : ℝ) < 3 * Real.pi := mul_pos (by norm_num) Real.pi_pos
      rw [div_le_iff₀ h3p]
      linarith [Real.two_le_pi]
    have heq1 : 2 * a ^ 2 * (|Γ| / (2 * Real.pi)) / (((‖z‖ ^ 2 / 4) * (3 / 4)) * (4 * a))
        = (4 / (3 * Real.pi)) * (a * |Γ| / ‖z‖ ^ 2) := by
      have hzz20 : ‖z‖ ^ 2 ≠ 0 := ne_of_gt hzz2pos
      have hpi0 : Real.pi ≠ 0 := Real.pi_ne_zero
      have h2 : (2 : ℝ) ≠ 0 := by norm_num
      have h3 : (3 : ℝ) ≠ 0 := by norm_num
      have h4 : (4 : ℝ) ≠ 0 := by norm_num
      have h34 : ((3 : ℝ) / 4) ≠ 0 := by norm_num
      have h2pi0 : ((2 : ℝ) * Real.pi) ≠ 0 := mul_ne_zero h2 hpi0
      have h3pi0 : ((3 : ℝ) * Real.pi) ≠ 0 := mul_ne_zero h3 hpi0
      have hS4 : (‖z‖ ^ 2 / 4 : ℝ) ≠ 0 := div_ne_zero hzz20 h4
      have hprod : ((‖z‖ ^ 2 / 4) * (3 / 4) : ℝ) ≠ 0 := mul_ne_zero hS4 h34
      have h4a0 : ((4 : ℝ) * a) ≠ 0 := mul_ne_zero h4 har0
      have hprod2 : (((‖z‖ ^ 2 / 4) * (3 / 4)) * (4 * a) : ℝ) ≠ 0 :=
        mul_ne_zero hprod h4a0
      field_simp
    refine le_trans hmid ?_
    rw [heq1]
    have hle := mul_le_mul_of_nonneg_right hfrac hX1
    rw [one_mul] at hle
    exact hle
  have hsum : a * |Γ| / ‖z‖ ^ 2 + 12 * |U| * a ^ 2 / ‖z‖ ^ 2
      = (12 * |U| * a ^ 2 + a * |Γ|) / ‖z‖ ^ 2 := by
    ring
  exact le_trans (norm_add_le _ _) (le_trans (add_le_add hT1 hT2) hsum.le)

/-- Existential packaging of the leaf: holomorphy on `2 * a < ‖z‖` and
constants `R1 > 2 * a`, `K ≥ 0` with the `K / ‖z‖^2` remainder bound for
`R1 ≤ ‖z‖`. -/
theorem exists_physicalVelocity_farField {a : ℝ} (ha : 0 < a) (U Γ α : ℝ) :
    DifferentiableOn ℂ (physicalVelocity a U Γ α) {z : ℂ | 2 * a < ‖z‖} ∧
      ∃ R1 K : ℝ, 2 * a < R1 ∧ 0 ≤ K ∧ ∀ z : ℂ, R1 ≤ ‖z‖ →
        ‖physicalVelocity a U Γ α z - (U : ℂ) * Complex.exp (-α * Complex.I) -
            (Γ : ℂ) / (2 * Real.pi * Complex.I * z)‖ ≤ K / ‖z‖ ^ 2 := by
  refine ⟨differentiableOn_physicalVelocity ha U Γ α, 4 * a,
    12 * |U| * a ^ 2 + a * |Γ|, by linarith [ha], by positivity, ?_⟩
  intro z hz
  exact physicalVelocity_farField_bound ha U Γ α hz

/-! ## Fixtures -/

/-- Nonzero-circulation fixture: `a = 1`, `U = 1`, `Γ = 1`, `α = 0` has a
nonzero `1 / z` tail coefficient and a finite bound with `R1 = 4`, `K = 13`. -/
theorem fixture_nonzero_tail :
    (1 : ℂ) / (2 * Real.pi * Complex.I) ≠ 0 ∧
      ∀ z : ℂ, 4 ≤ ‖z‖ →
        ‖physicalVelocity 1 1 1 0 z - 1 - 1 / (2 * Real.pi * Complex.I * z)‖ ≤
          13 / ‖z‖ ^ 2 := by
  constructor
  · exact div_ne_zero one_ne_zero
      (mul_ne_zero (mul_ne_zero (by norm_num) (by exact_mod_cast Real.pi_ne_zero))
        Complex.I_ne_zero)
  · intro z hz
    have h1 : (0 : ℝ) < 1 := by norm_num
    have h2 : 4 * 1 ≤ ‖z‖ := by rwa [mul_one]
    have h := physicalVelocity_farField_bound h1 1 1 0 h2
    have hU : ((1 : ℝ) : ℂ) * Complex.exp (-(0 : ℝ) * Complex.I) = 1 := by
      rw [Complex.ofReal_one, Complex.ofReal_zero, neg_zero, zero_mul,
        Complex.exp_zero, one_mul]
    have hK : (12 * |(1 : ℝ)| * (1 : ℝ) ^ 2 + 1 * |(1 : ℝ)|) = 13 := by norm_num
    rw [hU, hK, Complex.ofReal_one] at h
    exact h

/-- Invalid-point fixture: the leading edge `z = -2a` maps to `ζ = -a`, where
the conformal denominator vanishes, and it lies outside the bound region. -/
theorem fixture_leadingEdge {a : ℝ} (ha : 0 < a) :
    farFieldZeta a (-(2 * a : ℂ)) = -(a : ℂ) ∧
      1 - (a : ℂ) ^ 2 / (farFieldZeta a (-(2 * a : ℂ))) ^ 2 = 0 ∧
      ¬ (4 * a ≤ ‖(-(2 * a : ℂ))‖) := by
  have ha0 : (a : ℂ) ≠ 0 := by exact_mod_cast ne_of_gt ha
  have hz2 : (-(2 * a : ℂ)) ^ 2 = 4 * (a : ℂ) ^ 2 := by ring
  have h4a : (4 : ℂ) * (a : ℂ) ^ 2 ≠ 0 :=
    mul_ne_zero (by norm_num) (pow_ne_zero 2 ha0)
  have hrad : (1 - 4 * (a : ℂ) ^ 2 / (-(2 * a : ℂ)) ^ 2 : ℂ) = 0 := by
    rw [hz2, div_self h4a, sub_self]
  have hζ : farFieldZeta a (-(2 * a : ℂ)) = -(a : ℂ) := by
    unfold farFieldZeta
    rw [hrad, Complex.sqrt_zero, add_zero, mul_one]
    ring
  have hD : (1 - (a : ℂ) ^ 2 / (farFieldZeta a (-(2 * a : ℂ))) ^ 2 : ℂ) = 0 := by
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

end JoukowskiBranch

/-! ## B. Blasius force from a far-field expansion -/

namespace BlasiusForce

/-- Blasius force per unit span (as `Fx - I * Fy`) for the complex
velocity `W` on the circle of radius `R` about `0`, at density
`ρ`: `(I * ρ / 2) * ∮ W^2`. -/
noncomputable def blasiusForce (ρ : ℝ) (W : ℂ → ℂ) (R : ℝ) : ℂ :=
  (Complex.I * ρ / 2) * ∮ z in C(0, R), (W z) ^ 2

/-- Kutta-Joukowski from a far-field expansion: let `W` be
holomorphic on the exterior `R0 < ‖z‖`, with
`W z = A + B / z + e z` for `‖z‖ ≥ R1`, where
`A = U * exp (-α * I)`, `B = Γ / (2 * π * I)`, and the remainder
satisfies `‖e z‖ ≤ K / ‖z‖^2` there. Then at every radius
`R > R0`, the Blasius force is `I * ρ * U * Γ * exp (-α * I)`. -/
theorem blasiusForce_eq {ρ U Γ α R0 R1 K : ℝ} (hρ : 0 < ρ)
    (hU : 0 < U) (hR0 : 0 < R0) (hR1 : R0 < R1)
    {W e : ℂ → ℂ}
    (hW : DifferentiableOn ℂ W {z : ℂ | R0 < ‖z‖})
    (hdecomp : ∀ z : ℂ, R1 ≤ ‖z‖ →
      W z = (U : ℂ) * Complex.exp (-α * Complex.I) +
        ((Γ : ℂ) / (2 * Real.pi * Complex.I)) / z + e z)
    (he : ∀ z : ℂ, R1 ≤ ‖z‖ → DifferentiableAt ℂ e z)
    (hbound : ∀ z : ℂ, R1 ≤ ‖z‖ → ‖e z‖ ≤ K / ‖z‖ ^ 2)
    {R : ℝ} (hR : R0 < R) :
    blasiusForce ρ W R =
      Complex.I * ρ * U * Γ * Complex.exp (-α * Complex.I) := by
  have hρpos : 0 < ρ := hρ
  have hUpos : 0 < U := hU
  have hR1pos : 0 < R1 := lt_trans hR0 hR1
  have hRpos : 0 < R := lt_trans hR0 hR
  have hK : 0 ≤ K := by
    have hnorm : ‖(R1 : ℂ)‖ = R1 := by simp [abs_of_pos hR1pos]
    have hz0 : R1 ≤ ‖(R1 : ℂ)‖ := by rw [hnorm]
    have h := hbound _ hz0
    have hnn : (0 : ℝ) ≤ K / ‖(R1 : ℂ)‖ ^ 2 := le_trans (norm_nonneg _) h
    have hden : (0 : ℝ) < ‖(R1 : ℂ)‖ ^ 2 := by
      rw [hnorm]
      positivity
    have hmul := mul_nonneg hnn hden.le
    rwa [div_mul_cancel₀ _ hden.ne'] at hmul
  have hW2 : DifferentiableOn ℂ (fun z => (W z) ^ 2) {z : ℂ | R0 < ‖z‖} := hW.pow 2
  have hOpen : IsOpen {z : ℂ | R0 < ‖z‖} := isOpen_lt continuous_const continuous_norm
  have hEq : ∀ R2 : ℝ, R ≤ R2 →
      (∮ z in C((0 : ℂ), R2), (W z) ^ 2) = (∮ z in C((0 : ℂ), R), (W z) ^ 2) := by
    intro R2 hle
    apply Complex.circleIntegral_eq_of_differentiable_on_annulus_off_countable hRpos hle
      Set.countable_empty
    · apply hW2.continuousOn.mono
      intro z hz
      simp only [Set.mem_sdiff, Metric.mem_closedBall, Metric.mem_ball, dist_eq_norm,
        sub_zero] at hz
      change R0 < ‖z‖
      have hRle : R ≤ ‖z‖ := not_lt.mp hz.2
      exact lt_of_lt_of_le hR hRle
    · intro z hz
      simp only [Set.mem_sdiff, Metric.mem_ball, Metric.mem_closedBall, dist_eq_norm,
        sub_zero] at hz
      have hRlt : R < ‖z‖ := not_le.mp hz.1.2
      have hmem : z ∈ {z : ℂ | R0 < ‖z‖} := by exact lt_trans hR hRlt
      exact hW2.differentiableAt (hOpen.mem_nhds hmem)
  set A : ℂ := (U : ℂ) * Complex.exp (-α * Complex.I) with hA
  set B : ℂ := ((Γ : ℂ) / (2 * Real.pi * Complex.I)) with hB
  set L : ℂ := (2 * A * B) * (2 * Real.pi * Complex.I) with hL
  have hDecompInt : ∀ R2 : ℝ, R1 ≤ R2 →
      (∮ z in C((0 : ℂ), R2), (W z) ^ 2)
        = L + (∮ z in C((0 : ℂ), R2), (B / z + e z) ^ 2 + 2 * A * e z) := by
    intro R2 hle
    have hR2pos : 0 < R2 := lt_of_lt_of_le hR1pos hle
    have hR2le : 0 ≤ R2 := le_of_lt hR2pos
    have hSph : ∀ z : ℂ, z ∈ Metric.sphere (0 : ℂ) R2 → ‖z‖ = R2 := by
      intro z hz
      simpa [Metric.mem_sphere, dist_eq_norm, sub_zero] using hz
    have hzne : ∀ z : ℂ, z ∈ Metric.sphere (0 : ℂ) R2 → z ≠ 0 := by
      intro z hz hzero
      have hnorm := hSph z hz
      rw [hzero, norm_zero] at hnorm
      exact (ne_of_gt hR2pos) hnorm.symm
    have heCont : ContinuousOn e (Metric.sphere (0 : ℂ) R2) := by
      apply continuousOn_of_forall_continuousAt
      intro z hz
      have hle' : R1 ≤ ‖z‖ := by rw [hSph z hz]; exact hle
      exact (he z hle').continuousAt
    have hBzCont : ContinuousOn (fun z : ℂ => B / z) (Metric.sphere (0 : ℂ) R2) :=
      continuousOn_const.div continuousOn_id (fun z hz => hzne z hz)
    have hW2sph : ContinuousOn (fun z => (W z) ^ 2) (Metric.sphere (0 : ℂ) R2) := by
      apply hW2.continuousOn.mono
      intro z hz
      change R0 < ‖z‖
      rw [hSph z hz]
      exact lt_of_lt_of_le hR1 hle
    have hInt0 : CircleIntegrable (fun _ : ℂ => A ^ 2) 0 R2 :=
      ContinuousOn.circleIntegrable hR2le continuousOn_const
    have hInt1 : CircleIntegrable (fun z : ℂ => (2 * A * B) / z) 0 R2 :=
      ContinuousOn.circleIntegrable hR2le
        (continuousOn_const.div continuousOn_id (fun z hz => hzne z hz))
    have hSqCont : ContinuousOn (fun z : ℂ => (B / z + e z) ^ 2)
        (Metric.sphere (0 : ℂ) R2) :=
      (hBzCont.add heCont).pow 2
    have hfrCont : ContinuousOn (fun z : ℂ => (B / z + e z) ^ 2 + 2 * A * e z)
        (Metric.sphere (0 : ℂ) R2) :=
      hSqCont.add (continuousOn_const.mul heCont)
    have hIntr : CircleIntegrable
        (fun z : ℂ => (B / z + e z) ^ 2 + 2 * A * e z) 0 R2 :=
      ContinuousOn.circleIntegrable hR2le hfrCont
    have hInt01 : CircleIntegrable (fun z : ℂ => A ^ 2 + (2 * A * B) / z) 0 R2 :=
      hInt0.add hInt1
    have hWzAB : ∀ z : ℂ, R1 ≤ ‖z‖ → W z = A + B / z + e z := fun z hz => hdecomp z hz
    have hExpand : ∀ z ∈ Metric.sphere (0 : ℂ) R2,
        (W z) ^ 2 = A ^ 2 + (2 * A * B) / z + ((B / z + e z) ^ 2 + 2 * A * e z) := by
      intro z hz
      have hle' : R1 ≤ ‖z‖ := by rw [hSph z hz]; exact hle
      have hWz := hWzAB z hle'
      rw [hWz]
      ring
    have hIntEq : (∮ z in C((0 : ℂ), R2), (W z) ^ 2)
        = (∮ z in C((0 : ℂ), R2), A ^ 2)
          + (∮ z in C((0 : ℂ), R2), (2 * A * B) / z)
          + (∮ z in C((0 : ℂ), R2), (B / z + e z) ^ 2 + 2 * A * e z) := by
      have hcongr : Set.EqOn (fun z => (W z) ^ 2)
          (fun z => A ^ 2 + (2 * A * B) / z + ((B / z + e z) ^ 2 + 2 * A * e z))
          (Metric.sphere 0 R2) := hExpand
      rw [circleIntegral.integral_congr hR2le hcongr]
      rw [circleIntegral.integral_add hInt01 hIntr]
      rw [circleIntegral.integral_add hInt0 hInt1]
    have hInt0eq : (∮ z in C((0 : ℂ), R2), A ^ 2) = 0 := by
      have hcongr0 : Set.EqOn (fun _ : ℂ => A ^ 2)
          (fun z => A ^ 2 * (z - 0) ^ (0 : ℤ)) (Metric.sphere 0 R2) := by
        intro z _
        simp
      rw [circleIntegral.integral_congr hR2le hcongr0, circleIntegral.integral_const_mul,
        circleIntegral.integral_sub_zpow_of_ne (by decide : (0 : ℤ) ≠ -1) _ _ _, mul_zero]
    have hmem : (0 : ℂ) ∈ Metric.ball 0 R2 := Metric.mem_ball_self hR2pos
    have hInv : (∮ z in C((0 : ℂ), R2), (z - 0)⁻¹) = 2 * Real.pi * Complex.I :=
      circleIntegral.integral_sub_inv_of_mem_ball hmem
    have hInt1eq : (∮ z in C((0 : ℂ), R2), (2 * A * B) / z)
        = (2 * A * B) * (2 * Real.pi * Complex.I) := by
      have hcongr1 : Set.EqOn (fun z : ℂ => (2 * A * B) / z)
          (fun z => (2 * A * B) * (z - 0)⁻¹) (Metric.sphere 0 R2) := by
        intro z _
        simp [div_eq_mul_inv, sub_zero]
      rw [circleIntegral.integral_congr hR2le hcongr1, circleIntegral.integral_const_mul, hInv]
    rw [hIntEq, hInt0eq, hInt1eq, hL, zero_add]
  set C0 : ℝ := (‖B‖ + K) ^ 2 + 2 * ‖A‖ * K with hC0
  have hRemBound : ∀ R2 : ℝ, R1 ≤ R2 → 1 ≤ R2 →
      ∀ z ∈ Metric.sphere (0 : ℂ) R2,
        ‖(B / z + e z) ^ 2 + 2 * A * e z‖ ≤ C0 / R2 ^ 2 := by
    intro R2 hle hge1 z hz
    have hR2pos : 0 < R2 := lt_of_lt_of_le hR1pos hle
    have hn : ‖z‖ = R2 := by
      simpa [Metric.mem_sphere, dist_eq_norm, sub_zero] using hz
    have hle' : R1 ≤ ‖z‖ := by rw [hn]; exact hle
    have hez : ‖e z‖ ≤ K / R2 ^ 2 := by
      have h := hbound z hle'
      rwa [hn] at h
    have hBz : ‖B / z‖ = ‖B‖ / R2 := by rw [norm_div, hn]
    have hR2pow : R2 ≤ R2 ^ 2 := le_self_pow₀ hge1 two_ne_zero
    have hKdiv : K / R2 ^ 2 ≤ K / R2 := by
      have h1 : (1 : ℝ) / R2 ^ 2 ≤ 1 / R2 :=
        one_div_le_one_div_of_le hR2pos hR2pow
      rw [div_eq_mul_one_div K (R2 ^ 2), div_eq_mul_one_div K R2]
      exact mul_le_mul_of_nonneg_left h1 hK
    have hSum : ‖B / z‖ + ‖e z‖ ≤ (‖B‖ + K) / R2 := by
      calc ‖B / z‖ + ‖e z‖ = ‖B‖ / R2 + ‖e z‖ := by rw [hBz]
        _ ≤ ‖B‖ / R2 + K / R2 ^ 2 := add_le_add_right hez _
        _ ≤ ‖B‖ / R2 + K / R2 := add_le_add_right hKdiv _
        _ = (‖B‖ + K) / R2 := by rw [add_div]
    have hSq : (‖B / z‖ + ‖e z‖) ^ 2 ≤ ((‖B‖ + K) / R2) ^ 2 :=
      pow_le_pow_left₀ (by positivity) hSum 2
    have hPow : ‖(B / z + e z) ^ 2‖ ≤ (‖B‖ + K) ^ 2 / R2 ^ 2 := by
      calc ‖(B / z + e z) ^ 2‖ = ‖B / z + e z‖ ^ 2 := norm_pow _ _
        _ ≤ (‖B / z‖ + ‖e z‖) ^ 2 :=
            pow_le_pow_left₀ (norm_nonneg _) (norm_add_le _ _) 2
        _ ≤ ((‖B‖ + K) / R2) ^ 2 := hSq
        _ = (‖B‖ + K) ^ 2 / R2 ^ 2 := div_pow _ _ _
    have h2A : ‖2 * A * e z‖ ≤ 2 * ‖A‖ * K / R2 ^ 2 := by
      calc ‖2 * A * e z‖ = 2 * ‖A‖ * ‖e z‖ := by simp
        _ ≤ 2 * ‖A‖ * (K / R2 ^ 2) := mul_le_mul_of_nonneg_left hez (by positivity)
        _ = 2 * ‖A‖ * K / R2 ^ 2 := by ring
    calc ‖(B / z + e z) ^ 2 + 2 * A * e z‖
        ≤ ‖(B / z + e z) ^ 2‖ + ‖2 * A * e z‖ := norm_add_le _ _
      _ ≤ (‖B‖ + K) ^ 2 / R2 ^ 2 + 2 * ‖A‖ * K / R2 ^ 2 := add_le_add hPow h2A
      _ = C0 / R2 ^ 2 := by rw [hC0, add_div]
  have hRemLim : Filter.Tendsto
      (fun R2 : ℝ => ∮ z in C((0 : ℂ), R2), (B / z + e z) ^ 2 + 2 * A * e z)
      Filter.atTop (nhds 0) := by
    refine squeeze_zero_norm' (a := fun R2 : ℝ => (2 * Real.pi * C0) / R2) ?_ ?_
    · filter_upwards [Filter.eventually_ge_atTop (max R1 1)] with R2 hge
      have hR1le : R1 ≤ R2 := le_trans le_sup_left hge
      have h1le : 1 ≤ R2 := le_trans le_sup_right hge
      have hR2pos : 0 < R2 := lt_of_lt_of_le hR1pos hR1le
      have hR2le : 0 ≤ R2 := le_of_lt hR2pos
      have hBound := hRemBound R2 hR1le h1le
      have hInt := circleIntegral.norm_integral_le_of_norm_le_const (c := (0 : ℂ))
        (C := C0 / R2 ^ 2) hR2le hBound
      have hSimp : 2 * Real.pi * R2 * (C0 / R2 ^ 2) = (2 * Real.pi * C0) / R2 := by
        have hR2ne : R2 ≠ 0 := ne_of_gt hR2pos
        field_simp
      calc ‖∮ z in C((0 : ℂ), R2), (B / z + e z) ^ 2 + 2 * A * e z‖
          ≤ 2 * Real.pi * R2 * (C0 / R2 ^ 2) := hInt
        _ = (2 * Real.pi * C0) / R2 := hSimp
    · have hInv : Filter.Tendsto (fun R2 : ℝ => R2⁻¹) Filter.atTop (nhds 0) :=
        tendsto_inv_atTop_zero
      have hMul := Filter.Tendsto.const_mul (2 * Real.pi * C0) hInv
      simpa [div_eq_mul_inv] using hMul
  have hLimL : Filter.Tendsto (fun R2 : ℝ => ∮ z in C((0 : ℂ), R2), (W z) ^ 2)
      Filter.atTop (nhds L) := by
    have hAdd : Filter.Tendsto
        (fun R2 : ℝ => L + (∮ z in C((0 : ℂ), R2), (B / z + e z) ^ 2 + 2 * A * e z))
        Filter.atTop (nhds (L + 0)) :=
      tendsto_const_nhds.add hRemLim
    rw [add_zero] at hAdd
    apply Filter.Tendsto.congr' _ hAdd
    filter_upwards [Filter.eventually_ge_atTop (max R R1)] with R2 hge
    have hRle : R ≤ R2 := le_trans le_sup_left hge
    have hR1le : R1 ≤ R2 := le_trans le_sup_right hge
    change L + (∮ z in C((0 : ℂ), R2), (B / z + e z) ^ 2 + 2 * A * e z)
      = (∮ z in C((0 : ℂ), R2), (W z) ^ 2)
    exact (hDecompInt R2 hR1le).symm
  have hConst : Filter.Tendsto (fun R2 : ℝ => ∮ z in C((0 : ℂ), R2), (W z) ^ 2)
      Filter.atTop (nhds (∮ z in C((0 : ℂ), R), (W z) ^ 2)) := by
    refine Filter.Tendsto.congr'
      (f₁ := fun _ : ℝ => ∮ z in C((0 : ℂ), R), (W z) ^ 2) ?_ tendsto_const_nhds
    filter_upwards [Filter.eventually_ge_atTop R] with R2 hge
    show (∮ z in C((0 : ℂ), R), (W z) ^ 2) = (∮ z in C((0 : ℂ), R2), (W z) ^ 2)
    exact (hEq R2 hge).symm
  have hIntVal : (∮ z in C((0 : ℂ), R), (W z) ^ 2) = L :=
    tendsto_nhds_unique hConst hLimL
  have hNe : (2 : ℂ) * Real.pi * Complex.I ≠ 0 := Complex.two_pi_I_ne_zero
  simp only [blasiusForce]
  rw [hIntVal, hL, hA, hB]
  field_simp

end BlasiusForce

end FluidDynamics.IdealAirfoilModels
