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
