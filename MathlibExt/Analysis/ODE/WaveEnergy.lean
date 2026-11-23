/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import Mathlib.Analysis.Calculus.Deriv.Add
public import Mathlib.Analysis.Calculus.Deriv.Basic
public import Mathlib.Analysis.Calculus.Deriv.Mul
public import Mathlib.Analysis.Calculus.IteratedDeriv.Defs
public import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic

/-!
# A smooth wave mode and its conserved energy

The selected smooth mode `u(t, x) = cos (c * t) * cos x` on `[0, π]`
satisfies the homogeneous wave equation `u_tt = c² * u_xx`, has zero
boundary flux (`u_x = 0` at both ends), and its energy
`E(t) = (1 / 2) ∫₀^π (u_t² + c² u_x²) dx` equals the stated constant
`c² * π / 4`, so the energy is conserved in time. The flux term
`c² * u_t * u_x` that would change the energy vanishes at both ends
because `u_x` does; the selected mode makes that boundary contribution
visible as exactly zero, while the energy computation itself uses only
the two scalar integrals `∫₀^π cos² = π / 2` and `∫₀^π sin² = π / 2`.

## i. Overview

The first and second slice derivatives are computed once, as `HasDerivAt`
statements and as `deriv` function equalities, and reused by all four
public theorems. The energy integral is evaluated by rewriting the
integrand pointwise, splitting the interval integral, and applying
`intervalIntegral.integral_cos_sq` / `integral_sin_sq` on `[0, π]`.
This is one exact mode, not a general well-posedness or energy-identity
claim for arbitrary data: no existence, uniqueness, or decay is proved.

## ii. Key results

- `EarthScience.wave_mode_satisfies_wave_eq`: the mode solves the wave
  equation.
- `EarthScience.wave_mode_neumann_boundary`: zero boundary flux.
- `EarthScience.wave_mode_energy`: the energy is `c² * π / 4`.
- `EarthScience.wave_mode_energy_conserved`: the energy is conserved.

## iii. Table of contents

- A. Slice derivatives
- B. Wave equation and boundary flux
- C. Energy and conservation

## iv. References

- `HasDerivAt.cos`, `HasDerivAt.sin`, `intervalIntegral.integral_cos_sq`,
  `intervalIntegral.integral_sin_sq` (Mathlib).
-/

@[expose] public section

open MeasureTheory intervalIntegral

namespace EarthScience

/-! ## A. Slice derivatives -/

private theorem wave_ut_has (c t x : ℝ) :
    HasDerivAt (fun t : ℝ => Real.cos (c * t) * Real.cos x)
      (-c * Real.sin (c * t) * Real.cos x) t := by
  have hct : HasDerivAt (fun t : ℝ => c * t) c t := by
    simpa using (hasDerivAt_id t).const_mul c
  have hcos : HasDerivAt (fun t : ℝ => Real.cos (c * t)) (-Real.sin (c * t) * c) t :=
    hct.cos
  have hmul : HasDerivAt (fun t : ℝ => Real.cos (c * t) * Real.cos x)
      ((-Real.sin (c * t) * c) * Real.cos x) t :=
    hcos.mul_const _
  rw [show ((-Real.sin (c * t) * c) * Real.cos x)
      = -c * Real.sin (c * t) * Real.cos x from by ring] at hmul
  exact hmul

private theorem wave_utt_has (c t x : ℝ) :
    HasDerivAt (fun t : ℝ => -c * Real.sin (c * t) * Real.cos x)
      (-(c ^ 2) * Real.cos (c * t) * Real.cos x) t := by
  have hct : HasDerivAt (fun t : ℝ => c * t) c t := by
    simpa using (hasDerivAt_id t).const_mul c
  have hsin : HasDerivAt (fun t : ℝ => Real.sin (c * t)) (Real.cos (c * t) * c) t :=
    hct.sin
  have hcm : HasDerivAt (fun t : ℝ => -c * Real.sin (c * t))
      ((-c) * (Real.cos (c * t) * c)) t :=
    hsin.const_mul _
  have hmul : HasDerivAt (fun t : ℝ => -c * Real.sin (c * t) * Real.cos x)
      (((-c) * (Real.cos (c * t) * c)) * Real.cos x) t :=
    hcm.mul_const _
  rw [show (((-c) * (Real.cos (c * t) * c)) * Real.cos x)
      = -(c ^ 2) * Real.cos (c * t) * Real.cos x from by ring] at hmul
  exact hmul

private theorem wave_ux_has (c t x : ℝ) :
    HasDerivAt (fun x : ℝ => Real.cos (c * t) * Real.cos x)
      (-Real.cos (c * t) * Real.sin x) x := by
  have hcos : HasDerivAt Real.cos (-Real.sin x) x := Real.hasDerivAt_cos x
  have hcm : HasDerivAt (fun x : ℝ => Real.cos (c * t) * Real.cos x)
      (Real.cos (c * t) * (-Real.sin x)) x :=
    hcos.const_mul _
  rw [show (Real.cos (c * t) * (-Real.sin x))
      = -Real.cos (c * t) * Real.sin x from by ring] at hcm
  exact hcm

private theorem wave_uxx_has (c t x : ℝ) :
    HasDerivAt (fun x : ℝ => -Real.cos (c * t) * Real.sin x)
      (-Real.cos (c * t) * Real.cos x) x :=
  (Real.hasDerivAt_sin x).const_mul _

private theorem wave_deriv_t_fun (c x : ℝ) :
    deriv (fun t : ℝ => Real.cos (c * t) * Real.cos x)
      = fun t => -c * Real.sin (c * t) * Real.cos x :=
  funext fun t => (wave_ut_has c t x).deriv

private theorem wave_deriv2_t_fun (c x : ℝ) :
    deriv (fun t : ℝ => -c * Real.sin (c * t) * Real.cos x)
      = fun t => -(c ^ 2) * Real.cos (c * t) * Real.cos x :=
  funext fun t => (wave_utt_has c t x).deriv

private theorem wave_deriv_x_fun (c t : ℝ) :
    deriv (fun x : ℝ => Real.cos (c * t) * Real.cos x)
      = fun x => -Real.cos (c * t) * Real.sin x :=
  funext fun x => (wave_ux_has c t x).deriv

private theorem wave_deriv2_x_fun (c t : ℝ) :
    deriv (fun x : ℝ => -Real.cos (c * t) * Real.sin x)
      = fun x => -Real.cos (c * t) * Real.cos x :=
  funext fun x => (wave_uxx_has c t x).deriv

private theorem wave_deriv_t (c t x : ℝ) :
    deriv (fun t : ℝ => Real.cos (c * t) * Real.cos x) t
      = -c * Real.sin (c * t) * Real.cos x :=
  (wave_ut_has c t x).deriv

private theorem wave_deriv_x (c t x : ℝ) :
    deriv (fun x : ℝ => Real.cos (c * t) * Real.cos x) x
      = -Real.cos (c * t) * Real.sin x :=
  (wave_ux_has c t x).deriv

private theorem integral_cos_sq_zero_pi :
    ∫ x in (0 : ℝ)..Real.pi, Real.cos x ^ 2 = Real.pi / 2 := by
  rw [integral_cos_sq, Real.cos_pi, Real.sin_pi, Real.cos_zero, Real.sin_zero]
  ring

private theorem integral_sin_sq_zero_pi :
    ∫ x in (0 : ℝ)..Real.pi, Real.sin x ^ 2 = Real.pi / 2 := by
  rw [integral_sin_sq, Real.sin_zero, Real.cos_zero, Real.sin_pi, Real.cos_pi]
  ring

private theorem integrable_wave_cos (c t : ℝ) :
    IntervalIntegrable (fun x : ℝ => (c ^ 2 * Real.sin (c * t) ^ 2) * Real.cos x ^ 2)
      volume 0 Real.pi :=
  ((Real.continuous_cos.pow 2).intervalIntegrable 0 Real.pi).const_mul _

private theorem integrable_wave_sin (c t : ℝ) :
    IntervalIntegrable (fun x : ℝ => (c ^ 2 * Real.cos (c * t) ^ 2) * Real.sin x ^ 2)
      volume 0 Real.pi :=
  ((Real.continuous_sin.pow 2).intervalIntegrable 0 Real.pi).const_mul _

/-! ## B. Wave equation and boundary flux -/

/-- The selected smooth mode `u(t, x) = cos (c * t) * cos x` on `[0, π]`
satisfies the homogeneous wave equation `u_tt = c² * u_xx`, with
derivatives as `deriv`/`iteratedDeriv` of the slices. -/
theorem wave_mode_satisfies_wave_eq (c t x : ℝ) :
    iteratedDeriv 2 (fun t => Real.cos (c * t) * Real.cos x) t
      = c ^ 2 * iteratedDeriv 2 (fun x => Real.cos (c * t) * Real.cos x) x := by
  have hL : iteratedDeriv 2 (fun t : ℝ => Real.cos (c * t) * Real.cos x) t
      = -(c ^ 2) * Real.cos (c * t) * Real.cos x := by
    have e1 : iteratedDeriv 2 (fun t : ℝ => Real.cos (c * t) * Real.cos x)
        = deriv (deriv (fun t : ℝ => Real.cos (c * t) * Real.cos x)) := by
      rw [show (2 : ℕ) = 1 + 1 from rfl, iteratedDeriv_succ, iteratedDeriv_one]
    rw [e1, wave_deriv_t_fun c x, wave_deriv2_t_fun c x]
  have hR : iteratedDeriv 2 (fun x : ℝ => Real.cos (c * t) * Real.cos x) x
      = -Real.cos (c * t) * Real.cos x := by
    have e1 : iteratedDeriv 2 (fun x : ℝ => Real.cos (c * t) * Real.cos x)
        = deriv (deriv (fun x : ℝ => Real.cos (c * t) * Real.cos x)) := by
      rw [show (2 : ℕ) = 1 + 1 from rfl, iteratedDeriv_succ, iteratedDeriv_one]
    rw [e1, wave_deriv_x_fun c t, wave_deriv2_x_fun c t]
  rw [hL, hR]
  ring

/-- Zero boundary flux: the `x`-derivative of the wave mode vanishes at
both ends `x = 0` and `x = π`. -/
theorem wave_mode_neumann_boundary (c t : ℝ) :
    deriv (fun x => Real.cos (c * t) * Real.cos x) 0 = 0 ∧
    deriv (fun x => Real.cos (c * t) * Real.cos x) Real.pi = 0 := by
  constructor
  · rw [wave_deriv_x c t 0, Real.sin_zero, mul_zero]
  · rw [wave_deriv_x c t Real.pi, Real.sin_pi, mul_zero]

/-! ## C. Energy and conservation -/

/-- The energy of the wave mode is the stated constant: with
`E(t) = (1/2) ∫₀^π (u_t² + c² u_x²) dx`, `E(t) = c² * π / 4`. -/
theorem wave_mode_energy (c t : ℝ) :
    (1 / 2 : ℝ) * ∫ x in (0 : ℝ)..Real.pi,
        (deriv (fun t => Real.cos (c * t) * Real.cos x) t) ^ 2
          + c ^ 2 * (deriv (fun x => Real.cos (c * t) * Real.cos x) x) ^ 2
      = c ^ 2 * Real.pi / 4 := by
  have hpoint : ∀ x : ℝ,
      (deriv (fun t : ℝ => Real.cos (c * t) * Real.cos x) t) ^ 2
          + c ^ 2 * (deriv (fun x : ℝ => Real.cos (c * t) * Real.cos x) x) ^ 2
        = (c ^ 2 * Real.sin (c * t) ^ 2) * Real.cos x ^ 2
          + (c ^ 2 * Real.cos (c * t) ^ 2) * Real.sin x ^ 2 := by
    intro x
    rw [wave_deriv_t c t x, wave_deriv_x c t x]
    ring
  have hfun : (fun x : ℝ => (deriv (fun t : ℝ => Real.cos (c * t) * Real.cos x) t) ^ 2
          + c ^ 2 * (deriv (fun x : ℝ => Real.cos (c * t) * Real.cos x) x) ^ 2)
      = (fun x : ℝ => (c ^ 2 * Real.sin (c * t) ^ 2) * Real.cos x ^ 2
          + (c ^ 2 * Real.cos (c * t) ^ 2) * Real.sin x ^ 2) :=
    funext hpoint
  rw [hfun,
    intervalIntegral.integral_add (integrable_wave_cos c t) (integrable_wave_sin c t),
    intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul,
    integral_cos_sq_zero_pi, integral_sin_sq_zero_pi]
  have hsc : Real.sin (c * t) ^ 2 + Real.cos (c * t) ^ 2 = 1 :=
    Real.sin_sq_add_cos_sq _
  calc (1 / 2 : ℝ) * ((c ^ 2 * Real.sin (c * t) ^ 2) * (Real.pi / 2)
          + (c ^ 2 * Real.cos (c * t) ^ 2) * (Real.pi / 2))
      = (c ^ 2 * Real.pi / 4) * (Real.sin (c * t) ^ 2 + Real.cos (c * t) ^ 2) := by ring
    _ = c ^ 2 * Real.pi / 4 := by rw [hsc, mul_one]

/-- The wave-mode energy is conserved: `E(t₁) = E(t₂)` for all times. -/
theorem wave_mode_energy_conserved (c t₁ t₂ : ℝ) :
    (1 / 2 : ℝ) * ∫ x in (0 : ℝ)..Real.pi,
        (deriv (fun t => Real.cos (c * t) * Real.cos x) t₁) ^ 2
          + c ^ 2 * (deriv (fun x => Real.cos (c * t₁) * Real.cos x) x) ^ 2
      = (1 / 2 : ℝ) * ∫ x in (0 : ℝ)..Real.pi,
        (deriv (fun t => Real.cos (c * t) * Real.cos x) t₂) ^ 2
          + c ^ 2 * (deriv (fun x => Real.cos (c * t₂) * Real.cos x) x) ^ 2 := by
  exact (wave_mode_energy c t₁).trans (wave_mode_energy c t₂).symm

end EarthScience
